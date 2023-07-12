#ifndef GOLEM_PDKIND_H
#define GOLEM_PDKIND_H

#include "Engine.h"
#include "MainSolver.h"
#include "PTRef.h"
#include "TransitionSystem.h"
#include <memory>
#include <set>
#include <tuple>


struct IFrameElement {
        PTRef lemma;
        PTRef counter_example;

        IFrameElement(PTRef lemma, PTRef counter_example) : lemma(lemma), counter_example(counter_example) {}

        bool operator==(IFrameElement const & other) const {
            return this -> lemma == other.lemma && this -> counter_example == other.counter_example;
        }

        bool operator<(IFrameElement const & other) const {
            if (this -> lemma == other.lemma) {
                return this -> counter_example < other.counter_example;
            } else {
                return this -> lemma < other.lemma;
            }
        }
};

struct IFrameElementCompare {
        bool operator()(const IFrameElement &a, const IFrameElement &b) const {
            if (a.lemma == b.lemma) {
                return a.counter_example < b.counter_example;
            } else {
                return a.lemma < b.lemma;
            }
        }
};

struct PushResult {
    std::set<IFrameElement, IFrameElementCompare> i_frame;
    std::set<IFrameElement, IFrameElementCompare> new_i_frame;
    int n;
    bool is_invalid;
    PushResult(std::set<IFrameElement, IFrameElementCompare> i_frame,
               std::set<IFrameElement, IFrameElementCompare> new_i_frame,
               int n,
               bool is_invalid) : i_frame(std::move(i_frame)), new_i_frame(std::move(new_i_frame)), n(n), is_invalid(is_invalid) {}
};

class RFrame {
    size_t k;
    std::vector<PTRef> r;
    Logic & logic;
public:
    RFrame(Logic & logic, size_t k) : logic(logic) {
        for (size_t i = 0; i <= k; ++i) {
            r.push_back(logic.getTerm_true());
        }
    }
    RFrame(Logic & logic) : logic(logic) {}

    const PTRef & operator[] (size_t i) {
        if (i >= r.size()) {
            while (r.size() <= i) {
                r.push_back(logic.getTerm_true());
            }
        }
        return r[i];
    }

    void insert(PTRef fla, size_t k) {
        if (k >= r.size()) {
            while (r.size() <= k) {
                r.push_back(logic.getTerm_true());
            }
        }
        PTRef new_fla = logic.mkAnd(r[k], fla);
        r[k] = new_fla;
    }
};

class ReachabilityChecker {
private:
    RFrame r_frame;
    Logic & logic;
    TransitionSystem const & system;
    std::tuple<bool, PTRef> reachable (int k, PTRef formula);
public:
    ReachabilityChecker(Logic & logic, TransitionSystem const & system) : logic(logic), system(system), r_frame(logic) {}
    std::tuple<bool, int, PTRef> checkReachability (int from, int to, PTRef formula);
    PTRef generalize(Model & model, PTRef transition, PTRef formula);

};


class PDKind : public Engine {
        Logic & logic;
        bool computeWitness {false};
    public:

        PDKind (Logic & logic, Options const & options) : logic(logic) {
            if (options.hasOption(Options::COMPUTE_WITNESS)) {
                computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
            }
        }

        virtual VerificationResult solve(ChcDirectedHyperGraph const & graph) override;

        VerificationResult solve(ChcDirectedGraph const & system);

    private:
        PushResult push(TransitionSystem const & system, std::set<IFrameElement, IFrameElementCompare> & iframe, PTRef p, int n, int k, ReachabilityChecker & reachability_checker);
        VerificationResult solveTransitionSystem(TransitionSystem const & system);

        std::tuple<bool, PTRef> reachable(TransitionSystem const & system, int k1, PTRef formula, std::shared_ptr<RFrame> r);
        std::tuple<bool, int, PTRef> checkReachability(TransitionSystem const & system, std::shared_ptr<RFrame> r ,int k1, int k2, PTRef formula);

        PTRef generalize(TransitionSystem const & system, Model & model, PTRef transition, PTRef formula);
};

#endif // GOLEM_PDKIND_H