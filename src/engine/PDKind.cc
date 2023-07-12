#include "PDKind.h"

#include "Common.h"
#include "MainSolver.h"
#include "ModelBasedProjection.h"
#include "PTRef.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/BasicTransformationPipelines.h"
#include "transformers/SingleLoopTransformation.h"
#include <memory>
#include <queue>
#include <set>
#include <tuple>

VerificationResult PDKind::solve(ChcDirectedHyperGraph const & graph) {
    auto pipeline = Transformations::towardsTransitionSystems();
    auto transformationResult = pipeline.transform(std::make_unique<ChcDirectedHyperGraph>(graph));
    auto transformedGraph = std::move(transformationResult.first);
    auto translator = std::move(transformationResult.second);
    if (transformedGraph->isNormalGraph()) {
        auto normalGraph = transformedGraph->toNormalGraph();
        auto res = solve(*normalGraph);
        return computeWitness ? translator->translate(std::move(res)) : std::move(res);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

VerificationResult PDKind::solve(ChcDirectedGraph const & system) {
    if (isTrivial(system)) {
        return solveTrivial(system);
    }
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system);
        return solveTransitionSystem(*ts);
    }
    SingleLoopTransformation transformation;
    auto[ts, backtranslator] = transformation.transform(system);
    assert(ts);
    auto res = solveTransitionSystem(*ts);
    return res;
}

/* Create a wrapper structure which will hold the result and also an induction invariant or a number of steps to a counter example */
VerificationResult PDKind::solveTransitionSystem (TransitionSystem const & system) {
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();

    ReachabilityChecker reachability_checker(logic, system);

    SMTConfig config;
    TimeMachine tm{logic};
    MainSolver solver(logic, config, "PDKIND");

    MainSolver init_solver(logic, config, "Empty initial states");
    init_solver.insertFormula(init);
    { // Check for system with empty initial states
        auto res = init_solver.check();
        if (res == s_False) { return VerificationResult{VerificationAnswer::SAFE}; }

        init_solver.insertFormula(query);
        res = init_solver.check();
        if (res == s_True) { return VerificationResult{VerificationAnswer::UNSAFE}; }
    }

    solver.insertFormula(init);

    int n = 0;
    PTRef p = logic.mkNot(query);
    std::set<IFrameElement, IFrameElementCompare> inductionFrame;
    inductionFrame.insert(IFrameElement(p, logic.mkNot(p)));

    while (true) {
        int k = n + 1; /* Pick k such that 1 <= k <= n + 1. (Create better approaches). */
        auto res = push(system, inductionFrame, p, n, k, reachability_checker);

        if (res.is_invalid) {
            return VerificationResult(VerificationAnswer::UNSAFE, InvalidityWitness{});
        }
        if (res.i_frame == res.new_i_frame) {
            // make k-inductive invariant as a conjunction of formulas in iframe and call kinductiontoinduction
            return VerificationResult(VerificationAnswer::SAFE);
        }
        n = res.n;
        inductionFrame = res.new_i_frame;
    }
}

PushResult PDKind::push (TransitionSystem const & system, std::set<IFrameElement, IFrameElementCompare> & iframe, PTRef p, int n, int k, ReachabilityChecker & reachability_checker) {
    std::size_t maxUnrollings = k;
    PTRef init = system.getInit();
    PTRef transition = system.getTransition();

    SMTConfig config;
    TimeMachine tm{logic};

    std::queue<IFrameElement> q;
    for (auto e : iframe) {
        q.push(e);
    }
    std::set<IFrameElement, IFrameElementCompare> newIframe = {};
    int np = n + k;
    bool invalid = false;
    while (!invalid && !q.empty()) {
        IFrameElement lemma = q.front();
        q.pop();
        
        std::vector<PTRef> iframe_abs_vec  = {};
        for (auto e : iframe) {
            iframe_abs_vec.push_back(e.lemma);
        }
        PTRef iframe_abs = logic.mkAnd(iframe_abs_vec);

        PTRef t_k = transition;
        PTRef f_abs_conj = logic.getTerm_true();
        std::size_t currentUnrolling;

        for (currentUnrolling = 1; currentUnrolling < maxUnrollings; ++currentUnrolling) {
            PTRef versionedFla = tm.sendFlaThroughTime(iframe_abs, currentUnrolling);
            PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
            t_k = logic.mkAnd(t_k, versionedTransition);
            f_abs_conj = logic.mkAnd(f_abs_conj, versionedFla);

            }

        PTRef not_fabs = logic.mkNot(lemma.lemma);
        PTRef versioned_not_fabs = tm.sendFlaThroughTime(not_fabs, currentUnrolling);
        PTRef t_k_constr = logic.mkAnd(t_k, f_abs_conj);

        MainSolver solver1(logic, config, "PDKIND");
        solver1.insertFormula(iframe_abs);
        solver1.insertFormula(t_k_constr);
        solver1.insertFormula(versioned_not_fabs);
        auto res1 = solver1.check();


        if (res1 == s_False) {
            newIframe.insert(lemma);
            continue;
        }

        auto model1 = solver1.getModel();

        PTRef fcex = tm.sendFlaThroughTime(lemma.counter_example, currentUnrolling);
        
        MainSolver solver2(logic, config, "PDKKIND");
        solver2.insertFormula(iframe_abs);
        solver2.insertFormula(t_k_constr);
        solver2.insertFormula(fcex);
        auto res2 = solver2.check();
        
        if (res2 == s_True) {
            auto model2 = solver2.getModel();
            PTRef g_cex = reachability_checker.generalize(*model2, t_k, fcex);
            // u kazdeho cex si pamatovat pocet korku
            // g_cex je fcex.pocetkroku + k
            auto reach_res = reachability_checker.checkReachability(n - k + 1, n, g_cex);
            if (std::get<0>(reach_res)) {
                // g_cex pocet kroku + pocet kroku v reachibility checkingu
                invalid = true;
                continue;
            } else {
                PTRef g_abs = std::get<2>(reach_res);
                IFrameElement newLemma = IFrameElement(g_abs, g_cex);
                /*
                 *
                 *
                 * */
                iframe.insert(newLemma);
                q.push(newLemma);
                q.push(lemma);
                continue;
            }
        }

        PTRef g_cti = reachability_checker.generalize(*model1, t_k, versioned_not_fabs);
        auto reach_res = reachability_checker.checkReachability(n - k + 1, n, g_cti);
        if (std::get<0>(reach_res)) {
            reach_res = reachability_checker.checkReachability(n + 1, std::get<1>(reach_res) + k, not_fabs);
            np = std::min(np, std::get<1>(reach_res));
            IFrameElement newLemma = IFrameElement(logic.mkNot(lemma.counter_example), lemma.counter_example);
            iframe.insert(newLemma);
            newIframe.insert(newLemma);
        } else {
            PTRef g_abs = std::get<2>(reach_res);
            g_abs = logic.mkAnd(lemma.lemma, g_abs);
            IFrameElement newLemma = IFrameElement(g_abs, lemma.counter_example);
            iframe.insert(newLemma);
            iframe.extract(lemma);
            q.push(newLemma);
        }
    }
    PushResult res(iframe, newIframe, np, invalid);
    return res;
}

std::tuple<bool, PTRef> ReachabilityChecker::reachable (int k, PTRef formula) {
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    TimeMachine tm{logic};

    if (k == 0) {
        MainSolver init_solver(logic, config, "Init state reachability");
        init_solver.insertFormula(system.getInit());
        init_solver.insertFormula(formula);
        auto res = init_solver.check();
        if (res == s_False) {
            auto itpContext = init_solver.getInterpolationContext();
            vec<PTRef> itps;
            int mask = 1;
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);

            return std::make_tuple(false, itps[0]);
        }
        return std::make_tuple(true, logic.getTerm_false());
    }
    PTRef versioned_formula = tm.sendFlaThroughTime(formula, 1); // Send the formula through time by one so it matches the pattern init_0 transition_0-1 formula_1
    while (true) {
        MainSolver solver(logic, config, "Transitioned states rechability");
        solver.insertFormula(r_frame[k-1]);
        solver.insertFormula(system.getTransition());
        solver.insertFormula(versioned_formula);
        auto res = solver.check();

        if (res == s_True) {
            auto model = solver.getModel();
            PTRef g = generalize(*model,system.getTransition(), versioned_formula);
            auto reach_res = reachable(k-1, g);
            if (std::get<0>(reach_res)) {
                return std::make_tuple(true, logic.getTerm_false());
            } else {
                r_frame.insert(std::get<1>(reach_res), k-1);
            }
        } else {
            /*
             *  Get interpolant
             */
            auto itpContext = solver.getInterpolationContext();
            vec<PTRef> itps;
            int mask = 3; // A ^ B => C
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            PTRef interpolant = tm.sendFlaThroughTime(itps[0], -1);

            /*
             *  Get interpolant for initial states.
             */
            MainSolver init_solver(logic, config, "PDKIND");
            init_solver.insertFormula(system.getInit());
            init_solver.insertFormula(formula);

            auto res = init_solver.check();
            if (res == s_False) {
                auto itpContext = init_solver.getInterpolationContext();
                vec<PTRef> itps;
                int mask = 1;
                itpContext->getSingleInterpolant(itps, mask);
                assert(itps.size() == 1);
                PTRef init_interpolant = itps[0];

                return std::make_tuple(false, logic.mkOr(interpolant, init_interpolant));
            }

            return std::make_tuple(false, interpolant);
        }
    }
}

std::tuple<bool, int, PTRef> ReachabilityChecker::checkReachability (int k_from, int k_to, PTRef formula) {
    for (int i = k_from; i <= k_to; i++) {
        auto reach_res = reachable(i, formula);
        if (std::get<0>(reach_res)) {
            return std::make_tuple(true, i, logic.getTerm_false());
        }
        if (i == k_to) {
            return std::make_tuple(false, i, std::get<1>(reach_res));
        }
    }
    return std::make_tuple(false, 0, logic.getTerm_false());
}

PTRef ReachabilityChecker::generalize(Model & model, PTRef transition, PTRef formula) {
    auto xvars = system.getStateVars();

    PTRef conj = logic.mkAnd(transition, formula);
    ModelBasedProjection mbp(logic);
    PTRef g = mbp.keepOnly(conj, xvars, model);

    return g;
}