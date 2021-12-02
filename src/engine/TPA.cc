//
// Created by Martin Blicha on 01.06.21.
//

#include "TPA.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "graph/GraphTransformations.h"

#define TRACE_LEVEL 0

#define TRACE(l,m) if (TRACE_LEVEL >= l) {std::cout << m << std::endl; }

std::unique_ptr<TPABase> TPAEngine::mkSolver() {
    assert(options.hasOption(Options::ENGINE));
    auto val = options.getOption(Options::ENGINE);
    if (val == "tpa-split") {
        return std::unique_ptr<TPABase>(new TPASplit(logic, options));
    } else if (val == "tpa") {
        return std::unique_ptr<TPABase>(new TPABasic(logic, options));
    } else {
        throw std::logic_error("Unexpected situation");
    }
}

GraphVerificationResult TPAEngine::solve(const ChcDirectedGraph & system) {
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system, logic);
        return mkSolver()->solveTransitionSystem(*ts, system);
    }
    else {
        auto simplifiedGraph = GraphTransformations(logic).eliminateNodes(system);
        if (isTransitionSystem(simplifiedGraph)) {
            auto ts = toTransitionSystem(simplifiedGraph, logic);
            return mkSolver()->solveTransitionSystem(*ts, simplifiedGraph);
        }
        throw std::logic_error("BMC cannot handle general CHC systems yet!");
    }
}

class SolverWrapperSingleUse : public SolverWrapper {
    Logic & logic;
    SMTConfig config;
    sstat lastResult = s_Undef;
    std::unique_ptr<MainSolver> solver;
public:
    SolverWrapperSingleUse(Logic & logic, PTRef transition) : logic(logic) {
        this->transition = transition;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
        solver.reset(new MainSolver(logic, config, "Reachability checker"));
        solver->insertFormula(transition);
        solver->insertFormula(query);
        lastResult = solver->check();
        if (lastResult == s_False) {
            return ReachabilityResult::UNREACHABLE;
        } else if (lastResult == s_True) {
            return ReachabilityResult::REACHABLE;
        } else {
            throw std::logic_error("Unexpected solver result in checking reachability!");
        }
    }

    void strenghtenTransition(PTRef nTransition) override {
        transition = logic.mkAnd(transition, nTransition);
    }

    std::unique_ptr<Model> lastQueryModel() override {
        if (not solver or lastResult != s_True) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        return solver->getModel();
    }

    PTRef lastQueryTransitionInterpolant() override {
        if (not solver or lastResult != s_False) {
            throw std::logic_error("Invalid call for obtaining an interpolant from solver");
        }
        auto itpContext = solver->getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t mask = 1; // The transition was the first formula inserted
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef itp = itps[0];
        return itp;
    }
};

class SolverWrapperIncremental : public SolverWrapper {
protected:
    Logic & logic;
    SMTConfig config;
    sstat lastResult = s_Undef;
    std::unique_ptr<MainSolver> solver;

    unsigned allformulasInserted = 0;
    ipartitions_t mask = 0;
    bool pushed = false;

public:
    SolverWrapperIncremental(Logic & logic, PTRef transition) : logic(logic) {
//        std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
        this->transition = transition;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        solver.reset(new MainSolver(logic, config, "incremental reachability checker"));
        solver->insertFormula(transition);
        opensmt::setbit(mask, allformulasInserted++);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
//        std::cout << "Query: " << logic.printTerm(query) << std::endl;
        assert(not pushed);
        solver->push();
        pushed = true;
        solver->insertFormula(query);
        ++allformulasInserted;
        lastResult = solver->check();
        if (lastResult == s_False) {
            return ReachabilityResult::UNREACHABLE;
        } else if (lastResult == s_True) {
            return ReachabilityResult::REACHABLE;
        } else {
            throw std::logic_error("Unexpected solver result in checking reachability!");
        }
    }

    void strenghtenTransition(PTRef nTransition) override {
        assert(not pushed);
        solver->push();
        solver->insertFormula(nTransition);
        opensmt::setbit(mask, allformulasInserted++);
//        std::cout << "Current number of formulas inserted: " << allformulasInserted << std::endl;
    }

    std::unique_ptr<Model> lastQueryModel() override {
        if (lastResult != s_True or not pushed) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        auto model = solver->getModel();
        solver->pop();
        pushed = false;
        return std::move(model);
    }

    PTRef lastQueryTransitionInterpolant() override {
        if (lastResult != s_False or not pushed) {
            throw std::logic_error("Invalid call for obtaining an interpolant from solver");
        }
        auto itpContext = solver->getInterpolationContext();
        vec<PTRef> itps;
//        std::cout << "Current mask: "  << mask << std::endl;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef itp = itps[0];
        solver->pop();
        pushed = false;
//        std::cout << logic.printTerm(itp) << std::endl;
        return itp;
    }
};

class SolverWrapperIncrementalWithRestarts : public SolverWrapperIncremental {
    vec<PTRef> transitionComponents;
    const unsigned limit = 100;
    unsigned levels = 0;

    void rebuildSolver() {
        solver.reset(new MainSolver(logic, config, "incremental reachability checker"));
        PTRef consolidatedTransition = logic.mkAnd(transitionComponents);
        solver->insertFormula(consolidatedTransition);
        levels = 0;
        allformulasInserted = 0;
        mask = 0;
        opensmt::setbit(mask, allformulasInserted++);
        transitionComponents.clear();
        transitionComponents.push(consolidatedTransition);
    }

public:
    SolverWrapperIncrementalWithRestarts(Logic & logic, PTRef transition) : SolverWrapperIncremental(logic, transition) {
        transitionComponents.push(transition);
    }


    ReachabilityResult checkConsistent(PTRef query) override {
        ++levels;
        if (levels > limit) {
//            std::cout << "Rebuilding solver after " << levels << " pushes" << std::endl;
            rebuildSolver();
        }
        return SolverWrapperIncremental::checkConsistent(query);
    }

    void strenghtenTransition(PTRef nTransition) override {
        SolverWrapperIncremental::strenghtenTransition(nTransition);
        transitionComponents.push(nTransition);
        ++levels;
    }


};


TPASplit::~TPASplit() {
    for (SolverWrapper* solver : reachabilitySolvers) {
        delete solver;
    }
}

PTRef TPABase::getInit() const {
    return init;
}

PTRef TPABase::getTransitionRelation() const {
    return transition;
}

PTRef TPABase::getQuery() const {
    return query;
}

vec<PTRef> TPABase::getStateVars(int version) const {
    vec<PTRef> versioned;
    TimeMachine timeMachine(logic);
    for (PTRef var : stateVariables) {
        versioned.push(timeMachine.sendVarThroughTime(var, version));
    }
    return versioned;
}

PTRef TPABase::getNextVersion(PTRef currentVersion, int shift) const {
    auto it = versioningCache.find({currentVersion, shift});
    if (it != versioningCache.end()) {
        return it->second;
    }
    PTRef res = TimeMachine(logic).sendFlaThroughTime(currentVersion, shift);
    versioningCache.insert({{currentVersion, shift}, res});
    return res;
}

bool TPABase::isPureStateFormula(PTRef fla) const {
    auto vars = TermUtils(logic).getVars(fla);
    auto stateVars = getStateVars(0);
    return std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(stateVars.begin(), stateVars.end(), var) != stateVars.end();
    });
}

bool TPABase::isPureTransitionFormula(PTRef fla) const {
    auto vars = TermUtils(logic).getVars(fla);
    auto stateVars = getStateVars(0);
    auto nextStateVars = getStateVars(1);
    return std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(stateVars.begin(), stateVars.end(), var) != stateVars.end()
               or std::find(nextStateVars.begin(), nextStateVars.end(), var) != nextStateVars.end();
    });
}

PTRef TPABase::eliminateVars(PTRef fla, const vec<PTRef> & vars, Model & model) {
    if (useQE) {
        return QuantifierElimination(logic).eliminate(fla, vars);
    } else {
        return ModelBasedProjection(logic).project(fla, vars, model);
    }
}





PTRef TPASplit::getExactPower(unsigned short power) const {
    assert(power >= 0 and power < exactPowers.size());
    return exactPowers[power];
}

void TPASplit::storeExactPower(unsigned short power, PTRef tr) {
//    std::cout << "Strengthening exact reachability on level " << power << " with " << logic.printTerm(tr) << std::endl;
    if (power >= 2 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    exactPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = exactPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : TermUtils(logic).conjoin(tr, current);
    exactPowers[power] = toStore;

    reachabilitySolvers.growTo(power + 2, nullptr);
    PTRef nextLevelTransitionStrengthening = logic.mkAnd(tr, getNextVersion(tr));
    if (not reachabilitySolvers[power + 1]) {
        reachabilitySolvers[power + 1] = new SolverWrapperIncrementalWithRestarts(logic, nextLevelTransitionStrengthening);
//        reachabilitySolvers[power + 1] = new SolverWrapperIncremental(logic, nextLevelTransitionStrengthening);
//        reachabilitySolvers[power + 1] = new SolverWrapperSingleUse(logic, nextLevelTransitionStrengthening);
    } else {
        reachabilitySolvers[power + 1]->strenghtenTransition(nextLevelTransitionStrengthening);
    }
}

PTRef TPASplit::getLessThanPower(unsigned short power) const {
    assert(power >= 0 and power < lessThanPowers.size());
    return lessThanPowers[power];
}

void TPASplit::storeLessThanPower(unsigned short power, PTRef tr) {
//    std::cout << "Strengthening less-than reachability on level " << power << " with " << logic.printTerm(tr) << std::endl;
    assert(power >= 0);
    if (power >= 2 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    lessThanPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = lessThanPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : TermUtils(logic).conjoin(tr, current);
    lessThanPowers[power] = toStore;
}

SolverWrapper* TPASplit::getExactReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}


GraphVerificationResult TPASplit::solveTransitionSystem(TransitionSystem & system, ChcDirectedGraph const & graph) {
    resetTransitionSystem(system);
    queryCache.emplace_back();
    unsigned short power = 1;
    while (true) {
        auto res = checkPower(power);
        switch (res) {
            case VerificationResult::UNSAFE:
                return GraphVerificationResult(res);
            case VerificationResult::SAFE:
            {
                if (not options.hasOption(Options::COMPUTE_WITNESS) or inductiveInvariant == PTRef_Undef) {
                    return GraphVerificationResult(res);
                }
//                std::cout << "Computed invariant: " << logic.printTerm(stateInvariant) << std::endl;
                auto vertices = graph.getVertices();
                assert(vertices.size() == 3);
                VId vertex = vertices[2];
                assert(vertex != graph.getEntryId() and vertex != graph.getExitId());
                TermUtils utils(logic);
                TermUtils::substitutions_map subs;
                auto graphVars = utils.getVarsFromPredicateInOrder(graph.getStateVersion(vertex));
                auto systemVars = getStateVars(0);
                assert(graphVars.size() == systemVars.size());
                for (int i = 0; i < graphVars.size(); ++i) {
                    subs.insert({systemVars[i], graphVars[i]});
                }
                PTRef graphInvariant = utils.varSubstitute(inductiveInvariant, subs);
//                std::cout << "Graph invariant: " << logic.printTerm(graphInvariant) << std::endl;
                ValidityWitness::definitions_type definitions;
                definitions.insert({graph.getStateVersion(vertex), graphInvariant});
                return GraphVerificationResult(res, ValidityWitness(definitions));
            }
            case VerificationResult::UNKNOWN:
                ++power;
        }
    }
}


VerificationResult TPASplit::checkPower(unsigned short power) {
    assert(power > 0);
    TRACE(1, "Checking power " << power)
    // First compute the <2^n transition relation using information from previous level;
    auto res = reachabilityQueryLessThan(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) {
            std::cout << "; System is safe up to <2^" << power - 1 << " steps" << std::endl;
        }
        // Check if we have not reached fixed point.
        if (power >= 3) {
            auto fixedPointReached = checkLessThanFixedPoint(power);
            if (fixedPointReached) {
                return VerificationResult::SAFE;
            }
            fixedPointReached = checkExactFixedPoint(power - 1);
            if (fixedPointReached) {
                return VerificationResult::SAFE;
            }
        }
    }
    queryCache.emplace_back();
    // Second compute the exact power using the concatenation of previous one
    res = reachabilityQueryExact(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) {
            std::cout << "; System is safe up to 2^" << power - 1 << " steps" << std::endl;
        }
        return VerificationResult::UNKNOWN;
    } else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
}

TPASplit::QueryResult TPASplit::reachabilityExactOneStep(PTRef from, PTRef to) {
    // TODO: this solver can be persistent and used incrementally
    QueryResult result;
    SMTConfig config;
    MainSolver solver(logic, config, "1-step checker");
    solver.insertFormula(getExactPower(1));
    PTRef goal = getNextVersion(to);
    solver.insertFormula(logic.mkAnd(from, goal));
    auto res = solver.check();
    if (res == s_True) {
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
}

TPASplit::QueryResult TPASplit::reachabilityExactZeroStep(PTRef from, PTRef to) {
    QueryResult result;
    SMTConfig config;
    MainSolver solver(logic, config, "0-step checker");
    solver.insertFormula(logic.mkAnd(from, to));
    auto res = solver.check();
    if (res == s_True) {
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in exactly 2^n steps (n is 'power').
 * We do this using the (n-1)th abstraction of the transition relation and check 2-step reachability in this abstraction.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n.
 */
TPASplit::QueryResult TPASplit::reachabilityQueryExact(PTRef from, PTRef to, unsigned short power) {
//        std::cout << "Checking exact reachability on level " << power << " from " << logic.printTerm(from) << " to " << logic.printTerm(to) << std::endl;
    TRACE(2,"Checking exact reachability on level " << power << " from " << from.x << " to " << to.x)
    assert(power >= 1);
    if (power == 1) { // Basic check with real transition relation
        return reachabilityExactOneStep(from, to);
    }
    assert(queryCache.size() > power);
    auto it = queryCache[power].find({from, to});
    if (it != queryCache[power].end()) {
        TRACE(1, "Query found in cache on level " << power)
        return it->second;
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
    unsigned counter = 0;
    while(true) {
        TRACE(3, "Exact: Iteration " << ++counter << " on level " << power)
        auto solver = getExactReachabilitySolver(power);
        assert(solver);
        auto res = solver->checkConsistent(logic.mkAnd(from, goal));
        switch (res) {
            case ReachabilityResult::REACHABLE:
            {
                TRACE(3, "Top level query was reachable")
                PTRef previousTransition = getExactPower(power - 1);
                PTRef translatedPreviousTransition = getNextVersion(previousTransition);
                auto model = solver->lastQueryModel();
                if (power == 2) { // Base case, the 2 steps of the exact transition relation have been used
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = refineTwoStepTarget(from, logic.mkAnd(previousTransition, translatedPreviousTransition), goal, *model);
                    TRACE(3, "Exact: Truly reachable states are " << result.refinedTarget.x)
                    assert(result.refinedTarget != logic.getTerm_false());
                    queryCache[power].insert({{from, to}, result});
                    return result;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
//              PTRef modelMidpoint = getNextVersion(extractStateFromModel(getStateVars(1), *model), -1);
                PTRef nextState = extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model);
//              std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
                TRACE(3,"Midpoint from MBP: " << nextState.x)
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQueryExact(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: First half was unreachable, repeating...")
                    assert(getExactPower(power - 1) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    // TODO: check that this is really a subset of the original midpoint
                    TRACE(3, "Exact: First half was reachable")
                    nextState = extractReachableTarget(subQueryRes);
                    TRACE(3, "Midpoint from MBP - part 2: " << nextState.x)
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                }
                // here the first half of the found path is feasible, check the second half
                subQueryRes = reachabilityQueryExact(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: Second half was unreachable, repeating...")
                    assert(getExactPower(power - 1) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                TRACE(3, "Exact: Second half was reachable, reachable states are " << extractReachableTarget(subQueryRes).x)
                // both halves of the found path are feasible => this path is feasible!
                queryCache[power].insert({{from, to}, subQueryRes});
                return subQueryRes;
            }
            case ReachabilityResult::UNREACHABLE:
            {
                TRACE(3, "Top level query was unreachable")
                PTRef itp = solver->lastQueryTransitionInterpolant();
                itp = simplifyInterpolant(itp);
                itp = cleanInterpolant(itp);
//                std::cout << "Strenghtening representation of exact reachability on level " << power << " :";
//                TermUtils(logic).printTermWithLets(std::cout, itp);
//                std::cout << std::endl;
                TRACE(3, "Learning " << itp.x)
                TRACE(4, "Learning " << logic.pp(itp))
                assert(itp != logic.getTerm_true());
                storeExactPower(power, itp);
                result.result = ReachabilityResult::UNREACHABLE;
                return result;
            }
        }
    }
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in less than 2^n steps (n is 'power').
 * We do this using the (n-1)th abstractions of the transition relation (both exact and less-than).
 * Reachability in <2^n steps can happen if it is reachable in <2^(n-1) steps or if it is reachable in 2^(n-1) + <2^(n-1) steps.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n.
 */
TPASplit::QueryResult TPASplit::reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power) {
//        std::cout << "Checking less-than reachability on level " << power << " from " << logic.printTerm(from) << " to " << logic.printTerm(to) << std::endl;
    TRACE(2,"Checking less-than reachability on level " << power << " from " << from.x << " to " << to.x)
    assert(power >= 1);
    if (from == to) {
        QueryResult result;
        result.result = ReachabilityResult::REACHABLE;
        result.refinedTarget = to;
        return result;
    }
    if (power == 1) {
        return reachabilityExactZeroStep(from, to);
    }
    QueryResult result;
    assert(power >= 2);
    PTRef goal = getNextVersion(to, 2);
    unsigned counter = 0;
    while(true) {
        TRACE(3, "Less-than: Iteration " << ++counter << " on level " << power)
        SMTConfig config;
        const char * msg = "ok";
//        config.setOption(SMTConfig::o_verbosity, SMTOption(1), msg);
        config.setReduction(1);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        MainSolver solver(logic, config, "Less-than reachability checker");
        // Tr^{<n-1} or (Tr^{<n-1} concat Tr^{n-1})
        PTRef previousLessThanTransition = getLessThanPower(power - 1);
        PTRef translatedExactTransition = getNextVersion(getExactPower(power - 1));
        PTRef currentToNextNextPreviousLessThanTransition = shiftOnlyNextVars(previousLessThanTransition);
        PTRef twoStepTransition = logic.mkOr(
            currentToNextNextPreviousLessThanTransition,
            logic.mkAnd(previousLessThanTransition, translatedExactTransition)
        );
        // TODO: assert from and to are current-state formulas
        solver.insertFormula(twoStepTransition);
        solver.insertFormula(logic.mkAnd(from, goal));
        auto res = solver.check();
        if (res == s_False) {
            TRACE(3, "Top level query was unreachable")
            auto itpContext = solver.getInterpolationContext();
            vec<PTRef> itps;
            ipartitions_t mask = 1;
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            config.setLRAInterpolationAlgorithm(itp_lra_alg_strong); // compute also McMillan's interpolant
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 2);
            PTRef itp = logic.mkAnd(itps);
            // replace next-next variables with next-variables
            itp = simplifyInterpolant(itp);
            itp = cleanInterpolant(itp);
            TRACE(3, "Learning " << itp.x)
            TRACE(4, "Learning " << logic.pp(itp))
            assert(itp != logic.getTerm_true());
            storeLessThanPower(power, itp);
            result.result = ReachabilityResult::UNREACHABLE;
            return result;
        } else if (res == s_True) {
            TRACE(3, "Top level query was reachable")
            auto model = solver.getModel();
            if (model->evaluate(currentToNextNextPreviousLessThanTransition) == logic.getTerm_true()) {
                // First disjunct was responsible for the positive answer, check it
                TRACE(3, "First disjunct was satisfiable")
                if (power == 2) { // This means the goal is reachable in 0 steps, no need to re-check anythin
                    // TODO: double-check this
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = logic.mkAnd(from, to); // TODO: check if this is needed
                    TRACE(3, "Less-than: Truly reachable states are " << result.refinedTarget.x)
                    TRACE(4, "Less-than: Truly reachable states are " << logic.pp(result.refinedTarget))
                    return result;
                }
                auto subQueryRes = reachabilityQueryLessThan(from, to, power - 1);
                if (isReachable(subQueryRes)) {
                    TRACE(3, "Less-than: First half was reachable!")
                    return subQueryRes;
                } else {
                    TRACE(3, "Less-than: First half was unreachable, repeating...")
                    assert(isUnreachable(subQueryRes));
                    assert(getLessThanPower(power - 1) != previousLessThanTransition);
                    continue;
                }
            } else {
                // Second disjunct was responsible for the positive answer
                assert(model->evaluate(logic.mkAnd(previousLessThanTransition, translatedExactTransition)) == logic.getTerm_true());
                TRACE(3, "Second disjunct was satisfiable")
                if (power == 2) { // Since it was not reachable in 0 steps (checked above), here it means it was reachable in exactly 1 step
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = refineTwoStepTarget(from, logic.mkAnd(previousLessThanTransition, translatedExactTransition), goal, *model);
                    TRACE(3, "Less-than: Truly reachable states are " << result.refinedTarget.x)
                    return result;
                }
                PTRef nextState = extractMidPoint(from, previousLessThanTransition, translatedExactTransition, goal, *model);
                TRACE(3, "Midpoint is " << nextState.x)
                TRACE(4, "Midpoint is " << logic.pp(nextState));
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQueryLessThan(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Less-than: First half was unreachable, repeating...")
                    assert(getLessThanPower(power - 1) != previousLessThanTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    TRACE(3, "Less-than: First half was reachable!")
                    nextState = extractReachableTarget(subQueryRes);
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                    TRACE(3, "Modified midpoint : " << nextState.x)
                    TRACE(4, "Modified midpoint : " << logic.pp(nextState))
                }
                // here the first half of the found path is feasible, check the second half
                PTRef previousExactTransition = getExactPower(power - 1);
                subQueryRes = reachabilityQueryExact(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getExactPower(power - 1) != previousExactTransition);
                    TRACE(3, "Less-than: Second half was unreachable, repeating...")
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                TRACE(3, "Less-than: Second half was reachable, reachable states are " << extractReachableTarget(subQueryRes).x)
                // both halves of the found path are feasible => this path is feasible!
                return subQueryRes;
            }
        } else {
            throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
        }
    }
}


PTRef TPABase::simplifyInterpolant(PTRef itp) {
    auto & laLogic = dynamic_cast<LALogic&>(logic);
    LATermUtils utils(laLogic);
    if (logic.isOr(itp)) {
        PTRef simplified = utils.simplifyDisjunction(itp);
//        if (simplified != itp) {
//            std::cout << "SImplified " << logic.pp(itp) << " to " << logic.pp(simplified) << std::endl;
//        }
        return simplified;
    }
    return itp;
}

// TODO: unify cleanInterpolant and shiftOnlyNextVars. They are dual to each other and very similar
PTRef TPABase::cleanInterpolant(PTRef itp) {
    TermUtils utils(logic);
    auto itpVars = utils.getVars(itp);
    auto currentVars = getStateVars(0);
    auto nextnextVars = getStateVars(2);
    assert(std::all_of(itpVars.begin(), itpVars.end(), [&](PTRef var) {
        return std::find(currentVars.begin(), currentVars.end(), var) != currentVars.end() or
            std::find(nextnextVars.begin(), nextnextVars.end(), var) != nextnextVars.end();
    }));
    auto nextVars = getStateVars(1);
    TermUtils::substitutions_map subst;
    assert(nextVars.size() == nextnextVars.size());
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextnextVars[i], nextVars[i]});
    }
    return utils.varSubstitute(itp, subst);
}

PTRef TPABase::shiftOnlyNextVars(PTRef fla) {
    TermUtils utils(logic);
    auto vars = utils.getVars(fla);
    auto currentVars = getStateVars(0);
    auto nextVars = getStateVars(1);
    assert(std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(currentVars.begin(), currentVars.end(), var) != currentVars.end() or
               std::find(nextVars.begin(), nextVars.end(), var) != nextVars.end();
    }));
    auto nextnextVars = getStateVars(2);
    TermUtils::substitutions_map subst;
    assert(nextVars.size() == nextnextVars.size());
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextVars[i], nextnextVars[i]});
    }
    return utils.varSubstitute(fla, subst);
}

void TPABase::resetTransitionSystem(TransitionSystem const & system) {
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    this->stateVariables.clear();
    this->auxiliaryVariables.clear();
    auto stateVars = system.getStateVars();
    auto auxVars = system.getAuxiliaryVars();
    TermUtils::substitutions_map substMap;
    for (PTRef var : stateVars) {
        PTRef versionedVar = timeMachine.getVarVersionZero(var);
        this->stateVariables.push(versionedVar);
        substMap.insert({var, versionedVar});
    }
    for (PTRef var : auxVars) {
        PTRef versionedVar = timeMachine.getVarVersionZero(var);
        this->auxiliaryVariables.push(versionedVar);
        substMap.insert({var, versionedVar});
    }
    this->init = utils.varSubstitute(system.getInit(), substMap);
    this->init = utils.toNNF(this->init);
    if (not isPureStateFormula(init)) {
        throw std::logic_error("Initial states contain some non-state variable");
    }
    this->query = utils.varSubstitute(system.getQuery(), substMap);
    this->query = utils.toNNF(this->query);
    if (not isPureStateFormula(query)) {
        throw std::logic_error("Query states contain some non-state variable");
    }
    auto nextStateVars = system.getNextStateVars();
    assert(nextStateVars.size() == stateVars.size());
    for (int i = 0; i < nextStateVars.size(); ++i) {
            PTRef nextStateVersioned = timeMachine.sendVarThroughTime(substMap[stateVars[i]], 1);
            substMap.insert({nextStateVars[i], nextStateVersioned});
    }
    this->transition = utils.varSubstitute(system.getTransition(), substMap);
    this->transition = utils.toNNF(this->transition);
//    std::cout << "Before simplifications: " << transition.x << std::endl;
    if (not logic.isAtom(this->transition)) {
        this->transition = ::rewriteMaxArityAggresive(logic, this->transition);
//    std::cout << "After simplifications 1: " << transition.x << std::endl;
        this->transition = ::simplifyUnderAssignment_Aggressive(this->transition, logic);
//    std::cout << "After simplifications 2: " << transition.x << std::endl;
    }
    resetPowers();
//    std::cout << "Init: " << logic.printTerm(init) << std::endl;
//    std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
//    std::cout << "Transition: "; TermUtils(logic).printTermWithLets(std::cout, transition); std::cout << std::endl;
//    std::cout << "Query: " << logic.printTerm(query) << std::endl;
}

PTRef TPABase::extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model) {
    assert(isPureStateFormula(start));
    assert(isPureTransitionFormula(firstTransition));
    assert(isPureStateFormula(getNextVersion(goal, -2)));
    assert(isPureTransitionFormula(getNextVersion(secondTransition, -1)));
    PTRef firstStep = logic.mkAnd(start, firstTransition);
    PTRef secondStep = logic.mkAnd(goal, secondTransition);
    assert(model.evaluate(firstStep) == logic.getTerm_true() and model.evaluate(secondStep) == logic.getTerm_true());
    vec<PTRef> toEliminate = getStateVars(0);
    PTRef midPointFromStart = eliminateVars(firstStep, toEliminate, model);
    toEliminate = getStateVars(2);
    PTRef midPointFromGoal = eliminateVars(secondStep, toEliminate, model);
    PTRef midPoint = getNextVersion(logic.mkAnd(midPointFromStart, midPointFromGoal), -1);
    assert(isPureStateFormula(midPoint));
    return midPoint;
}

PTRef TPABase::refineTwoStepTarget(PTRef start, PTRef twoSteptransition, PTRef goal, Model & model) {
    assert(isPureStateFormula(getNextVersion(goal, -2)));
    PTRef transitionQuery = logic.mkAnd({start, twoSteptransition, goal});
    assert(model.evaluate(transitionQuery) == logic.getTerm_true());
    auto nextnextStateVars = getStateVars(2);
    TermUtils utils(logic);
    auto vars = utils.getVars(transitionQuery);
    vec<PTRef> toEliminate;
    for (PTRef var : vars) {
        auto it = std::find(nextnextStateVars.begin(), nextnextStateVars.end(), var);
        if (it == nextnextStateVars.end()) {
            toEliminate.push(var);
        }
    }
    PTRef refinedGoal = eliminateVars(transitionQuery, toEliminate, model);
    assert(refinedGoal != logic.getTerm_false());
    return getNextVersion(refinedGoal, -2);
}

void TPASplit::resetPowers() {
    TimeMachine timeMachine(logic);
    vec<PTRef> currentNextEqs;
    for (PTRef stateVar : stateVariables) {
        PTRef nextStateVar = timeMachine.sendVarThroughTime(stateVar, 1);
        currentNextEqs.push(logic.mkEq(stateVar, nextStateVar));
    }
    PTRef identity = logic.mkAnd(std::move(currentNextEqs));
    this->exactPowers.clear();
    this->lessThanPowers.clear();
    storeExactPower(0, identity);
    storeExactPower(1, transition);
    lessThanPowers.push(PTRef_Undef); // <0 does not make sense
    lessThanPowers.push(exactPowers[0]); // <1 is just exact 0
}

bool TPASplit::verifyLessThanPower(unsigned short power) {
    assert(power >= 2);
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getLessThanPower(power);
    PTRef previous = getLessThanPower(power - 1);
    PTRef previousExact = getExactPower(power - 1);
//    std::cout << "Previous exact: " << logic.printTerm(previousExact) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.insertFormula(logic.mkOr(
        shiftOnlyNextVars(previous),
        logic.mkAnd(previous, getNextVersion(previousExact))
    ));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}

bool TPASplit::verifyExactPower(unsigned short power) {
    assert(power >= 2);
    if (power > 2) {
        bool previousRes = verifyExactPower(power - 1);
        if (not previousRes) {
            return false;
        }
    }
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getExactPower(power);
    PTRef previous = getExactPower(power - 1);
//    std::cout << "Exact on level " << power << " : " << logic.printTerm(current) << std::endl;
//    std::cout << "Exact on level " << power - 1 << " : " << logic.printTerm(previous) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.insertFormula(logic.mkAnd(previous, getNextVersion(previous)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}


bool TPASplit::checkLessThanFixedPoint(unsigned short power) {
    assert(power >= 3);
    assert(verifyLessThanPower(power));
    for (unsigned short i = 3; i <= power; ++i) {
        PTRef currentLevelTransition = getLessThanPower(i);
        // first check if it is fixed point with respect to initial state
        SMTConfig config;
        {
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({currentLevelTransition, getNextVersion(transition), logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != s_False) {
                solver.push();
                solver.insertFormula(init);
                satres = solver.check();
                if (satres == s_False) {
                    restrictedInvariant = true;
                }
            }
            if (satres == s_False) {
                if (verbose() > 0) {
                    std::cout << "; Right fixed point detected in less-than relation on level " << i << " from " << power << std::endl;
                    std::cout << "; Fixed point detected for " << (not restrictedInvariant ? "whole transition relation" : "transition relation restricted to init") << std::endl;
                }
                if (options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true") {
//                     std::cout << "Computing inductive invariant" << std::endl;
                    inductiveInvariant = getNextVersion(QuantifierElimination(logic).keepOnly(logic.mkAnd(init, currentLevelTransition), getStateVars(1)), -1);
                }
                return true;
            }
        }
        // now check if it is fixed point with respect to bad states
        {
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({transition, getNextVersion(currentLevelTransition), logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != s_False) {
                solver.push();
                solver.insertFormula(getNextVersion(query, 2));
                satres = solver.check();
                if (satres == s_False) {
                    restrictedInvariant = true;
                }
            }
            if (satres == s_False) {
                if (verbose() > 0) {
                    std::cout << "; Left fixed point detected in less-than relation on level " << i << " from " << power << std::endl;
                    std::cout << "; Fixed point detected for " << (not restrictedInvariant ? "whole transition relation" : "transition relation restricted to bad") << std::endl;
                }
                if (options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true") {
                    // std::cout << "Computing inductive invariant" << std::endl;
                    inductiveInvariant = logic.mkNot(QuantifierElimination(logic).keepOnly(logic.mkAnd(currentLevelTransition,
                        getNextVersion(query)), getStateVars(0)));
                }
                return true;
            }
        }
    }
    return false;
}

bool TPASplit::checkExactFixedPoint(unsigned short power) {
    assert(power >= 2);
    for (unsigned short i = 2; i <= power; ++i) {
        PTRef currentLevelTransition = getExactPower(i);
        PTRef currentTwoStep = logic.mkAnd(currentLevelTransition, getNextVersion(currentLevelTransition));
        PTRef shifted = shiftOnlyNextVars(currentLevelTransition);
        SMTConfig config;
        MainSolver solver(logic, config, "Fixed-point checker");
        solver.insertFormula(logic.mkAnd({currentTwoStep, logic.mkNot(shifted)}));
        sstat satres = solver.check();
        char restrictedInvariant = 0;
        if (satres != s_False) {
            solver.push();
            solver.insertFormula(getNextVersion(logic.mkAnd(init, getLessThanPower(i)), -1));
            satres = solver.check();
            if (satres == s_False) {
                restrictedInvariant = 1;
            }
        }
        if (satres != s_False) {
            solver.pop();
            solver.push();
            solver.insertFormula(logic.mkAnd(getNextVersion(getLessThanPower(i), 2), getNextVersion(query, 3)));
            satres = solver.check();
            if (satres == s_False) {
                restrictedInvariant = 2;
            }
        }
        if (satres == s_False) {
            if (verbose() > 0) {
                std::cout << "; Fixed point detected in equals relation on level " << i << " from " << power << std::endl;
                std::cout << "; Fixed point detected for ";
                switch (restrictedInvariant) {
                    case 0:
                        std::cout << "whole transition relation";
                        break;
                    case 1:
                        std::cout << "transition relation restricted to init";
                        break;
                    case 2:
                        std::cout << "transition relation restricted to bad";
                        break;
                    default:
                        assert(false);
                }
                std::cout << std::endl;
            }
            if (options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true" and restrictedInvariant != 2) {
                if (i <= 10) {
//                    std::cout << "Computing inductive invariant" << std::endl;
                    assert(verifyLessThanPower(i));
                    assert(verifyExactPower(i));
//                    std::cout << "Less-than transition: " << logic.printTerm(getLessThanPower(i)) << '\n';
//                    std::cout << "Exact transition: " << logic.printTerm(getExactPower(i)) << std::endl;
                    PTRef transitionInvariant = logic.mkOr(
                        shiftOnlyNextVars(getLessThanPower(i)),
                        logic.mkAnd(getLessThanPower(i), getNextVersion(getExactPower(i)))
                    );
//                    std::cout << "Transition invariant: " << logic.printTerm(transitionInvariant) << std::endl;
                    PTRef stateInvariant = QuantifierElimination(logic).eliminate(
                        logic.mkAnd(init, transitionInvariant), getStateVars(0));
//                    std::cout << "After eliminating current state vars: " << logic.printTerm(stateInvariant) << std::endl;
                    stateInvariant = QuantifierElimination(logic).eliminate(stateInvariant, getStateVars(1));
                    stateInvariant = getNextVersion(stateInvariant, -2);
//                    std::cout << "State invariant: " << logic.printTerm(stateInvariant) << std::endl;
                    unsigned long k = 1;
                    k <<= (i - 1);
                    assert(verifyKinductiveInvariant(stateInvariant, k));
//                    std::cout << "K-inductivness of invariant sucessfully checked for k=" << k << std::endl;
                    inductiveInvariant = kinductiveToInductive(stateInvariant, k);
//                    std::cout << "Inductive invariant: " << logic.printTerm(inductiveInvariant) << std::endl;
//                    std::cout << "Inductive invariant computed!" << std::endl;
                    assert(verifyKinductiveInvariant(inductiveInvariant, 1));
                } else {
                    std::cerr << "; k-inductive invariant computed, by k is too large to compute 1-inductive invariant"
                              << std::endl;
                    inductiveInvariant = PTRef_Undef;
                }
            }
            return true;
        }
    }
    return false;
}

PTRef TPABase::kinductiveToInductive(PTRef invariant, unsigned long k) {
    /*
     * If P(x) is k-inductive invariant then the following formula is 1-inductive invariant:
     * P(x_0)
     * \land \forall x_1 (Tr(x_0,x_1) \implies P(x_1)
     * \land \forall x_1,x_2 (Tr(x_0,x_1 \land P(x_1) \land Tr(x_1,x_2) \implies P(x_2))
     * ...
     * \land \forall x_1,x_2,\ldots,x_{k-1}(Tr(x_0,x_1) \land p(x_1) \land \ldots \land P(x_{k-2}) \land Tr(x_{k-2},x_{k-1} \implies P(x_{k_1}))
     *
     * This is equivalent to
     * * P(x_0)
     * \land \neg \exists x_1 (Tr(x_0,x_1) \land \neg P(x_1)
     * \land \neg \exists x_1,x_2 (Tr(x_0,x_1 \land P(x_1) \land Tr(x_1,x_2) \land \neg P(x_2))
     * ...
     * \land \neg \exists x_1,x_2,\ldots,x_{k-1}(Tr(x_0,x_1) \land p(x_1) \land \ldots \land P(x_{k-2}) \land Tr(x_{k-2},x_{k-1} \land \neg P(x_{k_1}))
     *
     * Some computation can be re-used between iteration as going from one iteration to another (ignoring the last negated P(x_i)) we only and
     * next version of P(x_i) and Tr(x_i, x_{i+1})
     */
    // TODO: eliminate auxiliary variables from transition relation beforehand
    vec<PTRef> stateVars = getStateVars(0);
    vec<PTRef> resArgs;
    // step 0
    resArgs.push(invariant);
    vec<PTRef> helpers;
    helpers.push(PTRef_Undef);
    // step 1
//    std::cout << "Step 1 out of " << k << std::endl;
    PTRef afterElimination = QuantifierElimination(logic).keepOnly(logic.mkAnd(transition, logic.mkNot(getNextVersion(invariant))), stateVars);
    resArgs.push(logic.mkNot(afterElimination));
    helpers.push(transition);
    // steps 2 to k-1
    for (unsigned long i = 2; i < k; ++i) {
//        std::cout << "Step " << i << " out of " << k << std::endl;
        PTRef helper = logic.mkAnd({helpers[i-1], getNextVersion(invariant, i-1), getNextVersion(transition, i-1)});
        helper = QuantifierElimination(logic).eliminate(helper, getStateVars(i-1));
        helpers.push(helper);
        afterElimination = QuantifierElimination(logic).keepOnly(logic.mkAnd(helper, logic.mkNot(getNextVersion(invariant, i))), stateVars);
        resArgs.push(logic.mkNot(afterElimination));
    }
    return logic.mkAnd(resArgs);
}

bool TPABase::verifyKinductiveInvariant(PTRef fla, unsigned long k) {
    SMTConfig config;
    // Base cases:
    {
        MainSolver solver(logic, config, "k-induction base checker");
        solver.insertFormula(init);
        for (unsigned long i = 0; i < k; ++i) {
            solver.push();
            solver.insertFormula(logic.mkNot(getNextVersion(fla, i)));
            auto res = solver.check();
            if (res != s_False) {
                std::cerr << "k-induction verification failed; base case " << i << " does not hold!" << std::endl;
                return false;
            }
            solver.pop();
            solver.insertFormula(getNextVersion(transition, i));
        }
    }
    // Inductive case:
    MainSolver solver(logic, config, "k-induction inductive step checker");
    for (unsigned long i = 0; i < k; ++i) {
        solver.insertFormula(getNextVersion(fla, i));
        solver.insertFormula(getNextVersion(transition, i));
    }
    solver.insertFormula(logic.mkNot(getNextVersion(fla, k)));
    auto res = solver.check();
    if (res != s_False) {
        std::cerr << "k-induction verification failed; induction step does not hold!" << std::endl;
        return false;
    }
    return true;
}

// Single hierarchy version:
TPABasic::~TPABasic() {
    for (SolverWrapper* solver : reachabilitySolvers) {
        delete solver;
    }
}


PTRef TPABasic::getLevelTransition(unsigned short power) const {
    assert(power >= 0 and power < transitionHierarchy.size());
    return transitionHierarchy[power];
}

void TPABasic::storeLevelTransition(unsigned short power, PTRef tr) {
    //    std::cout << "Strengthening exact reachability on level " << power << " with " << logic.printTerm(tr) << std::endl;
    if (power >= 2 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    transitionHierarchy.growTo(power + 1, PTRef_Undef);
    PTRef current = transitionHierarchy[power];
    PTRef toStore = current == PTRef_Undef ? tr : TermUtils(logic).conjoin(tr, current);
    transitionHierarchy[power] = toStore;

    reachabilitySolvers.growTo(power + 2, nullptr);
    PTRef nextLevelTransitionStrengthening = logic.mkAnd(tr, getNextVersion(tr));
    if (not reachabilitySolvers[power + 1]) {
        reachabilitySolvers[power + 1] = new SolverWrapperIncrementalWithRestarts(logic, nextLevelTransitionStrengthening);
        //        reachabilitySolvers[power + 1] = new SolverWrapperIncremental(logic, nextLevelTransitionStrengthening);
        //        reachabilitySolvers[power + 1] = new SolverWrapperSingleUse(logic, nextLevelTransitionStrengthening);
    } else {
        reachabilitySolvers[power + 1]->strenghtenTransition(nextLevelTransitionStrengthening);
    }
}

SolverWrapper* TPABasic::getReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}


GraphVerificationResult TPABasic::solveTransitionSystem(TransitionSystem & system, ChcDirectedGraph const & graph) {
    resetTransitionSystem(system);
    queryCache.emplace_back();
    unsigned short power = 1;
    while (true) {
        auto res = checkPower(power);
        switch (res) {
            case VerificationResult::UNSAFE:
                return GraphVerificationResult(res);
                case VerificationResult::SAFE:
                {
                    if (not options.hasOption(Options::COMPUTE_WITNESS) or inductiveInvariant == PTRef_Undef) {
                        return GraphVerificationResult(res);
                    }
                    //                std::cout << "Computed invariant: " << logic.printTerm(stateInvariant) << std::endl;
                    auto vertices = graph.getVertices();
                    assert(vertices.size() == 3);
                    VId vertex = vertices[2];
                    assert(vertex != graph.getEntryId() and vertex != graph.getExitId());
                    TermUtils utils(logic);
                    TermUtils::substitutions_map subs;
                    auto graphVars = utils.getVarsFromPredicateInOrder(graph.getStateVersion(vertex));
                    auto systemVars = getStateVars(0);
                    assert(graphVars.size() == systemVars.size());
                    for (int i = 0; i < graphVars.size(); ++i) {
                        subs.insert({systemVars[i], graphVars[i]});
                    }
                    PTRef graphInvariant = utils.varSubstitute(inductiveInvariant, subs);
                    //                std::cout << "Graph invariant: " << logic.printTerm(graphInvariant) << std::endl;
                    ValidityWitness::definitions_type definitions;
                    definitions.insert({graph.getStateVersion(vertex), graphInvariant});
                    return GraphVerificationResult(res, ValidityWitness(definitions));
                }
                case VerificationResult::UNKNOWN:
                    ++power;
        }
    }
}

VerificationResult TPABasic::checkPower(unsigned short power) {
    assert(power > 0);
    TRACE(1, "Checking power " << power)
    queryCache.emplace_back();
    auto res = reachabilityQuery(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) {
            std::cout << "; System is safe up to <=2^" << power - 1 << " steps" << std::endl;
        }
        // Check if we have not reached fixed point.
        if (power >= 3) {
            bool fixedPointReached = checkFixedPoint(power);
            if (fixedPointReached) {
                return VerificationResult::SAFE;
            }
        }
    }
    return VerificationResult::UNKNOWN;
}

TPABasic::QueryResult TPABasic::reachabilityExactOneStep(PTRef from, PTRef to) {
    // TODO: this solver can be persistent and used incrementally
    QueryResult result;
    SMTConfig config;
    MainSolver solver(logic, config, "1-step checker");
    solver.insertFormula(transition);
    PTRef goal = getNextVersion(to);
    solver.insertFormula(logic.mkAnd(from, goal));
    auto res = solver.check();
    if (res == s_True) {
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
}

TPABasic::QueryResult TPABasic::reachabilityExactZeroStep(PTRef from, PTRef to) {
    QueryResult result;
    SMTConfig config;
    MainSolver solver(logic, config, "0-step checker");
    solver.insertFormula(logic.mkAnd(from, to));
    auto res = solver.check();
    if (res == s_True) {
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in  <=2^n steps (n is 'power').
 * We do this using the (n-1)th abstraction of the transition relation and check 2-step reachability in this abstraction.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n.
 */
TPABasic::QueryResult TPABasic::reachabilityQuery(PTRef from, PTRef to, unsigned short power) {
    //        std::cout << "Checking LEQ reachability on level " << power << " from " << logic.printTerm(from) << " to " << logic.printTerm(to) << std::endl;
    TRACE(2,"Checking LEQ reachability on level " << power << " from " << from.x << " to " << to.x)
    assert(power >= 0);
    if (power == 0) { // Basic check with real transition relation
        auto res = reachabilityExactZeroStep(from, to);
        if (res.result == ReachabilityResult::REACHABLE) { return res; }
        res = reachabilityExactOneStep(from, to);
        return res;
    }
    assert(queryCache.size() > power);
    auto it = queryCache[power].find({from, to});
    if (it != queryCache[power].end()) {
        TRACE(1, "Query found in cache on level " << power)
        return it->second;
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
    unsigned counter = 0;
    while(true) {
        TRACE(3, "Exact: Iteration " << ++counter << " on level " << power)
        auto solver = getReachabilitySolver(power);
        assert(solver);
        auto res = solver->checkConsistent(logic.mkAnd(from, goal));
        switch (res) {
            case ReachabilityResult::REACHABLE:
            {
                TRACE(3, "Top level query was reachable")
                PTRef previousTransition = getLevelTransition(power - 1);
                PTRef translatedPreviousTransition = getNextVersion(previousTransition);
                auto model = solver->lastQueryModel();
                if (power == 1) { // Base case, the 2 steps of the exact transition relation have been used
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = refineTwoStepTarget(from, logic.mkAnd(previousTransition, translatedPreviousTransition), goal, *model);
                    TRACE(3, "Exact: Truly reachable states are " << result.refinedTarget.x)
                    assert(result.refinedTarget != logic.getTerm_false());
                    queryCache[power].insert({{from, to}, result});
                    return result;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
                PTRef nextState = extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model);
                //              std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
                TRACE(3,"Midpoint from MBP: " << nextState.x)
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQuery(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: First half was unreachable, repeating...")
                    assert(getLevelTransition(power - 1) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    TRACE(3, "Exact: First half was reachable")
                    nextState = extractReachableTarget(subQueryRes);
                    TRACE(3, "Midpoint from MBP - part 2: " << nextState.x)
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                }
                // here the first half of the found path is feasible, check the second half
                subQueryRes = reachabilityQuery(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: Second half was unreachable, repeating...")
                    assert(getLevelTransition(power - 1) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                TRACE(3, "Exact: Second half was reachable, reachable states are " << extractReachableTarget(subQueryRes).x)
                // both halves of the found path are feasible => this path is feasible!
                queryCache[power].insert({{from, to}, subQueryRes});
                return subQueryRes;
            }
            case ReachabilityResult::UNREACHABLE:
            {
                TRACE(3, "Top level query was unreachable")
                PTRef itp = solver->lastQueryTransitionInterpolant();
                itp = simplifyInterpolant(itp);
                itp = cleanInterpolant(itp);
                //                std::cout << "Strenghtening representation of exact reachability on level " << power << " :";
                //                TermUtils(logic).printTermWithLets(std::cout, itp);
                //                std::cout << std::endl;
                TRACE(3, "Learning " << itp.x)
                TRACE(4, "Learning " << logic.pp(itp))
                assert(itp != logic.getTerm_true());
                storeLevelTransition(power, itp);
                result.result = ReachabilityResult::UNREACHABLE;
                return result;
            }
        }
    }
}

void TPABasic::resetPowers() {
    TimeMachine timeMachine(logic);
    vec<PTRef> currentNextEqs;
    for (PTRef stateVar : stateVariables) {
        PTRef nextStateVar = timeMachine.sendVarThroughTime(stateVar, 1);
        currentNextEqs.push(logic.mkEq(stateVar, nextStateVar));
    }
    PTRef identity = logic.mkAnd(std::move(currentNextEqs));
    this->transitionHierarchy.clear();
    storeLevelTransition(0, logic.mkOr(identity, transition));
}

bool TPABasic::verifyLevel(unsigned short power) {
    assert(power >= 2);
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getLevelTransition(power);
    PTRef previous = getLevelTransition(power - 1);
    solver.insertFormula(logic.mkAnd(previous, getNextVersion(previous)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}

bool TPABasic::checkFixedPoint(unsigned short power) {
    assert(power >= 3);
    verifyLevel(power);
    for (unsigned short i = 3; i <= power; ++i) {
        PTRef currentLevelTransition = getLevelTransition(i);
        // first check if it is fixed point with respect to initial state
        SMTConfig config;
        {
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({currentLevelTransition, getNextVersion(transition), logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != s_False) {
                solver.push();
                solver.insertFormula(init);
                satres = solver.check();
                if (satres == s_False) {
                    restrictedInvariant = true;
                }
            }
            if (satres == s_False) {
                if (verbose() > 0) {
                    std::cout << "; Right fixed point detected in on level " << i << " from " << power << std::endl;
                    std::cout << "; Fixed point detected for " << (not restrictedInvariant ? "whole transition relation" : "transition relation restricted to init") << std::endl;
                }
                if (options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true") {
                    //                     std::cout << "Computing inductive invariant" << std::endl;
                    inductiveInvariant = getNextVersion(QuantifierElimination(logic).keepOnly(logic.mkAnd(init, currentLevelTransition), getStateVars(1)), -1);
                }
                return true;
            }
        }
        // now check if it is fixed point with respect to bad states
        {
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({transition, getNextVersion(currentLevelTransition), logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != s_False) {
                solver.push();
                solver.insertFormula(getNextVersion(query, 2));
                satres = solver.check();
                if (satres == s_False) {
                    restrictedInvariant = true;
                }
            }
            if (satres == s_False) {
                if (verbose() > 0) {
                    std::cout << "; Left fixed point detected on level " << i << " from " << power << std::endl;
                    std::cout << "; Fixed point detected for " << (not restrictedInvariant ? "whole transition relation" : "transition relation restricted to bad") << std::endl;
                }
                if (options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true") {
                    // std::cout << "Computing inductive invariant" << std::endl;
                    inductiveInvariant = logic.mkNot(QuantifierElimination(logic).keepOnly(logic.mkAnd(currentLevelTransition,
                        getNextVersion(query)), getStateVars(0)));
                }
                return true;
            }
        }
    }
    return false;
}