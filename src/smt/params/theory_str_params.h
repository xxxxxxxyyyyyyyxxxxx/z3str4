/*++
Module Name:

    theory_str_params.h

Abstract:

    Parameters for string theory plugin

Author:

    Murphy Berzish (mtrberzi) 2016-12-13

Revision History:

--*/

#pragma once

#include "util/params.h"

struct theory_str_params {
    /*
     * If AssertStrongerArrangements is set to true,
     * the implications that would normally be asserted during arrangement generation
     * will instead be asserted as equivalences.
     * This is a stronger version of the standard axiom.
     * The Z3str2 axioms can be simulated by setting this to false.
     */
    bool m_StrongArrangements = true;

    /*
     * If AggressiveLengthTesting is true, we manipulate the phase of length tester equalities
     * to prioritize trying concrete length options over choosing the "more" option.
     */
    bool m_AggressiveLengthTesting = false;

    /*
     * Similarly, if AggressiveValueTesting is true, we manipulate the phase of value tester equalities
     * to prioritize trying concrete value options over choosing the "more" option.
     */
    bool m_AggressiveValueTesting = false;

    /*
     * If AggressiveUnrollTesting is true, we manipulate the phase of regex unroll tester equalities
     * to prioritize trying concrete unroll counts over choosing the "more" option.
     */
    bool m_AggressiveUnrollTesting = true;

    /*
     * If UseFastLengthTesterCache is set to true,
     * length tester terms will not be generated from scratch each time they are needed,
     * but will be saved in a map and looked up.
     */
    bool m_UseFastLengthTesterCache = false;

    /*
     * If UseFastValueTesterCache is set to true,
     * value tester terms will not be generated from scratch each time they are needed,
     * but will be saved in a map and looked up.
     */
    bool m_UseFastValueTesterCache = true;

    /*
     * If StringConstantCache is set to true,
     * all string constants in theory_str generated from anywhere will be cached and saved.
     */
    bool m_StringConstantCache = true;

    double m_OverlapTheoryAwarePriority = -0.1;

    /*
     * RegexAutomata_DifficultyThreshold is the lowest difficulty above which Z3str3
     * will not eagerly construct an automaton for a regular expression term.
     */
    unsigned m_RegexAutomata_DifficultyThreshold = 1000;

    /*
     * RegexAutomata_IntersectionDifficultyThreshold is the lowest difficulty above which Z3str3
     * will not eagerly intersect automata to check unsatisfiability.
     */
    unsigned m_RegexAutomata_IntersectionDifficultyThreshold = 1000;

    /*
     * RegexAutomata_FailedAutomatonThreshold is the number of failed attempts to build an automaton
     * after which a full automaton (i.e. with no length information) will be built regardless of difficulty.
     */
    unsigned m_RegexAutomata_FailedAutomatonThreshold = 10;

    /*
     * RegexAutomaton_FailedIntersectionThreshold is the number of failed attempts to perform automaton
     * intersection after which intersection will always be performed regardless of difficulty.
     */
    unsigned m_RegexAutomata_FailedIntersectionThreshold = 10;

    /*
     * RegexAutomaton_LengthAttemptThreshold is the number of attempts to satisfy length/path constraints
     * before which we begin checking unsatisfiability of a regex term.
     */
    unsigned m_RegexAutomata_LengthAttemptThreshold = 10;
    /*
     * If FixedLengthRefinement is true and the fixed-length equation solver is enabled,
     * Z3str3 will use abstraction refinement to handle formulas that would result in disjunctions or expensive
     * reductions to fixed-length formulas.
     */
    bool m_FixedLengthRefinement = false;

    /*
     * PreMilliseconds is the number of milliseconds to try the sequence solver on disjunctive fragment queries.
     */
    unsigned m_PreMilliseconds = 1000;


    unsigned m_MidMilliseconds = 1000;

    /*
    * If MultisetCheck is true, we use the quick multiset check to
    * help solve word equations.
    */
    bool m_MultisetCheck = false;
    /*
     * If rewriterTactic is true, we apply a global formula rewriter prior to SMT solving.
     * This can enable simplifications that aren't caught by the local term rewriter.
     */
    bool m_RewriterTactic = true;
    /*
     * StrTactic allows bypassing of the portfolio selection in z3str3_tactic for testing.
     * The options are:
     * 0 (default) - all tactics are used
     * 1 - length abstraction and fixed-length solving
     * 2 - arrangement solver (traditional Z3str)
     */
    symbol m_StrTactic = symbol("z3str4");


    /*
     * If FixedLengthNaiveCounterexamples is true and the fixed-length equation solver is enabled,
     * Z3str3 will only construct simple counterexamples to block unsatisfiable length assignments
     * instead of attempting to learn more complex lessons.
     */
    bool m_FixedLengthNaiveCounterexamples = true;

    /*
     * If ShareConstraints is true, Z3str3 will mark certain axioms and conflict clauses as "shared" and
     * will propagate them to other solvers if it fails to find a solution.
     * This has no effect outside of the portfolio tactic or if no other tactic is called after Z3str3 runs.
     */
    bool m_ShareConstraints = true;
    bool m_SearchOverlaps = false;
    unsigned m_SearchOverlapsMilliseconds = 1000;
    bool m_FixedLengthPreprocessing = false;
    unsigned m_FixedLengthIterations = 5;
    // Enables the regex prefix/suffix heuristic, which checks for common prefixes/suffixes of intersected regex constraints.
    bool m_UseRegexPrefixSuffixHeuristic = true;
    // Construct full length constraints for automata when expected to be linear.
    bool m_RegexAutomata_ConstructLinearLengthConstraints = true;

    // Construct lower/upper bounds for regex automata.
    bool m_RegexAutomata_ConstructBounds = true;


    theory_str_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
    void display(std::ostream & out) const;
};
