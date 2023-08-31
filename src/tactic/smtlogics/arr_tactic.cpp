/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    arr_tactic.cpp

Abstract:

    Tactic for ARR solver

Author:

    John Lu and Stefan Siemer

Update:


Notes:

--*/
#include "util/params.h"
#include "tactic/tactical.h"
#include "tactic/smtlogics/arr_tactic.h"
#include "tactic/str/ext_str_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "smt/params/smt_params.h"
#include "ast/ast_pp.h"


/*Can this go because the ext_str_tactic rewriting and all the other simplifications will be part of the learning?
tactic * mk_rewriter_las_tactic(ast_manager & m, params_ref const & p) {
    smt_params m_smt_params;
    m_smt_params.updt_params(p);
   return and_then(mk_simplify_tactic(m, p), and_then(mk_ctx_simplify_tactic(m, p), and_then(mk_ext_str_tactic(m, p), mk_simplify_tactic(m, p))));
}*/

tactic * mk_arr_tactic(ast_manager & m, params_ref const & p) {
    smt_params m_smt_params;
    m_smt_params.updt_params(p);
    TRACE("str", tout << "using Z3str3 portfolio tactic " << m_smt_params.m_StrTactic << std::endl;);

    params_ref preprocess_p = p;
    preprocess_p.set_bool("str.fixed_length_preprocessing", true);
    preprocess_p.set_bool("str.fixed_length_models", true);
    preprocess_p.set_bool("str.multiset_check", true);
    preprocess_p.set_bool("str.search_overlaps", false);
    preprocess_p.set_uint("str.regex_automata_length_attempt_threshold", 3);
    preprocess_p.set_uint("str.regex_automata_failed_automaton_threshold", 3);
    preprocess_p.set_uint("str.regex_automata_failed_intersection_threshold", 1);
    preprocess_p.set_sym("string_solver", symbol("z3str3"));

    params_ref general_p = p;
    general_p.set_bool("str.fixed_length_preprocessing", false);
    general_p.set_bool("str.fixed_length_models", true);
    general_p.set_bool("str.multiset_check", false);
    general_p.set_sym("string_solver", symbol("z3str3"));
    general_p.set_bool("str.search_overlaps", false);

    params_ref seq_p = p;
    seq_p.set_sym("string_solver", symbol("seq")); 
    seq_p.set_bool("tactic_model_validation", true); // check what is it

    params_ref search_overlaps_p = p;
    search_overlaps_p.set_bool("str.fixed_length_preprocessing", false);
    search_overlaps_p.set_bool("str.fixed_length_models", true);
    search_overlaps_p.set_bool("str.multiset_check", false);
    search_overlaps_p.set_sym("string_solver", symbol("z3str3"));
    search_overlaps_p.set_bool("str.search_overlaps", true);

    tactic * z3str3_1 = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), preprocess_p);
    tactic * z3str3_2 = using_params(mk_smt_tactic(m), general_p);
    
	// arrangement solver only
	TRACE("str", tout << "z3str3 tactic bypassed: performing arrangement solving" << std::endl;);
	tactic * st = using_params(z3str3_2, p);
	return st;
    

}
