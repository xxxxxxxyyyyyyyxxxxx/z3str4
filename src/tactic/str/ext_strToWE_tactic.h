/*
Module name:
	ext_strToWE_tactic.h

Abstract:
    Tactic that performs global formula rewriting of extended string predicates to word equations

Authors:
    Stefan Siemer and John Lu
*/

#ifndef ext_strToWE_tactic_H_
#define ext_strToWE_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic* mk_ext_strToWE_tactic(ast_manager& m, params_ref const& p);

/*
ADD_TACTIC("ext_strToWE", "Rewrite extended predicates to word equations.", "mk_ext_strToWE_tactic(m, p)")
*/

#endif // !defined ext_strToWE_tactic_H_
