/*
Module name:
    ext_strToRegex_tactic.h

Abstract:
    Tactic that performs global formula rewriting on string terms for extended constraints

Authors:
    Stefan Siemer and John Lu
*/

#ifndef ext_strToRegex_tactic_H_
#define ext_strToRegex_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic* mk_ext_strToRegex_tactic(ast_manager& m, params_ref const& p);

/*
ADD_TACTIC("ext_strToRegex", "Rewrite extended predicates to Regex", "mk_ext_strToRegex_tactic(m, p)")
*/

#endif // !defined ext_strToRegex_tactic_H_
