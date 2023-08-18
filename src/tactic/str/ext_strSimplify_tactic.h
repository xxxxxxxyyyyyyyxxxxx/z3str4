/*
Module name:
    ext_strSimplify_tactic.h

Abstract:
    Tactic that performs global formula rewriting on extended string predicates.

Authors:
    Stefan Siemer and John Lu
*/

#ifndef ext_strSimplify_tactic_H_
#define ext_strSimplify_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic* mk_ext_strSimplify_tactic(ast_manager& m, params_ref const& p);

/*
ADD_TACTIC("ext_strSimplify", "Simplify extended string predicates", "mk_ext_strSimplify_tactic(m, p)")
*/

#endif // !defined ext_strSimplify_tactic_H_
