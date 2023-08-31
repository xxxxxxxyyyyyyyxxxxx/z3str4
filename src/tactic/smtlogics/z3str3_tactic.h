/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    z3str3_tactic.h

Abstract:

    Tactic for string instances that synergizes with Z3str3

Author:

    Murphy Berzish (mtrberzi) 2019-01-10

Notes:

--*/
#ifndef Z3STR3_TACTIC_H_
#define Z3STR3_TACTIC_H_

#include "util/params.h"
#include "tactic/goal_util.h"

class ast_manager;
class tactic;

tactic * mk_z3str3_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("z3str3",  "use z3str3 tricks to solve string problems.", "mk_z3str3_tactic(m, p)")
*/

probe * mk_is_cf_probe();

/*
  ADD_PROBE("is-cf_probe", "true if the formula is a conjunctive fragment.", "mk_is_cf_probe()")
*/


probe * mk_has_word_eq_probe();

/*
  ADD_PROBE("has_word_eq", "true if the formula has a word equation.", "mk_has_word_eq_probe()")
*/


probe * mk_has_regex_probe();

/*
  ADD_PROBE("has_regeq", "true if the formular has a regular expression.", "mk_has_regex_probe()")
*/


#endif
