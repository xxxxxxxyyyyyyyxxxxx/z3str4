/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    arr_tactic.h

Abstract:

    Tactic for using the arr solver

Author:

    John Lu and Stefan Siemer

Notes:

--*/
#ifndef ARR_TACTIC_H_
#define ARR_TACTIC_H_

#include "util/params.h"
#include "tactic/goal_util.h"

class ast_manager;
class tactic;

tactic * mk_arr_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("arr",  "use arr string solver.", "mk_arr_tactic(m, p)")
*/


#endif
