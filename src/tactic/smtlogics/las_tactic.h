/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    las_tactic.h

Abstract:

    Tactic for using the las solver

Author:

    John Lu and Stefan Siemer

Notes:

--*/
#ifndef LAS_TACTIC_H_
#define LAS_TACTIC_H_

#include "util/params.h"
#include "tactic/goal_util.h"

class ast_manager;
class tactic;

tactic * mk_las_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("las",  "use las string solver.", "mk_las_tactic(m, p)")
*/


#endif
