/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ufbv_templatation_tactic.h

Abstract:

    Tactic for solving UFBV problems via automatic function template refinement.

Author:

    Christoph (cwinter) 2015-11-06

Notes:

--*/
#ifndef UFBV_TEMPLATATION_TACTIC_H_
#define UFBV_TEMPLATATION_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_ufbv_templatation_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("ufbv-templatation", "Tactic for solving UFBV problems via automatic function template refinement.", "mk_ufbv_templatation_tactic(m, p)")
*/

#endif
