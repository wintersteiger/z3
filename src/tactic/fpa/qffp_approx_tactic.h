/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qffp_approx_tactic.h

Abstract:

    Approximating tactic for QF_FP benchmarks.

Author:

    Christoph (cwinter) 2015-06-13

Notes:


--*/
#ifndef _QFFP_APPROX_TACTIC_H_
#define _QFFP_APPROX_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qffp_approx_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qffp_approx", "(try to) solve goal using the tactic for QF_FP.", "mk_qffp_approx_tactic(m, p)")
*/

#endif
