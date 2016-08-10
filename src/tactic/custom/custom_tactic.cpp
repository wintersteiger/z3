/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    custom_tactic.cpp

Abstract:

    A custom tactic.

Author:

    Christoph (cwinter) 2016-08-10

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bv_bounds_tactic.h"
#include"solve_eqs_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"smt_tactic.h"
#include"reduce_args_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"ackermannize_bv_tactic.h"
#include"qfbv_tactic.h"


tactic * mk_custom_tactic(ast_manager & m, params_ref const & p) {
// #ifdef USE_ARRAY_TH
// #define SMT_THEORY "QF_AUFBV"
//   s = Z3_mk_solver_for_logic(ctx(), Z3_mk_string_symbol(ctx(), SMT_THEORY));
//   Z3_solver_inc_ref(ctx(), s);
// #endif
  
  params_ref prms = p;
  prms.set_bool("elim_and", true);
  prms.set_bool("blast_distinct", true);
  prms.set_str("smt.logic", "QF_UFBV");  
  
  tactic * st = using_params(
      and_then(mk_simplify_tactic(m),
          mk_propagate_values_tactic(m),
          //mk_bv_bounds_tactic(m),
          mk_solve_eqs_tactic(m),
          mk_elim_uncnstr_tactic(m),
          mk_reduce_args_tactic(m),
          mk_simplify_tactic(m),
          mk_bv_size_reduction_tactic(m),
          mk_max_bv_sharing_tactic(m),
          //mk_ackermannize_bv_tactic(m,p),
          cond(mk_is_qfbv_probe(), mk_qfbv_tactic(m, p), mk_smt_tactic())),
      prms);
  
  st->updt_params(p);
  return st;
}
