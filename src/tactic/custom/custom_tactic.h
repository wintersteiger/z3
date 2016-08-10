/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    custom_tactic.h

Abstract:

    A custom tactic.

Author:

    Christoph (cwinter) 2016-08-10

Notes:

--*/
#ifndef CUSTOM_TACTIC_H_
#define CUSTOM_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_custom_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("custom",  "a custom tactic.", "mk_custom_tactic(m, p)")
*/

#endif
