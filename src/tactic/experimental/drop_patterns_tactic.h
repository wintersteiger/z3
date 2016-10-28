/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    drop_patterns_tactic.h

Abstract:

    Tactic that drops (removes) patterns from quantifiers.

Author:

    Christoph (cwinter) 2016-10-28

Notes:

--*/
#ifndef DROP_PATTERNS_TACTIC_H_
#define DROP_PATTERNS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_drop_patterns_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
ADD_TACTIC("drop-patterns", "drop patterns from quantifiers.", "mk_drop_patterns_tactic(m, p)")
*/

#endif

