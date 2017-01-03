/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    smt_search_log.h

Abstract:

    Functions to extract replayable search logs.

Author:

    Christoph (cwinter) 2017-01-14.

Revision History:

--*/
#ifndef SMT_SEARCH_LOG_H_
#define SMT_SEARCH_LOG_H_

#include<fstream>

#include"ast.h"
#include"smt_quantifier.h"
#include"smt_conflict_resolution.h"

namespace smt {

    class context;

    class search_log {
        ast_manager        & m;
        context            & m_ctx;
        quantifier_manager & m_qmanager;
        params_ref           m_pp_params;
        std::ofstream      * m_strm;
        std::streampos       m_before_last_cmd;

    public:
        search_log(ast_manager & m, context & ctx, quantifier_manager & qm);
        ~search_log();

        void enable(smt_params & m_fparams);

        void note(char const * msg);
        void push(unsigned scope_lvl);
        void pop(unsigned scope_lvl, unsigned num_scopes);
        void decide(expr * e, bool is_pos);
        void lemma(conflict_resolution & cr, unsigned levels);
        void log_instance(quantifier * q, unsigned num_bindings, enode * const * bindings, expr_ref instance, unsigned generation, unsigned scope);
        void check_sat(lbool expected_result, statistics stats, unsigned num_assumptions = 0);

        bool is_instance(expr const * e, quantifier * & q) const;
        void mk_instance_bindings(expr const * e, unsigned & num_bindings, ptr_vector<enode> & bindings);
        bool replay_instance(expr_ref const & instance);

        expr_ref mk_log_instance(quantifier * q, unsigned num_bindings, enode * const * bindings) const;
    };

};

#endif
