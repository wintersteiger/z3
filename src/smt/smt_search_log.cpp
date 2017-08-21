/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    smt_search_log.cpp

Abstract:

    Functions to extract replayable search logs.

Author:

    Christoph (cwinter) 2017-01-14.

Revision History:

--*/
#include "ast/ast.h"
#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"

#include "smt/smt_search_log.h"

namespace smt {

    search_log::search_log(ast_manager & m, context & ctx, quantifier_manager & qm) :
        m(m),
        m_ctx(ctx),
        m_qmanager(qm),
        m_strm(0) {
        m_pp_params.set_bool("single_line", true);
    }

    search_log::~search_log() {
        if (m_strm) {
            m_strm->flush();
            m_strm->close();
            dealloc(m_strm);
            m_strm = 0;
        }
    }

    void search_log::enable(smt_params & m_fparams) {
        if (m_strm) {
            m_strm->flush();
            m_strm->close();
            dealloc(m_strm);
            m_strm = 0;
        }

        char const * filename = m_fparams.m_search_log;
        if (strcmp(filename, "") != 0) {
            m_strm = alloc(std::ofstream, filename, std::ios::out | std::ios::app);
            m_before_last_cmd = m_strm->tellp();
        }
    }

    void search_log::note(char const * msg) {
        if (m_strm) {
            m_before_last_cmd = m_strm->tellp();
            (*m_strm) << ";; " << msg << std::endl;
        }
    }

    void search_log::push(unsigned scope_lvl) {
        if (m_strm) {
            m_before_last_cmd = m_strm->tellp();
            (*m_strm) << "(push) ;; to " << scope_lvl << std::endl;
        }
    }


    void search_log::pop(unsigned scope_lvl, unsigned num_scopes) {
        if (m_strm) {
            m_before_last_cmd = m_strm->tellp();
            unsigned new_lvl = scope_lvl - num_scopes;
            (*m_strm) << "(pop " << num_scopes << ") ;; to " << new_lvl << std::endl;
        }
    }

    void search_log::decide(expr * e, bool is_pos) {
        if (m_strm) {
            (*m_strm) << "(decide ";
            if (!is_pos) (*m_strm) << "(not ";
            (*m_strm) << mk_ismt2_pp(e, m, m_pp_params);
            if (!is_pos) (*m_strm) << ")";
            (*m_strm) << ")" << std::endl;
        }
    }

    void search_log::lemma(conflict_resolution & cr, unsigned levels) {
        if (m_strm) {
            // undo the preceeding (pop).
            m_strm->seekp(m_before_last_cmd);

            m_before_last_cmd = m_strm->tellp();
            (*m_strm) << "(lemma " << levels;
            unsigned sz = cr.get_lemma_num_literals();
            expr * const * lits = cr.get_lemma_atoms();
            if (sz == 1)
                (*m_strm) << " " << mk_ismt2_pp(lits[0], m, m_pp_params);
            else {
                (*m_strm) << " (or";
                for (unsigned i = 0; i < sz; i++)
                    (*m_strm) << " " << mk_ismt2_pp(lits[i], m, m_pp_params);
                (*m_strm) << ")";
            }
            (*m_strm) << ")" << std::endl;
        }
    }

    void search_log::log_instance(quantifier * q,
                                  unsigned num_bindings, enode * const * bindings,
                                  expr_ref instance,
                                  unsigned generation, unsigned scope) {
        TRACE("qi_log_instance_detail",
            tout << "Quantifier (lqid=" << m_qmanager.get_qid(q) << "): " << std::endl;
            tout << mk_ismt2_pp(q, m) << std::endl;
            tout << "Bindings: " << std::endl;
            for (unsigned i = 0; i < num_bindings; i++)
                tout << mk_ismt2_pp(bindings[i]->get_owner(), m) << std::endl;
            tout << "Instance: " << std::endl;
            tout << mk_ismt2_pp(instance, m) << std::endl; );

        TRACE("qi_log_instance_short",
            tout << "Instantiate lqid=" << m_qmanager.get_qid(q) << " with: " << std::endl;
            for (unsigned i = 0; i < num_bindings; i++)
                tout << mk_ismt2_pp(bindings[i]->get_owner(), m) << std::endl; );

        if (m_strm) {
            m_before_last_cmd = m_strm->tellp();
            expr_ref instance(mk_log_instance(q, num_bindings, bindings), m);
            (*m_strm) << "(add-instance " << mk_ismt2_pp(instance, m, m_pp_params) << ") ;; gen: " << generation << " scope: " << scope << std::endl;
        }
    }

    void search_log::check_sat(lbool expected_result, statistics stats, unsigned num_assumptions) {
        if (m_strm) {
            m_before_last_cmd = m_strm->tellp();
            (*m_strm) << "(check-sat)" << std::endl;
            (*m_strm) << ";; was " << ((expected_result == l_true) ? "sat" :
                                       (expected_result == l_false) ? "unsat" :
                                       "unknown") << std::endl;
            ::statistics stat;
            m_qmanager.collect_statistics(stat);
            (*m_strm) << ";; Instances: " << stat.get_uint("quant instantiations") << std::endl;
            (*m_strm) << ";; Decisions: " << stats.m_num_decisions << std::endl;
            (*m_strm) << ";; Conflicts: " << stats.m_num_conflicts << std::endl;
        }
    }

    bool search_log::is_instance(expr const * e, quantifier * & q) const {
        // Instances are represented by terms of the form
        // (=>  (! false :lblpos k!<lqid> :lblpos k!<base-idx>)
        //      (exists ((x ...) ...) (! (and (= ...) (= ...) ...))))

        if (m.is_implies(e)) {
            expr * lit = to_app(e)->get_arg(0);
            expr * qe = to_app(e)->get_arg(1);
            buffer<symbol> names;
            bool pos;
            expr * lbl;
            if (m.is_label(lit, pos, names, lbl) &&
                pos && names.size() == 1 &&
                is_app_of(lbl, m.get_basic_family_id(), OP_FALSE) &&
                is_exists(qe)) {
                quantifier * iq = to_quantifier(qe);
                unsigned iq_num_decls = iq->get_num_decls();
                expr * pq_body = iq->get_expr();
                sort * const * iq_sorts = iq->get_decl_sorts();
                if (pq_body->get_kind() != AST_APP)
                    return false;

                symbol qid = names[0];
                if (!m_qmanager.find(qid, q)) {
                    warning_msg("quantifier with qid '%s' not found; ignoring instance", qid.str().c_str());
                    return false;
                }
                else {
                    sort * const * q_sorts = q->get_decl_sorts();
                    if (iq_num_decls != q->get_num_decls())
                        return false;
                    for (unsigned i = 0; i < iq_num_decls; i++)
                        if (iq_sorts[i] != q_sorts[i])
                            return false;
                    if (!m.is_and(pq_body))
                        return false;
                    app * a_body = to_app(pq_body);
                    unsigned sz = a_body->get_num_args();
                    for (unsigned i = 0; i < sz; i++) {
                        expr * ai = a_body->get_arg(i);
                        if (!m.is_eq(ai))
                            return false;
                        app * aai = to_app(ai);
                        if (aai->get_num_args() != 2)
                            return false;
                        expr * var = aai->get_arg(0);
                        expr_ref val(aai->get_arg(1), m);
                        if (var->get_kind() != AST_VAR ||
                            to_var(var)->get_idx() != (iq_num_decls - i - 1) ||
                            !is_ground(val))
                            return false;
                    }
                    return true;
                }
            }
        }
        return false;
    }

    void search_log::mk_instance_bindings(expr const * e,
                                          unsigned & num_bindings,  ptr_vector<smt::enode> & bindings) {
        app const * a = to_app(to_quantifier(to_app(e)->get_arg(1))->get_expr());
        num_bindings = a->get_num_args();
        app * const * eqs = (app * const *)a->get_args();

        for (unsigned i = 0; i < num_bindings; i++) {
            expr * var = eqs[i]->get_arg(0);
            expr * val = eqs[i]->get_arg(1);

            expr_ref sval(m);
            proof_ref pr(m);
            m_ctx.get_simplifier()(val, sval, pr);

            if (!m_ctx.e_internalized(sval) && !m_ctx.b_internalized(sval)) {
                TRACE("qi_log_instance_bindings", tout << "(= " << mk_ismt2_pp(var, m) << " " << mk_ismt2_pp(sval, m) << ")" << std::endl;);
                m_ctx.internalize(sval, false); // +generation?
            }

            SASSERT(m_ctx.e_internalized(sval) || m_ctx.b_internalized(sval));
            bindings.push_back(m_ctx.find_enode(sval));
        }
    }

    bool search_log::replay_instance(expr_ref const & instance) {
        quantifier * q;

        if (!is_instance(instance, q)) {
            throw default_exception("Invalid quantifier instance");
        }
        else {
            TRACE("qi_log_instance", tout << mk_ismt2_pp(instance, m) << std::endl;);
            unsigned num_bindings;
            ptr_vector<smt::enode> bindings;
            mk_instance_bindings(instance, num_bindings, bindings);
            bool r = m_qmanager.add_instance(q, num_bindings, bindings.c_ptr());
            m_qmanager.propagate();
            return r;
        }
    }

    expr_ref search_log::mk_log_instance(quantifier * q, unsigned num_bindings, enode * const * bindings) const {
        expr_ref_vector eqs(m);
        for (unsigned i = 0; i < num_bindings; i++) {
            unsigned vinx = num_bindings - i - 1;
            sort_ref vsrt(q->get_decl_sort(i), m);
            var_ref v(m.mk_var(vinx, vsrt), m);
            expr_ref e(m.mk_eq(v, bindings[i]->get_owner()), m);
            eqs.push_back(e);
        }
        expr_ref body(m.mk_and(num_bindings, eqs.c_ptr()), m);
        vector<symbol> names(num_bindings);
        for (unsigned i = 0; i < num_bindings; i++) {
            std::stringstream ss;
            ss << "$" << i;
            names[i] = symbol(ss.str().c_str());
        }
        quantifier_ref ex(m.mk_exists(q->get_num_decls(), q->get_decl_sorts(), names.c_ptr(), body), m);
        symbol qid(m_qmanager.get_qid(q));
        expr_ref qll(m.mk_label(true, qid, m.mk_false()), m);
        expr_ref impl(m.mk_implies(qll, ex), m);
        return impl;
    }

}
