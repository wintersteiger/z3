/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    drop_patterns_tactic.cpp

Abstract:

    Tactic that drops (removes) patterns from quantifiers.

Author:

    Christoph (cwinter) 2016-10-28

Notes:

--*/
#include"tactical.h"
#include"rewriter.h"
#include"rewriter_def.h"
#include"cooperate.h"
#include"drop_patterns_tactic.h"

struct drop_patterns_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;
    params_ref                 m_params;
    expr_ref_vector            m_out;
    sort_ref_vector            m_bindings;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    ast_manager & m() const { return m_manager; }

    drop_patterns_rewriter_cfg(ast_manager & m, params_ref const & p) :
        m_manager(m),
        m_params(p),
        m_out(m),
        m_bindings(m)
    {
        updt_params(p);
    }

    ~drop_patterns_rewriter_cfg() {}

    void cleanup_buffers() { m_out.finalize(); }

    void reset() {}

    void updt_local_params(params_ref const & _p) {}

    void updt_params(params_ref const & p) {}

    bool max_steps_exceeded(unsigned num_steps) const {
        cooperate("drop-patterns");
        return num_steps > m_max_steps;
    }

    bool pre_visit(expr * t)
    {
        if (is_quantifier(t)) {
            quantifier * q = to_quantifier(t);
            TRACE("drop_patterns", tout << "pre_visit quantifier [" << q->get_id() << "]: " << mk_ismt2_pp(q->get_expr(), m()) << std::endl;);
            sort_ref_vector new_bindings(m_manager);
            for (unsigned i = 0; i < q->get_num_decls(); i++)
                new_bindings.push_back(q->get_decl_sort(i));
            SASSERT(new_bindings.size() == q->get_num_decls());
            m_bindings.append(new_bindings);
        }
        return true;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        return BR_FAILED;
    }

    bool reduce_quantifier(quantifier * old_q,
        expr * new_body,
        expr * const * new_patterns,
        expr * const * new_no_patterns,
        expr_ref & result,
        proof_ref & result_pr) {
        unsigned curr_sz = m_bindings.size();
        SASSERT(old_q->get_num_decls() <= curr_sz);
        unsigned num_decls = old_q->get_num_decls();
        unsigned old_sz = curr_sz - num_decls;
        string_buffer<> name_buffer;
        result = m().mk_quantifier(old_q->is_forall(),
                                    old_q->get_num_decls(),
                                    old_q->get_decl_sorts(),
                                    old_q->get_decl_names(),
                                    new_body,
                                    old_q->get_weight(), old_q->get_qid(), old_q->get_skid(),
                                    0, 0, 0, 0);
        result_pr = 0;
        m_bindings.shrink(old_sz);
        TRACE("drop_patterns", tout << "reduce_quantifier[" << old_q->get_depth() << "]: " <<
                                mk_ismt2_pp(old_q->get_expr(), m()) << std::endl <<
                                " new body: " << mk_ismt2_pp(new_body, m()) << std::endl;
                                tout << "result = " << mk_ismt2_pp(result, m()) << std::endl;);
        return true;
    }

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
        return false;
    }
};


struct drop_patterns_rewriter : public rewriter_tpl<drop_patterns_rewriter_cfg> {
    drop_patterns_rewriter_cfg m_cfg;
    drop_patterns_rewriter(ast_manager & m, params_ref const & p) :
        rewriter_tpl<drop_patterns_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }
};

class drop_patterns_tactic : public tactic {
    ast_manager &     m;
    params_ref m_params;
    drop_patterns_rewriter m_rw;
    unsigned          m_num_steps;

    bool              m_proofs_enabled;
    bool              m_produce_models;
    bool              m_produce_unsat_cores;

public:
    drop_patterns_tactic(ast_manager & m, params_ref const & p) :
        m(m),
        m_params(p),
        m_rw(m, p),
        m_proofs_enabled(false),
        m_produce_models(false),
        m_produce_unsat_cores(false) {
        //m_rw(m, m_conv, p),
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(drop_patterns_tactic, m, m_params);
    }

    virtual ~drop_patterns_tactic() { }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_rw.cfg().updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
    }

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        try {
            SASSERT(g->is_well_sorted());
            m_proofs_enabled = g->proofs_enabled();
            m_produce_models = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();

            mc = 0; pc = 0; core = 0; result.reset();
            tactic_report report("drop-patterns", *g);
            m_rw.reset();

            TRACE("drop_patterns", tout << "BEFORE: " << std::endl; g->display(tout););

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            m_num_steps = 0;
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                m_rw(curr, new_curr, new_pr);
                m_num_steps += m_rw.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }

            //if (g->models_enabled())
            //    mc = // necessary?

            g->inc_depth();
            result.push_back(g.get());

            SASSERT(g->is_well_sorted());
            TRACE("drop_patterns", tout << "AFTER: " << std::endl; g->display(tout);
            if (mc) mc->display(tout); tout << std::endl; );
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    virtual void cleanup() {
        m_rw.reset();
    }

};

tactic * mk_drop_patterns_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(drop_patterns_tactic, m, p));
}