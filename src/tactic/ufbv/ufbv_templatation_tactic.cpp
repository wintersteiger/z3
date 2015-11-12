/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ufbv_templatation_tactic.cpp

Abstract:

    Tactic for solving UFBV problems via automatic function template refinement.

Author:

    Christoph (cwinter) 2015-11-06

Notes:

--*/
#include"tactical.h"
#include"simplifier.h"
#include"basic_simplifier_plugin.h"
#include"ufbv_templatation.h"
#include"ufbv_templatation_tactic.h"

class ufbv_templatation_tactic : public tactic {

    struct imp {
        ast_manager & m_manager;
        bool m_cancel;
        ufbv_templatation tmpl;

        imp(ast_manager & m, params_ref const & p) :
            m_manager(m),
            m_cancel(false),
            tmpl(m, p) {
            updt_params(p);
        }

        ast_manager & m() const { return m_manager; }

        void set_cancel(bool f) {
            m_cancel = f;
        }

        void operator()(goal_ref const & g,
            goal_ref_buffer & result,
            model_converter_ref & mc,
            proof_converter_ref & pc,
            expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("ufbv-templatation", *g);
            fail_if_proof_generation("ufbv-templatation", g);
            fail_if_unsat_core_generation("ufbv-templatation", g);

            bool produce_proofs = g->proofs_enabled();

            TRACE("ufbv_templatation", tout << "Before:\n"; g->display(tout););

            for (unsigned i = 0; i < g->size(); i++)
                tmpl.add(g->form(i));

            lbool s = tmpl.check_sat(0, 0);
            switch (s) {
            case l_true:
                g->reset();
                result.push_back(g.get());
                break;
            case l_false: {
                proof * pr = 0;
                expr_dependency * lcore = 0;
                g->reset();
                g->assert_expr(m_manager.mk_false(), pr, lcore);
                result.push_back(g.get());
                break;
            }
            case l_undef:
                throw tactic_exception("ufbv-templatation failed to show goal to be sat/unsat");
                break;
            }
            mc = 0;

            g->inc_depth();
            result.push_back(g.get());
            TRACE("ufbv-templatation", g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void updt_params(params_ref const & p) {
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:
    ufbv_templatation_tactic(ast_manager & m, params_ref const & p) :
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(ufbv_templatation_tactic, m, m_params);
    }

    virtual ~ufbv_templatation_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        insert_max_memory(r);
        insert_produce_models(r);
        insert_produce_proofs(r);
    }

    virtual void operator()(goal_ref const & in,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }

    virtual void cleanup() {
        ast_manager & m = m_imp->m();
        imp * d = alloc(imp, m, m_params);
#pragma omp critical (tactic_cancel)
        {
            std::swap(d, m_imp);
        }
        dealloc(d);
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_ufbv_templatation_tactic(ast_manager & m, params_ref const & p) {
    return alloc(ufbv_templatation_tactic, m, p);
}