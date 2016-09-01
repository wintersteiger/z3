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
#include"qfufbv_tactic.h"
#include"ast_pp_util.h"


class print_info_tactic : public skip_tactic {
    tactic * m_t;
    unsigned m_lvl;
    std::string m_msg;

public:
    print_info_tactic(tactic * t, unsigned lvl, const char * msg) : m_t(t), m_lvl(lvl), m_msg(msg) {
        SASSERT(m_t);
        m_t->inc_ref();
    }

    ~print_info_tactic() {
        m_t->dec_ref();
    }

    virtual void updt_params(params_ref const & p) { if (m_t) m_t->updt_params(p); }
    virtual void collect_param_descrs(param_descrs & r) { if (m_t) m_t->collect_param_descrs(r); }
    virtual void collect_statistics(statistics & st) const { if (m_t) m_t->collect_statistics(st); }
    virtual void reset_statistics() { if (m_t) m_t->reset_statistics(); }
    virtual void cleanup() { if (m_t) m_t->cleanup();  };
    virtual void reset() { if (m_t) m_t->reset(); }
    virtual void set_logic(symbol const & l) { if (m_t) m_t->set_logic(l); }
    virtual void set_progress_callback(progress_callback * callback) { if (m_t) m_t->set_progress_callback(callback); }
    virtual tactic * translate(ast_manager & m) { return m_t ? m_t->translate(m) : 0; };

    virtual void operator()(goal_ref const & in,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {

        if (0) {
            std::cerr << "; printing smt" << std::endl;
            expr_ref_vector fmls(in->m());
            unsigned sz = in->size();
            for (unsigned i = 0; i < sz; i++) fmls.push_back(in->form(i));
            ast_pp_util visitor(in->m());
            visitor.collect(fmls);
            visitor.display_decls(std::cerr);
            visitor.display_asserts(std::cerr, fmls, true);
        }

        
        bool have_exception = false;
        tactic_exception te("");

        IF_VERBOSE(m_lvl, verbose_stream() << "(start " << m_msg << ")\n";);

        try {
            have_exception = false;
            (*m_t)(in, result, mc, pc, core);
        }
        catch (tactic_exception & ex) {
            have_exception = true;            
            te = ex;
        }

        if (is_decided_sat(result))
            std::cout << "sat" << std::endl;
        else if (is_decided_unsat(result))
            std::cout << "unsat" << std::endl;
        else
            std::cout << "unknown" << std::endl;

        IF_VERBOSE(m_lvl, verbose_stream() << "(end " << m_msg << ")\n";);
        if (have_exception) throw te;
    }
};

tactic * mk_print_info_tactic(tactic * t, unsigned lvl, const char * msg) {
    return alloc(print_info_tactic, t, lvl, msg);
}

tactic * mk_ackr(ast_manager & m, params_ref const & p) {
    params_ref prms = p;
    prms.set_str("smt.logic", "QF_UFBV");
    return mk_print_info_tactic(
        using_params(mk_qfufbv_ackr_tactic(m, p), prms),
        2, "custom"
    );
}


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

    tactic * st = 0 ? mk_ackr(m, p)
        :
        mk_print_info_tactic(
            using_params(
                and_then(
                    and_then(mk_simplify_tactic(m),
                        mk_propagate_values_tactic(m),
                        //mk_bv_bounds_tactic(m),
                        mk_solve_eqs_tactic(m),
                        mk_elim_uncnstr_tactic(m),
                        mk_reduce_args_tactic(m),
                        mk_simplify_tactic(m),
                        mk_bv_size_reduction_tactic(m)
                        //mk_ackermannize_bv_tactic(m, p), 
                        ),
                    and_then(
                        mk_max_bv_sharing_tactic(m),
                        //mk_qfufbv_ackr_tactic(m, p)
                        cond(mk_is_qfbv_probe(), mk_qfbv_tactic(m, p), mk_smt_tactic(p))
                    )
                ), prms),
            2, "custom");    

    //tactic * st = mk_print_info_tactic(mk_skip_tactic(), 2, "nothing");

    st->updt_params(p);
    return st;
}
