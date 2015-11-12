/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ufbv_templatation.cpp

Abstract:

    CEGAR loop for automatic function template refinement in UFBV formulas.

Author:

    Christoph (cwinter) 2015-11-06

Notes:

--*/
#include"tactical.h"
#include"ast_smt2_pp.h"
#include"ast_pp.h"
#include"rewriter_def.h"
#include"expr_replacer.h"

#include"ufbv_templatation.h"

ufbv_templatation::ufbv_templatation(ast_manager & m, params_ref const & p) :
    m(m),
    m_params(p),
    m_bv_util(m),
    m_goal(m),
    m_bit_blaster(m, p),
    m_sat_solver(p, m.limit(), 0),
    m_atom2bool(m) {
}

ufbv_templatation::~ufbv_templatation() {
    for (templates_t::iterator it = m_templates.begin();
         it != m_templates.end();
         it++)
        m.dec_ref(it->m_value);

    for (calls_t::iterator it = m_calls.begin();
         it != m_calls.end();
         it++)
        m.dec_ref(it->m_value);
}

void ufbv_templatation::add(expr * a) {
    m_goal.assert_expr(a);
}

struct init_proc {
    ast_manager & m;
    bv_util & m_bv_util;
    ufbv_templatation::templates_t & m_templates;
    bool m_has_quantifiers = false;

    init_proc(ast_manager & m, bv_util & u, ufbv_templatation::templates_t & templates) :
        m(m),
        m_bv_util(u),
        m_templates(templates) {
    }

    void operator()(var * n) { }

    void operator()(quantifier * n) {
        m_has_quantifiers = true;
    }

    void operator()(app * n) {
        func_decl * fd = n->get_decl();
        if (fd->get_family_id() == null_family_id && !m_templates.contains(fd)) {
            TRACE("ufbv_templatation", tout << "Tracking " << mk_ismt2_pp(fd, m) << std::endl;);
            expr * initial_template = m.mk_fresh_const(0, fd->get_range());
            m_templates.insert(fd, initial_template);
            m.inc_ref(initial_template);
        }
    }
};

class funccalls_rw_cfg : public default_rewriter_cfg {
    ast_manager      & m;
    params_ref const & m_params;
    ufbv_templatation::templates_t & m_templates;
    obj_map<app, app*> & m_calls;

public:
    funccalls_rw_cfg(
        ast_manager & m,
        params_ref const & p,
        ufbv_templatation::templates_t & t,
        ufbv_templatation::calls_t & c) :
        m(m), m_params(p), m_templates(t), m_calls(c) {}

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        if (m_templates.contains(f)) {
            app_ref cll(m.mk_app(f, num, args), m);
            app * v = 0;
            if (m_calls.find(cll, v))
                result = v;
            else {
                result = m.mk_fresh_const(0, f->get_range());
                app * r = to_app(result);
                m_calls.insert(cll, r);
                m.inc_ref(r);
            }
            result_pr = 0;
            return BR_DONE;
        }
        else
            return BR_FAILED;
    }

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
        return false;
    }

    bool reduce_quantifier(quantifier * old_q, expr * new_body, expr * const * new_patterns, expr * const * new_no_patterns, expr_ref & result, proof_ref & result_pr) {
        return false;
    }
};

struct funccalls_rewriter : public rewriter_tpl<funccalls_rw_cfg> {
    funccalls_rw_cfg m_cfg;
    funccalls_rewriter(ast_manager & m, params_ref const & p, ufbv_templatation::templates_t & t, ufbv_templatation::calls_t & c) :
        rewriter_tpl<funccalls_rw_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p, t, c) {
    }
};

void ufbv_templatation::replace_calls_w_cnsts() {
    // For each function call, introduce a new call constant, i.e.,
    // for (g (f x y)) turns into cc1, plus additional constraints
    // (= cc1 (g cc2)) and (= cc2 (f x y)).

    funccalls_rewriter fcr(m, m_params, m_templates, m_calls);
    for (unsigned i = 0; i < m_goal.size(); i++) {
        expr_ref t(m);
        fcr(m_goal.form(i), t);
        m_goal.update(i, t);
    }
}

void ufbv_templatation::instantiate_tmplts() {
    for (calls_t::iterator it = m_calls.begin();
         it != m_calls.end();
         it++) {
        app_ref fc(m); expr_ref cc(m);
        fc = it->m_key; cc = it->m_value;

        func_decl_ref fd(fc->get_decl(), m);
        SASSERT(m_templates.contains(fd));

        expr_ref t(m);
        t = m_templates.find(fd);

        TRACE("ufbv_templatation",
            tout << "Instantiating function call: " <<
            "(= " << mk_ismt2_pp(cc, m) << " " << mk_ismt2_pp(fc, m) << ")" <<
            " w/ template (= " << fd->get_name() << " " << mk_ismt2_pp(t, m) << ")" << std::endl;);

        // unsigned arity = fd->get_arity();

        expr_ref t_i(t, m); // TODO: instantiate
        expr_ref cc_eq_t_i(m.mk_eq(cc, t_i), m);
        blast(cc_eq_t_i);
    }
}

void ufbv_templatation::display_trace() {
    TRACE("ufbv_templatation",
        tout << "Assertions:" << std::endl;
        for (unsigned i = 0; i < m_goal.size(); i++)
             tout << mk_ismt2_pp(m_goal.form(i), m) << std::endl;
        tout << "Calls:" << std::endl;
        for (calls_t::iterator it = m_calls.begin();
             it != m_calls.end();
            it++)
            tout << mk_ismt2_pp(it->m_key, m) << " := " << mk_ismt2_pp(it->m_value, m) << std::endl;
        tout << "Templates:" << std::endl;
        for (templates_t::iterator it = m_templates.begin();
             it != m_templates.end();
             it++)
            tout << mk_ismt2_pp(it->m_key, m) << " := " << mk_ismt2_pp(it->m_value, m) << std::endl;
        );
}

void ufbv_templatation::blast(expr * e) {
    expr_ref t(m);
    proof_ref tp(m);
    m_bit_blaster(e, t, tp);
    goal g(m, true, true);
    g.assert_expr(t);
    m_goal2sat(g, m_params, m_sat_solver, m_atom2bool, m_dep2asm);
}

lbool ufbv_templatation::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    if (num_assumptions != 0)
        throw tactic_exception("UFBV templatation does not support assumptions yet.");

    init_proc iproc(m, m_bv_util, m_templates);
    expr_mark visited;
    unsigned sz = m_goal.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * e = m_goal.form(i);
        for_each_expr(iproc, visited, e);
    }

    if (iproc.m_has_quantifiers)
        throw tactic_exception("UFBV templatation does not support quantifiers yet.");

    replace_calls_w_cnsts();
    display_trace();

    for (unsigned i = 0; i < m_goal.size(); i++)
        blast(m_goal.form(i));

    TRACE("ufbv_templatation_verbose", m_sat_solver.display(tout); );
    TRACE("ufbv_templatation_verbose", m_atom2bool.display(tout); );

    // From here on, m_assertions does not contain function calls,
    // only BV and perhaps (in future) universal quantifiers.

    unsigned itrtn = 0;
    for (bool is_solved = false; !is_solved; ) {
        instantiate_tmplts();

        unsigned num_sat_assumptions = 0;
        sat::literal const * sat_assumptions = 0;
        lbool i_res = m_sat_solver.check(num_sat_assumptions, sat_assumptions);
        TRACE("ufbv_templatation", tout << "itrtn " << itrtn << ": " << i_res << std::endl;);

        switch (i_res) {
        case l_true:
            // Functions found; build model.
            break;
        case l_false:
            // No such functions; refine templates.
            break;
        case l_undef:
            // Problem, pass it on.
            return l_undef;
        }

        return l_undef;
        NOT_IMPLEMENTED_YET();

        itrtn++;
    }

    return l_undef;
}
