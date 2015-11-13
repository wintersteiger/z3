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


class ufbv_templatation::function_template {
    ast_manager    & m;
    bv_util          m_util;
    func_decl_ref    m_fd;
    expr_ref_vector  m_terms;
    unsigned         m_degree;
    var_ref_vector   m_vars;

public:
    function_template(ast_manager & m, func_decl * fd) :
        m(m),
        m_util(m),
        m_terms(m),
        m_fd(fd, m),
        m_vars(m) {
        // Initial templates are just constants
        m_terms.push_back(m.mk_fresh_const(0, fd->get_range()));
        m_degree = 0;
        for (unsigned i = 0; i < fd->get_arity(); i++)
            m_vars.push_back(m.mk_var(i, fd->get_domain()[i]));
    }

    ~function_template() {}

    expr_ref get_expr() {
        expr_ref res(m);
        res = m_terms.get(0);
        for (unsigned i = 1; i < m_terms.size(); i++)
            res = m_util.mk_bv_add(res, m_terms.get(i));
        return res;
    }

    expr_ref instantiate(app * call) {
        SASSERT(m_terms.size() > 0);
        SASSERT(call->get_decl()->get_family_id() == null_family_id);
        SASSERT(m_vars.size() == call->get_num_args());

        expr_substitution es(m);
        for (unsigned i = 0; i < m_vars.size(); i++)
            es.insert(m_vars.get(i), call->get_arg(i));

        expr_ref res(get_expr(), m);

        TRACE("ufbv_templatation",
            tout << "Instantiating function call: " <<
                "(= " << mk_ismt2_pp(call, m) << ")" <<
                " w/ template (= " << call->get_decl()->get_name() << " " <<
                mk_ismt2_pp(res, m) << ")" << std::endl;);

        return res;
    }

    void refine() {
    }

    void display(std::ofstream & out) const {
        out << mk_ismt2_pp(m_terms.get(0), m);
        for (unsigned i = 1; i < m_terms.size(); i++)
            out << std::endl << mk_ismt2_pp(m_terms.get(i), m);
    }
};


ufbv_templatation::ufbv_templatation(ast_manager & m, params_ref const & p) :
    m(m),
    m_params(p),
    m_bv_util(m),
    m_goal(m),
    m_simplifier(m),
    m_bit_blaster(m, p),
    m_sat_solver(p, m.limit(), 0),
    m_atom2bool(m) {
}

ufbv_templatation::~ufbv_templatation() {
    for (templates_t::iterator it = m_templates.begin();
         it != m_templates.end();
         it++)
        dealloc(it->m_value);

    for (calls_t::iterator it = m_calls.begin();
         it != m_calls.end();
         it++)
        m.dec_ref(it->m_value);

    for (obj_map<expr, expr*>::iterator it = m_core_labels.begin();
         it != m_core_labels.end();
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
            ufbv_templatation::function_template * ft =
                alloc(ufbv_templatation::function_template, m, fd);
            m_templates.insert(fd, ft);
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

        ufbv_templatation::function_template * ft;
        bool fnd = m_templates.find(fd, ft);
        SASSERT(fnd);

        expr_ref t_i(m);
        t_i = ft->instantiate(fc);
        expr_ref cc_eq_t_i(m.mk_eq(cc, t_i), m);
        expr_ref lbl(m), impl(m);
        lbl = m.mk_fresh_const(0, m.mk_bool_sort());
        impl = m.mk_implies(lbl, cc_eq_t_i);
        blast(impl);

        expr_ref actual_call(m);
        actual_call = m.mk_eq(cc, fc);
        m_core_labels.insert(lbl, actual_call);
        m.inc_ref(actual_call);
        expr2var::var lbl_var = m_atom2bool.to_var(lbl);
        SASSERT(lbl_var != UINT_MAX);
        m_core_literals.push_back(sat::literal(lbl_var, false));
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
             it++) {
            tout << mk_ismt2_pp(it->m_key, m) << " := ";
            it->m_value->display(tout);
            tout << std::endl;
        });
}

void ufbv_templatation::blast(expr * e) {
    expr_ref t(e, m);
    proof_ref tp(0, m);
    m_simplifier(t, t);
    m_bit_blaster(t, t, tp);
    goal g(m, false, true, true);
    g.assert_expr(t);
    m_goal2sat(g, m_params, m_sat_solver, m_atom2bool, m_dep2asm, true);
}

model_ref ufbv_templatation::get_bv_model() {
    model_ref res = alloc(model, m);
    sat::model const & ll_m = m_sat_solver.get_model();
    atom2bool_var::iterator it = m_atom2bool.begin();
    atom2bool_var::iterator end = m_atom2bool.end();
    for (; it != end; ++it) {
        expr * n = it->m_key;
        sat::bool_var v = it->m_value;
        if (is_app(n) && to_app(n)->get_decl()->get_arity() != 0)
            continue;
        switch (sat::value_at(v, ll_m)) {
        case l_true: res->register_decl(to_app(n)->get_decl(), m.mk_true()); break;
        case l_false: res->register_decl(to_app(n)->get_decl(), m.mk_false()); break;
        default:
            break;
        }
    }
    sat::model mdl = m_sat_solver.get_model();
    model_converter_ref bb_mc = mk_bit_blaster_model_converter(m, m_bit_blaster.const2bits());
    bb_mc->operator()(res, 0);
    return res;
}

expr_ref_vector ufbv_templatation::get_bv_core() {
    expr_ref_vector res(m);
    sat::literal_vector core = m_sat_solver.get_core();
    for (unsigned i = 0; i < core.size(); i++) {
        sat::literal l = core[i];
        unsigned v = l.var();
        expr * e_tm = 0;
        for (atom2bool_var::iterator it = m_atom2bool.begin();
             it != m_atom2bool.end() && e_tm == 0;
             it++) {
            if (it->m_value == v)
                e_tm = it->m_key;
        }

        expr * feq;
        SASSERT(e_tm != 0);
        bool check = m_core_labels.find(e_tm, feq);
        SASSERT(check && m.is_eq(feq));
        SASSERT(to_app(feq)->get_num_args() >= 2);
        res.push_back(to_app(feq)->get_arg(1));
    }

    return res;
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

        lbool i_res = m_sat_solver.check(m_core_literals.size(), m_core_literals.c_ptr());
        TRACE("ufbv_templatation", tout << "itrtn " << itrtn << ": " << i_res << std::endl;);

        switch (i_res) {
        case l_true: {
            // Functions found; build model.
            model_ref mdl = get_bv_model();
            TRACE("ufbv_templatation",
                    tout << "Model: " << std::endl;
                    for (templates_t::iterator it = m_templates.begin();
                         it != m_templates.end();
                         it++) {
                        expr_ref f(m);
                        mdl->eval(it->m_value->get_expr(), f, true);
                        tout << mk_ismt2_pp(it->m_key, m) << " := " << mk_ismt2_pp(f, m) << std::endl;
                    });
            return l_true;
            break;
        }
        case l_false: {
            // No such functions; refine templates.
            expr_ref_vector core = get_bv_core();
            TRACE("ufbv_templatation",
                tout << "Core (function calls):" << std::endl;
                for (unsigned i = 0; i < core.size(); i++)
                    tout << mk_ismt2_pp(core.get(i), m) << std::endl;
                );
            NOT_IMPLEMENTED_YET();
            break;
        }
        case l_undef:
            // Problem; pass it on.
            return l_undef;
        }

        itrtn++;
    }

    return l_undef;
}
