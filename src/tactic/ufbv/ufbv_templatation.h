/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ufbv_templatation.h

Abstract:

    CEGAR loop for automatic function template refinement in UFBV formulas.

Author:

    Christoph (cwinter) 2015-11-06

Notes:

--*/
#ifndef UFBV_TEMPLATATION_H_
#define UFBV_TEMPLATATION_H_

#include"ast.h"
#include"obj_hashtable.h"
#include"bit_blaster_rewriter.h"
#include"bit_blaster_model_converter.h"
#include"sat_solver.h"
#include"check_sat_result.h"
#include"bv_decl_plugin.h"
#include"goal2sat.h"

class ufbv_templatation : public check_sat_result {
public:
    typedef obj_map<func_decl, expr*> templates_t;
    typedef obj_map<app, app*> calls_t;

protected:
    ast_manager      & m;
    params_ref         m_params;
    bv_util            m_bv_util;
    goal               m_goal;

    templates_t        m_templates;
    calls_t            m_calls;

    bit_blaster_rewriter m_bit_blaster;
    sat::solver        m_sat_solver;
    goal2sat           m_goal2sat;
    atom2bool_var      m_atom2bool;
    obj_map<expr, sat::literal> m_dep2asm;

public:
    ufbv_templatation(ast_manager & m, params_ref const & p);
    ~ufbv_templatation();

    void add(expr * a);

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions);

    virtual void collect_statistics(statistics & st) const { NOT_IMPLEMENTED_YET(); }
    virtual void get_unsat_core(ptr_vector<expr> & r) { NOT_IMPLEMENTED_YET(); }
    virtual void get_model(model_ref & m) { NOT_IMPLEMENTED_YET(); }
    virtual proof * get_proof() { NOT_IMPLEMENTED_YET(); }
    virtual std::string reason_unknown() const { NOT_IMPLEMENTED_YET(); }
    virtual void get_labels(svector<symbol> & r) { NOT_IMPLEMENTED_YET(); }

protected:
    void blast(expr * e);
    void replace_calls_w_cnsts();
    void instantiate_tmplts();
    void display_trace();
};

#endif