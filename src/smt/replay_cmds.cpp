/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    replay_cmds.h

Abstract:
    Custom SMT2 commands for replaying search logs.

Author:

    Christoph (cwinter) 2017-05-01

Notes:

--*/
#include<fstream>

#include"smt2parser.h"
#include"cmd_context.h"
#include"gparams.h"
#include"func_decl_dependencies.h"
#include"for_each_expr.h"
#include"smt_solver.h"
#include"solver_na2as.h"
#include"replay_cmds.h"

class nasty_hack : public cmd_context {
public:
    ref<solver> const & get_solver() const { return m_solver; }
    void set_solver(ref<solver> & s) { m_solver = s; }
    unsigned get_num_assumptions() const { static_cast<solver_na2as*>(m_solver.get())->get_num_assumptions(); }
    expr * get_assumption(unsigned i) { static_cast<solver_na2as*>(m_solver.get())->get_assumption(i); }
};

class add_instance_cmd : public cmd {
    expr *     m_instance;
    params_ref m_params;
public:
    add_instance_cmd() : cmd("add-instance"), m_instance(0) { }
    virtual char const * get_usage() const { return "<term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "add a quantifier instance"; }
    virtual unsigned get_arity() const { return 1; }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_EXPR; }

    virtual void set_next_arg(cmd_context & ctx, expr * i) {
        SASSERT(m_instance == 0);
        ast_manager & m = ctx.m();
        m.inc_ref(i);
        m_instance = i;
    }

    virtual void failure_cleanup(cmd_context & ctx) {}

    virtual void execute(cmd_context & ctx) {
        IF_VERBOSE(11, verbose_stream() << "(smt.replay.add_instance)" << std::endl; );
        ast_manager & m = ctx.m();

        nasty_hack * hacked_ctx = reinterpret_cast<nasty_hack*>(&ctx);
        ref<solver> slvr = hacked_ctx->get_solver();
        SASSERT(slvr);

        try {
            expr_ref i(m_instance, m);

            unsigned lim = m_params.get_uint("qi.max_instances", 0);
            m_params.set_uint("qi.max_instances", lim + 1);
            slvr->updt_params(m_params);

            if (!slvr->add_quantifier_instance(i)) {
                std::stringstream ss("");
                ss << mk_ismt2_pp(m_instance, m);
                // IF_VERBOSE(12, warning_msg("Redundant quantifier instance: %s", ss.str().c_str()); );
                IF_VERBOSE(12, warning_msg("(Redundant quantifier instance)"););
            }
        }
        catch (default_exception & ex) {
            std::stringstream ss("");
            ss << mk_ismt2_pp(m_instance, m);
            warning_msg("Exception: '%s'; ignored: %s", ex.msg(), ss.str().c_str());
        }

    }

    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) {
        if (m_instance)
            ctx.m().dec_ref(m_instance);
        m_instance = 0;
    }
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};


class decide_cmd : public cmd {
    expr * m_decision;
    bool   m_ignore;
    bool   m_ignore_lemmas;

public:
    decide_cmd(bool ignore, bool ignore_lemmas) :
        cmd("decide"), m_decision(0), m_ignore(ignore), m_ignore_lemmas(ignore_lemmas) {}
    virtual char const * get_usage() const { return "<term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "add a decision"; }
    virtual unsigned get_arity() const { return 1; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_EXPR; }

    virtual void set_next_arg(cmd_context & ctx, expr * e) {
        SASSERT(m_decision == 0);
        ast_manager & m = ctx.m();
        m.inc_ref(e);
        m_decision = e;
    }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
        IF_VERBOSE(11, verbose_stream() << "(smt.replay.decide)" << std::endl; );
        ast_manager & m = ctx.m();
        nasty_hack * hacked_ctx = reinterpret_cast<nasty_hack*>(&ctx);
        ref<solver> slvr = hacked_ctx->get_solver();
        SASSERT(slvr);

        if (!m_ignore || !m_ignore_lemmas) {
            // Decisions include 1 push, so that the assertion will be
            // backtracked if it's wrong (at the next lemma cmd).
            ctx.push();
        }

        if (!m_ignore) {
            slvr->assert_expr(m_decision);
        }
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context& ctx) {
        if (m_decision)
            ctx.m().dec_ref(m_decision);
        m_decision = 0;
    }
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};


class lemma_cmd : public cmd {
    expr       * m_lemma;
    unsigned     m_levels;
    bool         m_ignore;
    bool         m_ignore_decisions;

public:
    lemma_cmd(bool ignore, bool ignore_decisions) :
        cmd("lemma"), m_lemma(0), m_levels(UINT_MAX), m_ignore(ignore), m_ignore_decisions(ignore_decisions) { }
    virtual char const * get_usage() const { return "<number> <term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "backtrack <number> levels and add a (checked) lemma"; }
    virtual unsigned get_arity() const { return 2; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return m_levels == UINT_MAX ? CPK_UINT : CPK_EXPR; }

    virtual void set_next_arg(cmd_context & ctx, unsigned val) {
        SASSERT(m_lemma == 0);
        SASSERT(m_levels == UINT_MAX);
        m_levels = val;
    }

    virtual void set_next_arg(cmd_context & ctx, expr * e) {
        SASSERT(m_lemma == 0);
        ast_manager & m = ctx.m();
        m.inc_ref(e);
        m_lemma = e;
    }

    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
        IF_VERBOSE(11, verbose_stream() << "(smt.replay.lemma)" << std::endl; );
        ast_manager & m = ctx.m();
        nasty_hack * hacked_ctx = reinterpret_cast<nasty_hack*>(&ctx);
        ref<solver> slvr = hacked_ctx->get_solver();
        SASSERT(slvr);
        SASSERT(m_lemma);

        if (m_ignore) {
            if (!m_ignore_decisions)
                slvr->pop(m_levels);
        }
        else {
            expr_ref not_lemma(m.mk_not(m_lemma), m);
            slvr->push();
            slvr->assert_expr(not_lemma);

            lbool s = slvr->check_sat(0, 0);

            slvr->pop(m_levels + 1);
            // TODO: Check that lemma depends on things on the current level?

            DEBUG_CODE({
                statistics st;
                slvr->collect_statistics(st);
                TRACE("replay_stats", st.display(tout); );
            });

            switch (s) {
            case l_false: {
                slvr->assert_expr(m_lemma);
                break;
            }
            case l_true: {
                std::stringstream strs;
                strs << mk_ismt2_pp(m_lemma, m);
                warning_msg("ignoring erroneous lemma: %s", strs.str().c_str());
                break;
            }
            case l_undef:
            default: {
                std::stringstream strs;
                strs << mk_ismt2_pp(m_lemma, m);
                warning_msg("could not prove lemma: %s %s", strs.str().c_str(), slvr->reason_unknown().c_str());
                break;
            }
            }
        }
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) {
        m_levels = UINT_MAX;
        if (m_lemma)
            ctx.m().dec_ref(m_lemma);
        m_lemma = 0;
    }
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};


class replay_cmd : public cmd {
    add_instance_cmd * m_add_instance_cmd;
    decide_cmd *       m_decide_cmd;
    lemma_cmd *        m_lemma_cmd;
    std::string        m_log_filename;

    bool               m_global_decls_before;
    context_params     m_ctx_params_before;
    std::string        m_auto_config_before;
    std::string        m_mbqi_before;
    std::string        m_ematching_before;

public:
    replay_cmd() : cmd("replay"), m_log_filename("") {}
    virtual char const * get_usage() const { return "<filename>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "replay a search log file"; }
    virtual unsigned get_arity() const { return 1; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_STRING; }
    virtual void set_next_arg(cmd_context & ctx, char const * val) { m_log_filename = val; }
    virtual void failure_cleanup(cmd_context & ctx) {}

protected:
    static cmd_context * m_tmp_ctx;

    static void new_func_decl_eh(func_decl * fd) {
        symbol const & name = fd->get_name();
        if (!m_tmp_ctx->is_func_decl(name) && !m_tmp_ctx->is_macro(name)) {
            // std::cout << "Post-inserting " << fd->get_name() << std::endl;
            m_tmp_ctx->insert(fd);
        }
    }

    static void erase_func_decl_eh(func_decl * fd) {
        m_tmp_ctx->erase_func_decl(fd);
    }

    void inject_func_decls(ast_manager & m, cmd_context & ctx) {
        // CMW: We'd want a faster way to do this.
        ast_table::iterator it = m.begin_asts();
        ast_table::iterator end = m.end_asts();
        for (; it != end; it++) {
            if (is_func_decl(*it)) {
                func_decl * fd = to_func_decl(*it);
                symbol const & name = fd->get_name();
                if (!ctx.is_func_decl(name) && !ctx.is_macro(name)) {
                    // std::cout << "Pre-inserting " << fd->get_name() << std::endl;
                    ctx.insert(fd);
                }
            }
        }
    }

    void setup_env(cmd_context & ctx) {
        bool ignore_decisions = gparams::get_value("smt.search_log.replay.ignore_decisions") == "true";
        bool ignore_lemmas = gparams::get_value("smt.search_log.replay.ignore_lemmas") == "true";

        ctx.m().new_func_decl_eh = &new_func_decl_eh;
        ctx.m().erase_func_decl_eh = &erase_func_decl_eh;

        ctx.insert(m_add_instance_cmd = alloc(add_instance_cmd));
        ctx.insert(m_decide_cmd = alloc(decide_cmd, ignore_decisions, ignore_lemmas));
        ctx.insert(m_lemma_cmd = alloc(lemma_cmd, ignore_lemmas, ignore_decisions));

        m_ctx_params_before = ctx.params();
        m_global_decls_before = ctx.global_decls();
        m_auto_config_before = gparams::get_value("auto-config");
        m_mbqi_before = gparams::get_value("smt.mbqi");
        m_ematching_before = gparams::get_value("smt.ematching");

        gparams::set("auto-config", "false");
        gparams::set("smt.mbqi", "false");
        gparams::set("smt.ematching", "false");

        ctx.set_global_decls_unsafe(true);
        ctx.global_params_updated();
    }

    void restore_env(cmd_context & ctx) {
        ctx.erase_cmd(m_add_instance_cmd->get_name());
        ctx.erase_cmd(m_decide_cmd->get_name());
        ctx.erase_cmd(m_lemma_cmd->get_name());

        ctx.m().new_func_decl_eh = 0;
        ctx.m().erase_func_decl_eh = 0;

        gparams::set("auto-config", m_auto_config_before.c_str());
        gparams::set("smt.mbqi", m_mbqi_before.c_str());
        gparams::set("smt.ematching", m_ematching_before.c_str());

        ctx.params() = m_ctx_params_before;
        ctx.set_global_decls_unsafe(m_global_decls_before);
    }

public:
    virtual void execute(cmd_context & ctx) {
        SASSERT(m_log_filename.compare("") != 0);
        m_tmp_ctx = &ctx;

        IF_VERBOSE(10, verbose_stream() << "(smt.replay \"" << m_log_filename << "\")" << std::endl; );

        TRACE("replay",
            expr * const * it = ctx.begin_assertions();
            expr * const * end = ctx.end_assertions();
            for (; it != end; it++)
                tout << mk_ismt2_pp(*it, ctx.m()) << std::endl;
        );

        setup_env(ctx);
        inject_func_decls(ctx.m(), ctx);

        nasty_hack * hacked_ctx = reinterpret_cast<nasty_hack*>(&ctx);
        ref<solver> slvr = hacked_ctx->get_solver();
        SASSERT(slvr);

        slvr->push(); // forces internalization

        std::ifstream strm(m_log_filename.c_str());
        if (!strm.is_open())
            warning_msg("error opening search log file '%s', proceeding without log.", m_log_filename.c_str());
        else {
            parse_smt2_commands(ctx, strm, false, gparams::get(), m_log_filename.c_str());
            strm.close();
        }

        restore_env(ctx);
        slvr->pop(1);

        ctx.set_check_sat_result(slvr.get());

        IF_VERBOSE(10, verbose_stream() << "(smt.end-of-replay)" << std::endl; );
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context& ctx) { m_log_filename = ""; }
    virtual void finalize(cmd_context & ctx) {}
};

cmd_context * replay_cmd::m_tmp_ctx = 0;

void install_replay_cmds(cmd_context & ctx) {
    ctx.insert(alloc(replay_cmd));
}
