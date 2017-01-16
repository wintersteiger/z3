/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    async_cmds.cpp

Abstract:

    Asynchronous commands

Author:

    Christoph (cwinter) 2017-01-16

Notes :

--*/
#include<thread>

#include"z3_omp.h"
#include"rlimit.h"
#include"cancel_eh.h"
#include"scoped_ctrl_c.h"
#include"scoped_timer.h"
#include"cmd_context.h"
#include"solver.h"
#include"ast_translation.h"
#include"gparams.h"
#include"solver_na2as.h"

#include"async_cmds.h"

class async_worker : public std::thread {
public:
    cmd_context & m_context;
    ast_manager m_manager;
    solver * m_solver;
    expr_ref_vector m_assumptions;

    async_worker(cmd_context & ctx) :
        std::thread(),
        m_context(ctx),
        m_manager(ctx.get_ast_manager(), false),
        m_solver(0),
        m_assumptions(ctx.get_ast_manager()) {
        solver_factory & sf = ctx.get_solver_factory();
        m_solver = sf(m_manager, params_ref(), // params necessary?
                    ctx.produce_proofs(), ctx.produce_models(), ctx.produce_unsat_cores(),
                    ctx.get_logic());
        m_solver->updt_params(gparams::get());
        solver_na2as * from_slvr = (solver_na2as*)(&ctx.get_solver());
        ast_translation translate(ctx.get_ast_manager(), m_manager, true);
        unsigned sz = from_slvr->get_num_assertions();
        for (unsigned i = 0; i < sz; i++)
            m_solver->assert_expr(translate(from_slvr->get_assertion(i)));
        sz = from_slvr->get_num_assumptions();
        for (unsigned i = 0; i < sz; i++)
            m_assumptions.push_back(translate(from_slvr->get_assumption(i)));
        // m_solver->display(std::cout);
    }

    ~async_worker() {
        if (m_solver) dealloc(m_solver);
    }

    void start() {
        (*(std::thread*)this) = (std::thread(&async_worker::work, this));
    }

    void work() {
        IF_IVERBOSE(9, verbose_stream() << "(smt.async.start :tid " <<
            std::this_thread::get_id() << ")" << std::endl; );

        unsigned timeout = m_context.params().m_timeout;
        unsigned rlimit = m_context.params().m_rlimit;
        cmd_context::scoped_watch sw(m_context);
        lbool r;

        m_solver->set_progress_callback(0); // &ctx?
        cancel_eh<reslimit> eh(m_manager.limit());
        scoped_timer timer(timeout, &eh);
        scoped_rlimit _rlimit(m_manager.limit(), rlimit);
        try {
            r = m_solver->check_sat(m_assumptions.size(), m_assumptions.c_ptr());
        }
        catch (z3_exception & ex) {
            m_solver->set_reason_unknown(ex.msg());
            r = l_undef;
        }

        m_solver->set_status(r);

        IF_IVERBOSE(9, verbose_stream() << "(smt.async.stop :tid " <<
            std::this_thread::get_id() << ")" << std::endl; );
    }
};

class check_sat_async_cmd : public cmd {
public:
    check_sat_async_cmd() : cmd("check-sat-async") {}
    virtual char const * get_usage() const { return "()"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "start an asynchronous query"; }
    virtual unsigned get_arity() const { return 0; }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
        if (!ctx.has_solver())
            throw cmd_exception("No solver associated with command context");

#ifdef _NO_OMP_
        throw cmd_exception("Z3 has been compiled without support for OpenMP; command not available.");
#else
        async_worker * wrkr = alloc(async_worker, ctx);
        ctx.async_start(wrkr);
        wrkr->start();
#endif
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) { }
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};

class async_cancel_eh : public event_handler {
    cmd_context & m_ctx;
public:
    async_cancel_eh(cmd_context & ctx) : m_ctx(ctx) { }

    virtual void operator()() {
        for (unsigned i = 0; i < m_ctx.async_num_queries(); i++) {
            async_worker * w = static_cast<async_worker*>(m_ctx.get(i));
            w->m_solver->get_manager().limit().cancel();
        }

        m_ctx.async_reset();
    }
};

class await_cmd : public cmd {
public:
    await_cmd() : cmd("await") {}
    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "await the completion of asynchronous queries"; }
    virtual unsigned get_arity() const { return 0; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_UINT; }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
#ifdef _NO_OMP_
        throw cmd_exception("Z3 has been compiled without support for OpenMP; command not available.");
#else
        ast_manager & m = ctx.get_ast_manager();

        async_cancel_eh eh(ctx);
        scoped_ctrl_c ctrlc(eh);
        unsigned num_queries = ctx.async_await();
        IF_IVERBOSE(9, verbose_stream() << "(smt.async.awaited :num-queries " << num_queries << ")" << std::endl; );

        statistics stats; // TODO

        for (unsigned i = 0; i < num_queries; i++) {
            async_worker * w = static_cast<async_worker*>(ctx.async_get(i));
            ast_translation translate(w->m_manager, m, false);
            check_sat_result * fr = w->m_solver;
            ctx.display_sat_result(fr->status());
            w->m_solver->collect_statistics(stats);
        }
#endif
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) {}
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};

class choose_async_cmd : public cmd {
    unsigned m_inx;
public:
    choose_async_cmd() : cmd("choose-async") {}
    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "selects an asynchronously computed result"; }
    virtual unsigned get_arity() const { return 1; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_UINT; }
    virtual void set_next_arg(cmd_context & ctx, unsigned val) { m_inx = val;  }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
#ifdef _NO_OMP_
        throw cmd_exception("Z3 has been compiled without support for OpenMP; command not available.");
#else
        if (ctx.async_in_progress())
            throw cmd_exception("Asynchronous queries in progress; await results before using choose-async");

        if (m_inx >= ctx.async_num_queries())
            throw cmd_exception("Result index out of bounds");

        ast_manager & m = ctx.get_ast_manager();
        async_worker * w = static_cast<async_worker*>(ctx.async_get(m_inx));
        if (!w) throw cmd_exception("result unavailable (no worker)");

        ast_translation translate(w->m_manager, m, false);
        check_sat_result * fr = w->m_solver;
        simple_check_sat_result * r = alloc(simple_check_sat_result, m);
        r->set_status(fr->status());
        switch (fr->status()) {
        case l_true: {
            model_ref tm;
            fr->get_model(tm);
            r->m_model = tm->translate(translate);
            break;
        }
        case l_false: {
            r->m_core.reset();
            expr_ref_vector core(w->m_manager);
            fr->get_unsat_core(core);
            for (unsigned i = 0; i < core.size(); i++)
                r->m_core.push_back(translate(core.get(i)));
            proof * fp = fr->get_proof();
            if (fp)
                r->m_proof = translate(fp);
            break;
        }
        case l_undef:
            r->set_reason_unknown(fr->reason_unknown().c_str());
            break;
        default:;
        }

        ctx.set_check_sat_result(r);
#endif
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) { m_inx = 0; }
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};

class cancel_async_cmd : public cmd {
public:
    cancel_async_cmd() : cmd("cancel-async") {}
    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "aborts asynchronous queries"; }
    virtual unsigned get_arity() const { return 0; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_UINT; }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
#ifdef _NO_OMP_
        throw cmd_exception("Z3 has been compiled without support for OpenMP; command not available.");
#else
        (async_cancel_eh(ctx))();
#endif
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) {}
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};

class cancel_async_cmd : public cmd {
public:
    cancel_async_cmd() : cmd("cancel-async") {}
    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "aborts asynchronous queries"; }
    virtual unsigned get_arity() const { return 0; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_UINT; }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
#ifdef _NO_OMP_
        throw cmd_exception("Z3 has been compiled without support for OpenMP; command not available.");
#else
        (async_cancel_eh(ctx))();
#endif
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) {}
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};


void install_async_cmds(cmd_context & ctx) {
    ctx.insert(alloc(check_sat_async_cmd));
    ctx.insert(alloc(await_cmd));
    ctx.insert(alloc(get_model_async_cmd));
    ctx.insert(alloc(get_proof_async_cmd));
    ctx.insert(alloc(get_unsat_core_async_cmd));
}
