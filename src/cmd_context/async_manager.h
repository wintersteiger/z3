/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    async_manager.h

Abstract:

    Asynchronous manager for cmd_context.

Author:

    Christoph (cwinter) 2017-01-16

Notes :

--*/
#ifndef ASYNC_MANAGER_H_
#define ASYNC_MANAGER_H_

#include<thread>

#include"map.h"
#include"solver.h"
#include"check_sat_result.h"

class async_manager {
    bool m_in_progress;
    vector<std::thread*> m_threads;

public:
    async_manager();
    ~async_manager();

    void async_start(std::thread * t);
    unsigned async_await();
    void async_reset();
    bool async_in_progress() const { return m_in_progress; }
    unsigned async_num_queries() const { return m_in_progress ? 0 : m_threads.size(); }
    std::thread * async_get(unsigned i) const { return m_threads[i]; }
};

#endif
