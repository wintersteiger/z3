/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    async_manager.cpp

Abstract:

    Asynchronous manager for cmd_context.

Author:

    Christoph (cwinter) 2017-01-16

Notes :

--*/
#include<thread>
#include<mutex>
#include"z3_omp.h"
#include"async_manager.h"

async_manager::async_manager() :
    m_in_progress(false) {
}

async_manager::~async_manager() {
    async_reset();
}

void async_manager::async_start(std::thread * t) {
    m_in_progress = true;
    m_threads.push_back(t);
}

unsigned async_manager::async_await() {
    unsigned num = m_threads.size();
    for (unsigned i = 0; i < num; i++) {
        std::thread * t = m_threads[i];
        if (t && t->joinable())
            t->join();
    }
    m_in_progress = false;
    return num;
}

void async_manager::async_reset() {
    for (unsigned i = 0; i < m_threads.size(); i++) {
        if (m_threads[i]) {
            if (m_threads[i]->joinable()) m_threads[i]->join();
            dealloc(m_threads[i]);
            m_threads[i] = 0;
        }
    }
    m_threads.reset();
}
