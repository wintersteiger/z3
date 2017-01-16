/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    async_cmds.h

Abstract:

    Asynchronous commands

Author:

    Christoph (cwinter) 2017-01-16

Notes:

--*/
#ifndef ASYNC_CMDS_H_
#define ASYNC_CMDS_H_

class cmd_context;

void install_async_cmds(cmd_context & ctx);

#endif /* ASYNC_CMDS_H_ */
