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
#ifndef REPLAY_CMDS_H_
#define REPLAY_CMDS_H_

class cmd_context;

void install_replay_cmds(cmd_context & ctx);

#endif
