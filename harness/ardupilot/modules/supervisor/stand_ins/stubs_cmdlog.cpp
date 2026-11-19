// stubs_cmdlog.cpp: the tick's command log the generated command stand-ins write into, and the
// abort for queries no stand-in answers (supervisor_shadow.h).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "supervisor_shadow.h"

SupCmd sup_cmd_log[SUP_CMD_LOG_MAX];
uint32_t sup_cmd_count;
uint32_t sup_cmd_overflow;
static SupCmd *cur;

void sup_cmd_begin(uint32_t id)
{
    if (sup_cmd_count < SUP_CMD_LOG_MAX) {
        cur = &sup_cmd_log[sup_cmd_count++];
        cur->id = id;
        cur->nargs = 0;
    } else {
        cur = nullptr;
        sup_cmd_overflow++;
    }
}

void sup_cmd_word(uint32_t w, bool is_float)
{
    if (cur != nullptr && cur->nargs < SUP_CMD_MAX_ARGS) {
        cur->arg_is_float[cur->nargs] = is_float;
        cur->arg[cur->nargs++] = w;
    }
}

void sup_cmd_end()
{
    cur = nullptr;
}

void sup_unanswered(const char *method)
{
    fprintf(stderr, "supervisor: no stand-in answers %s (a query or a command with a result)\n",
            method);
    abort();
}

// the method names of the command ids (generated and hand-written)
struct SupCmdName {
    uint32_t id;
    const char *stage;
    const char *method;
};
static const SupCmdName sup_cmd_names[] = {
#include "cmd_table.inc"
    SUP_CMD_HAND_TABLE
};

static const char *named_methods[256];
static const char *named_stages[256];
static uint32_t nnamed;

uint32_t sup_named_id(const char *method, const char *stage)
{
    for (uint32_t k = 0; k < nnamed; k++) {
        if (strcmp(named_methods[k], method) == 0) {
            return 2000 + k;
        }
    }
    if (nnamed == 256) {
        sup_unanswered("sup_named_id: more than 256 named commands");
    }
    named_methods[nnamed] = method;
    named_stages[nnamed] = stage;
    return 2000 + nnamed++;
}

const char *sup_cmd_method(uint32_t id, const char **stage)
{
    if (id >= 2000 && id < 2000 + nnamed) {
        if (stage != nullptr) {
            *stage = named_stages[id - 2000];
        }
        return named_methods[id - 2000];
    }
    for (const SupCmdName &c : sup_cmd_names) {
        if (c.id == id) {
            if (stage != nullptr) {
                *stage = c.stage;
            }
            return c.method;
        }
    }
    return nullptr;
}

bool sup_cmd_called(const char *method)
{
    for (uint32_t k = 0; k < sup_cmd_count; k++) {
        const char *m = sup_cmd_method(sup_cmd_log[k].id, nullptr);
        if (m != nullptr && strcmp(m, method) == 0) {
            return true;
        }
    }
    return false;
}

uint32_t sup_unanswered_count;

bool sup_strict()
{
    static int strict = -1;
    if (strict < 0) {
        strict = getenv("SUP_STRICT") != nullptr ? 1 : 0;
    }
    return strict == 1;
}

// not strict (the default, and every campaign): an unanswered query returns its type's zero and
// is counted in `unanswered` (guaranteed 0); SUP_STRICT=1: it aborts (sup_unanswered)
bool sup_lenient(const char *method)
{
    if (sup_strict()) {
        return false;
    }
    sup_unanswered_count++;
    // each method once, for the discovery list
    static const char *seen[512];
    static unsigned nseen;
    for (unsigned k = 0; k < nseen; k++) {
        if (seen[k] == method) {
            return true;
        }
    }
    if (nseen < 512) {
        seen[nseen++] = method;
    }
    fprintf(stderr, "supervisor: unanswered (lenient) %s\n", method);
    return true;
}

void sup_unfilled(const char *what)
{
    if (sup_strict()) {
        fprintf(stderr, "supervisor: unfilled shadow value reached an output: %s\n", what);
        abort();
    }
    sup_lenient(what);
}
