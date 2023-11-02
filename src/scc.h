/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */
/*
 * Copyright 2023 Saso Kiselkov. All rights reserved.
 */

#ifndef	_LIBSCC_H_
#define	_LIBSCC_H_

#include <stdbool.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct scc_components_s scc_components_t;
typedef bool (*scc_handle_semicolon_t)(const scc_components_t *comps,
    void *userinfo);

bool scc_read(const char *filepath, scc_handle_semicolon_t cb, void *userinfo,
    char *out_err, size_t out_err_cap);
size_t scc_comp_count(const scc_components_t *comps);
const char *scc_comp_get(const scc_components_t *comps, size_t idx);

#ifdef __cplusplus
}
#endif

#endif	/* _LIBSCC_H_ */
