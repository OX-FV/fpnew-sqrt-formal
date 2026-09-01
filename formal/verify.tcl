# Copyright 2026 University of Oxford.
# Licensed under the Apache License, Version 2.0 (see LICENSE for details).
# The underlying commands and reports of this script are copyrighted by Cadence.
# We thank Cadence for granting permission to share our research to help
# promote and foster the next generation of innovators.
# Original Authors: Louis-Emile Ploix, Ashraf Alam
# SPDX-License-Identifier: Apache-2.0

clear -all ;# Make this file reloadable

# Enable broad caching of proof results.
set_prove_cache on
set_prove_cache_path jgproofs
set_prove_cache_mode coi
set_prove_cache_traces true

analyze -sv12 -f build/filelist.txt

elaborate -top formal_fpnew_top -disable_auto_bbox

clock clk_i
reset ~rst_ni

