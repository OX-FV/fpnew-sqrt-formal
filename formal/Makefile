# Copyright 2026 University of Oxford.
# Licensed under the Apache License, Version 2.0 (see LICENSE for details).
# Original Authors: Louis-Emile Ploix, Ashraf Alam
# SPDX-License-Identifier: Apache-2.0

FPNEW_ROOT=..
export FPNEW_REPO_DIR=${FPNEW_ROOT}

.PHONY: build/filelist.txt
build/filelist.txt:
	mkdir -p build
	python3 flist.py formal.flist --copy build/copy > build/filelist.txt

.PHONY: jg
jg: build/filelist.txt
	jg verify.tcl -allow_unsupported_OS -acquire_proj

.PHONY: jg-shell
jg-shell: build/filelist.txt
	jg verify.tcl -allow_unsupported_OS -acquire_proj -no_gui

