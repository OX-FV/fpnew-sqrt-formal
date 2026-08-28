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

