assume -from_assert <embedded>::formal_fpnew_top.OpStable
assume -from_assert <embedded>::formal_fpnew_top.Sqrt64BStable
assume -from_assert <embedded>::formal_fpnew_top.BaseCase
assume -from_assert <embedded>::formal_fpnew_top.Q_initial
assume -from_assert <embedded>::formal_fpnew_top.R_initial
assume -from_assert <embedded>::formal_fpnew_top.J_initial
assume -from_assert <embedded>::formal_fpnew_top.J_next
assume -from_assert <embedded>::formal_fpnew_top.R_next_eq
assume -from_assert <embedded>::formal_fpnew_top.Q_next_eq
assume -from_assert <embedded>::formal_fpnew_top.TimeConsistency
assume -from_assert <embedded>::formal_fpnew_top.SrtBusy
assume -from_assert <embedded>::formal_fpnew_top.Q_recur
assume -from_assert <embedded>::formal_fpnew_top.R_recur
assume -from_assert <embedded>::formal_fpnew_top.jBound
assume -from_assert <embedded>::formal_fpnew_top.q_bound

stopat j
stopat i_fpnew_top.gen_operation_groups(1).i_opgroup_block.gen_merged_slice.i_multifmt_slice.gen_num_lanes(0).active_lane.lane_instance.gen_thmulti_c910_divsqrt.i_fpnew_divsqrt_th_64_c910.i_ct_vfdsu_top.x_ct_vfdsu_ctrl.ex3_pipedown
stopat Q
stopat R
stopat R_next
stopat Q_next
stopat i_fpnew_top.gen_operation_groups(1).i_opgroup_block.gen_merged_slice.i_multifmt_slice.gen_num_lanes(0).active_lane.lane_instance.gen_thmulti_c910_divsqrt.i_fpnew_divsqrt_th_64_c910.divsqrt_fmt_q
stopat i_fpnew_top.gen_operation_groups(1).i_opgroup_block.gen_merged_slice.i_multifmt_slice.gen_num_lanes(0).active_lane.lane_instance.gen_thmulti_c910_divsqrt.i_fpnew_divsqrt_th_64_c910.divsqrt_op_q
stopat i_fpnew_top.gen_operation_groups(1).i_opgroup_block.gen_merged_slice.i_multifmt_slice.gen_num_lanes(0).active_lane.lane_instance.gen_thmulti_c910_divsqrt.i_fpnew_divsqrt_th_64_c910.vfdsu_dp_fdiv_busy
stopat q
stopat i_fpnew_top.gen_operation_groups(1).i_opgroup_block.gen_merged_slice.i_multifmt_slice.gen_num_lanes(0).active_lane.lane_instance.gen_thmulti_c910_divsqrt.i_fpnew_divsqrt_th_64_c910.i_ct_vfdsu_top.x_ct_vfdsu_double.x_ct_vfdsu_srt.x_ct_vfdsu_srt_radix16_with_sqrt.srt_sm_on

prove -property {<embedded>::formal_fpnew_top.R_correct} -bg