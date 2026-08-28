// Original author: Ashraf Alam, University of Oxford

module formal_fpnew_top#(
  // FPU configuration
  parameter fpnew_pkg::fpu_features_t       Features       = fpnew_pkg::RV64D_Xsflt,
  parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::DEFAULT_NOREGS,
  // DivSqrtSel chooses among PULP, TH32, or THMULTI (see documentation and fpnew_pkg.sv for further details)
  parameter fpnew_pkg::divsqrt_unit_t       DivSqrtSel     = fpnew_pkg::THMULTI,
  parameter type                            TagType        = logic,
  parameter int unsigned                    TrueSIMDClass  = 0,
  parameter int unsigned                    EnableSIMDMask = 0,
  // Do not change
  localparam int unsigned NumLanes     = fpnew_pkg::max_num_lanes(Features.Width, Features.FpFmtMask, Features.EnableVectors),
  localparam type         MaskType     = logic [NumLanes-1:0],
  localparam int unsigned WIDTH        = Features.Width,
  localparam int unsigned NUM_OPERANDS = 3
) (
  input logic                               clk_i,
  input logic                               rst_ni,
  // Input signals
  input logic [NUM_OPERANDS-1:0][WIDTH-1:0] operands_i,
  input fpnew_pkg::roundmode_e              rnd_mode_i,
  input fpnew_pkg::operation_e              op_i,
  input logic                               op_mod_i,
  input fpnew_pkg::fp_format_e              src_fmt_i,
  input fpnew_pkg::fp_format_e              dst_fmt_i,
  input fpnew_pkg::int_format_e             int_fmt_i,
  input logic                               vectorial_op_i,
  input TagType                             tag_i,
  input MaskType                            simd_mask_i,
  // Input Handshake
  input  logic                              in_valid_i,
  output logic                              in_ready_o,
  input  logic                              flush_i,
  // Output signals
  output logic [WIDTH-1:0]                  result_o,
  output fpnew_pkg::status_t                status_o,
  output TagType                            tag_o,
  // Output handshake
  output logic                              out_valid_o,
  input  logic                              out_ready_i,
  // Indication of valid data in flight
  output logic                              busy_o,
  output logic                              early_valid_o
);

fpnew_top i_fpnew_top (
    .*
);

localparam int unsigned LANE_NUM = 0; // This is the only lane which does 64 bit operations

`define MULTISLICE i_fpnew_top.gen_operation_groups[1].i_opgroup_block.gen_merged_slice.i_multifmt_slice
`define TH `MULTISLICE.gen_num_lanes[LANE_NUM].active_lane.lane_instance.gen_thmulti_c910_divsqrt.i_fpnew_divsqrt_th_64_c910
`define CTRL `TH.i_ct_vfdsu_top.x_ct_vfdsu_ctrl
`define SRT_SQRT `TH.i_ct_vfdsu_top.x_ct_vfdsu_double.x_ct_vfdsu_srt.x_ct_vfdsu_srt_radix16_with_sqrt
`define BUSY (`SRT_SQRT.srt_sm_on == `CTRL.SRT_BUSY)
`define IDLE (`SRT_SQRT.srt_sm_on == `CTRL.SRT_IDLE)
`define FIRST (j == '0 && `BUSY)
`define MIDDLE (`BUSY && ~`FIRST)
`define LAST (`CTRL.ex3_pipedown)
`define ROUND `TH.i_ct_vfdsu_top.x_ct_vfdsu_double.x_ct_vfdsu_round
`define PACK `TH.i_ct_vfdsu_top.x_ct_vfdsu_double.x_ct_vfdsu_pack
`define NO_SPECIAL (`TH.srcf0_q[WE+WF-1:WF] != '1 && `TH.srcf0_q[WE+WF-1:0] != '0 && `TH.srcf0_q[WE+WF] != 1)
`define SQRT_64B (`TH.divsqrt_fmt_q == 4'b1000 && `TH.divsqrt_op_q == fpnew_pkg::SQRT)

localparam int unsigned WE = 11; // exponent width
localparam int unsigned WF = 52; // fraction width
localparam int unsigned B = 4; // buffer to prevent overflow
localparam int unsigned L = 65; // number of bits to represent variables

logic signed [B+L-1:0] Q;
logic signed [B+L-1:0] R;
logic signed [B+L-1:0] TwoP;
logic signed [B+L-1:0] Q_next;
logic signed [B+L-1:0] R_next;
logic signed [4:0] q;
logic signed [B+L-1:0] q_scaled;
logic signed [7:0] q2;
logic signed [B+L-1:0] q2_scaled;
logic [B+L-1:0] X;
logic signed [B+L-1:0] Q_rnd;
logic signed [54:0] Q_after_rnd;
logic [5:0] clz;
logic [12:0] bias;

logic flush;
assign flush = `TH.i_ct_vfdsu_top.rtu_yy_xx_flush;

logic no_special;
assign no_special = (`TH.srcf0_q[WE+WF-1:WF] != '1 && `TH.srcf0_q[WE+WF-1:0] != '0 && `TH.srcf0_q[WE+WF] != 1);

assign Q = {{B{1'b0}},{7{1'b0}}, `SRT_SQRT.total_qt_rt}; // Q = total_qt_rt
assign R = {{B{`SRT_SQRT.srt_remainder[60]}}, `SRT_SQRT.srt_remainder, {4{1'b0}}}; // R = srt_remainder * 2**4
assign Q_rnd = {{B{1'b0}},{7{1'b0}}, `ROUND.total_qt_rt_58};
assign Q_after_rnd = `ROUND.frac_final_rst;
assign bias = 13'd1023;

logic signed [5:0] j;
assign j = 13 - $signed(`CTRL.srt_cnt); // iteration of the algorithm, going from 0 to 14

always_comb begin // TwoP = 2**(56 - 4*j)
  unique case (j)
    6'd0: TwoP = {{B{1'b0}}, {8{1'b0}}, 1'b1, {56{1'b0}}}; 
    6'd1: TwoP = {{B{1'b0}}, {12{1'b0}}, 1'b1, {52{1'b0}}};
    6'd2: TwoP = {{B{1'b0}}, {16{1'b0}}, 1'b1, {48{1'b0}}};
    6'd3: TwoP = {{B{1'b0}}, {20{1'b0}}, 1'b1, {44{1'b0}}}; 
    6'd4:  TwoP = {{B{1'b0}}, {24{1'b0}}, 1'b1, {40{1'b0}}}; 
    6'd5:  TwoP = {{B{1'b0}}, {28{1'b0}}, 1'b1, {36{1'b0}}}; 
    6'd6:  TwoP = {{B{1'b0}}, {32{1'b0}}, 1'b1, {32{1'b0}}}; 
    6'd7:  TwoP = {{B{1'b0}}, {36{1'b0}}, 1'b1, {28{1'b0}}}; 
    6'd8:  TwoP = {{B{1'b0}}, {40{1'b0}}, 1'b1, {24{1'b0}}}; 
    6'd9:  TwoP = {{B{1'b0}}, {44{1'b0}}, 1'b1, {20{1'b0}}};
    6'd10:  TwoP = {{B{1'b0}}, {48{1'b0}}, 1'b1, {16{1'b0}}};
    6'd11:  TwoP = {{B{1'b0}}, {52{1'b0}}, 1'b1, {12{1'b0}}};
    6'd12:  TwoP = {{B{1'b0}}, {56{1'b0}}, 1'b1, {8{1'b0}}};
    6'd13:  TwoP = {{B{1'b0}}, {60{1'b0}}, 1'b1, {4{1'b0}}};
    6'd14: TwoP = {{B{1'b0}}, {64{1'b0}}, 1'b1, {0{1'b0}}};
    default : TwoP = 0;
  endcase
end

always_comb begin // -9 <= q <= 9
  unique case ({`SRT_SQRT.rem_sign,`SRT_SQRT.bound_cmp_sign})
    10'b0111111111: q = 5'd0;
    10'b0011111111: q = 5'd1;
    10'b0001111111: q = 5'd2;
    10'b0000111111: q = 5'd3;
    10'b0000011111: q = 5'd4;
    10'b0000001111: q = 5'd5;
    10'b0000000111: q = 5'd6;
    10'b0000000011: q = 5'd7;
    10'b0000000001: q = 5'd8;
    10'b0000000000: q = 5'd9;
    10'b1111111111: q = -5'd0;
    10'b1011111111: q = -5'd1;
    10'b1001111111: q = -5'd2;
    10'b1000111111: q = -5'd3;
    10'b1000011111: q = -5'd4;
    10'b1000001111: q = -5'd5;
    10'b1000000111: q = -5'd6;
    10'b1000000011: q = -5'd7;
    10'b1000000001: q = -5'd8;
    10'b1000000000: q = -5'd9;
    default: q = 0;
  endcase
end

assign Q_next = {{B{1'b0}},{7{1'b0}}, `SRT_SQRT.total_qt_rt_next};
assign q2 = q*q;

always_comb begin // q_scaled = q * 2**(54-4*j)
  unique case (j)
    6'd0: q_scaled = {{B+6{q[4]}}, q, {54{1'b0}}};
    6'd1: q_scaled = {{B+10{q[4]}}, q, {50{1'b0}}};
    6'd2: q_scaled = {{B+14{q[4]}}, q, {46{1'b0}}};
    6'd3: q_scaled = {{B+18{q[4]}}, q, {42{1'b0}}};
    6'd4: q_scaled = {{B+22{q[4]}}, q, {38{1'b0}}};
    6'd5: q_scaled = {{B+26{q[4]}}, q, {34{1'b0}}};
    6'd6: q_scaled = {{B+30{q[4]}}, q, {30{1'b0}}};
    6'd7: q_scaled = {{B+34{q[4]}}, q, {26{1'b0}}};
    6'd8: q_scaled = {{B+38{q[4]}}, q, {22{1'b0}}};
    6'd9: q_scaled = {{B+42{q[4]}}, q, {18{1'b0}}};
    6'd10: q_scaled = {{B+46{q[4]}}, q, {14{1'b0}}};
    6'd11: q_scaled = {{B+50{q[4]}}, q, {10{1'b0}}};
    6'd12: q_scaled = {{B+54{q[4]}}, q, {6{1'b0}}};
    6'd13: q_scaled = {{B+58{q[4]}}, q, {2{1'b0}}};
    default q_scaled = 0;
  endcase
end

assign R_next = {{B{`SRT_SQRT.srt_remainder_nxt[60]}}, `SRT_SQRT.srt_remainder_nxt, {4{1'b0}}}; // R_next = srt_remainder_nxt * 2**4

always_comb begin // q2_scaled = q**2 * 2**(56-4*j)
  unique case (j)
    6'd0: q2_scaled = {{B+1{1'b0}}, q2, {56{1'b0}}};
    6'd1: q2_scaled = {{B+5{1'b0}}, q2, {52{1'b0}}};
    6'd2: q2_scaled = {{B+9{1'b0}}, q2, {48{1'b0}}};
    6'd3: q2_scaled = {{B+13{1'b0}}, q2, {44{1'b0}}};
    6'd4: q2_scaled = {{B+17{1'b0}}, q2, {40{1'b0}}};
    6'd5: q2_scaled = {{B+21{1'b0}}, q2, {36{1'b0}}};
    6'd6: q2_scaled = {{B+25{1'b0}}, q2, {32{1'b0}}};
    6'd7: q2_scaled = {{B+29{1'b0}}, q2, {28{1'b0}}};
    6'd8: q2_scaled = {{B+33{1'b0}}, q2, {24{1'b0}}};
    6'd9: q2_scaled = {{B+37{1'b0}}, q2, {20{1'b0}}};
    6'd10: q2_scaled = {{B+41{1'b0}}, q2, {16{1'b0}}};
    6'd11: q2_scaled = {{B+45{1'b0}}, q2, {12{1'b0}}};
    6'd12: q2_scaled = {{B+49{1'b0}}, q2, {8{1'b0}}};
    6'd13: q2_scaled = {{B+53{1'b0}}, q2, {4{1'b0}}};
    default: q2_scaled = 0;
  endcase
end

always_comb begin
  if (`TH.srcf0_q[WF+WE-1:WF] == '0) begin // denormal
    unique casez (`TH.srcf0_q[WF-1:0])
      52'b1???????????????????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-1:0],{L-7-WF{1'b0}}}; clz = 6'd0;  end
      52'b01??????????????????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-2:0],{L-7-WF{1'b0}}}; clz = 6'd1;  end
      52'b001?????????????????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-3:0],{L-5-WF{1'b0}}}; clz = 6'd2;  end
      52'b0001????????????????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-4:0],{L-5-WF{1'b0}}}; clz = 6'd3;  end
      52'b00001???????????????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-5:0],{L-3-WF{1'b0}}}; clz = 6'd4;  end
      52'b000001??????????????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-6:0],{L-3-WF{1'b0}}}; clz = 6'd5;  end
      52'b0000001?????????????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-7:0],{L-1-WF{1'b0}}}; clz = 6'd6;  end
      52'b00000001????????????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-8:0],{L-1-WF{1'b0}}}; clz = 6'd7;  end
      52'b000000001???????????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-9:0],{L+1-WF{1'b0}}}; clz = 6'd8;  end
      52'b0000000001??????????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-10:0],{L+1-WF{1'b0}}}; clz = 6'd9;  end
      52'b00000000001?????????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-11:0],{L+3-WF{1'b0}}}; clz = 6'd10;  end
      52'b000000000001????????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-12:0],{L+3-WF{1'b0}}}; clz = 6'd11;  end
      52'b0000000000001???????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-13:0],{L+5-WF{1'b0}}}; clz = 6'd12;  end
      52'b00000000000001??????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-14:0],{L+5-WF{1'b0}}}; clz = 6'd13;  end
      52'b000000000000001?????????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-15:0],{L+7-WF{1'b0}}}; clz = 6'd14;  end
      52'b0000000000000001????????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-16:0],{L+7-WF{1'b0}}}; clz = 6'd15;  end
      52'b00000000000000001???????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-17:0],{L+9-WF{1'b0}}}; clz = 6'd16;  end
      52'b000000000000000001??????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-18:0],{L+9-WF{1'b0}}}; clz = 6'd17;  end
      52'b0000000000000000001?????????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-19:0],{L+11-WF{1'b0}}}; clz = 6'd18;  end
      52'b00000000000000000001????????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-20:0],{L+11-WF{1'b0}}}; clz = 6'd19;  end
      52'b000000000000000000001???????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-21:0],{L+13-WF{1'b0}}}; clz = 6'd20;  end
      52'b0000000000000000000001??????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-22:0],{L+13-WF{1'b0}}}; clz = 6'd21;  end
      52'b00000000000000000000001?????????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-23:0],{L+15-WF{1'b0}}}; clz = 6'd22;  end
      52'b000000000000000000000001????????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-24:0],{L+15-WF{1'b0}}}; clz = 6'd23;  end
      52'b0000000000000000000000001???????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-25:0],{L+17-WF{1'b0}}}; clz = 6'd24;  end
      52'b00000000000000000000000001??????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-26:0],{L+17-WF{1'b0}}}; clz = 6'd25;  end
      52'b000000000000000000000000001?????????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-27:0],{L+19-WF{1'b0}}}; clz = 6'd26;  end
      52'b0000000000000000000000000001????????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-28:0],{L+19-WF{1'b0}}}; clz = 6'd27;  end
      52'b00000000000000000000000000001???????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-29:0],{L+21-WF{1'b0}}}; clz = 6'd28;  end
      52'b000000000000000000000000000001??????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-30:0],{L+21-WF{1'b0}}}; clz = 6'd29;  end
      52'b0000000000000000000000000000001?????????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-31:0],{L+23-WF{1'b0}}}; clz = 6'd30;  end
      52'b00000000000000000000000000000001????????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-32:0],{L+23-WF{1'b0}}}; clz = 6'd31;  end
      52'b000000000000000000000000000000001???????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-33:0],{L+25-WF{1'b0}}}; clz = 6'd32;  end
      52'b0000000000000000000000000000000001??????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-34:0],{L+25-WF{1'b0}}}; clz = 6'd33;  end
      52'b00000000000000000000000000000000001?????????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-35:0],{L+27-WF{1'b0}}}; clz = 6'd34;  end
      52'b000000000000000000000000000000000001????????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-36:0],{L+27-WF{1'b0}}}; clz = 6'd35;  end
      52'b0000000000000000000000000000000000001???????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-37:0],{L+29-WF{1'b0}}}; clz = 6'd36;  end
      52'b00000000000000000000000000000000000001??????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-38:0],{L+29-WF{1'b0}}}; clz = 6'd37;  end
      52'b000000000000000000000000000000000000001?????????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-39:0],{L+31-WF{1'b0}}}; clz = 6'd38;  end
      52'b0000000000000000000000000000000000000001????????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-40:0],{L+31-WF{1'b0}}}; clz = 6'd39;  end
      52'b00000000000000000000000000000000000000001???????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-41:0],{L+33-WF{1'b0}}}; clz = 6'd40;  end
      52'b000000000000000000000000000000000000000001??????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-42:0],{L+33-WF{1'b0}}}; clz = 6'd41;  end
      52'b0000000000000000000000000000000000000000001?????????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-43:0],{L+35-WF{1'b0}}}; clz = 6'd42;  end
      52'b00000000000000000000000000000000000000000001????????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-44:0],{L+35-WF{1'b0}}}; clz = 6'd43;  end
      52'b000000000000000000000000000000000000000000001???????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-45:0],{L+37-WF{1'b0}}}; clz = 6'd44;  end
      52'b0000000000000000000000000000000000000000000001??????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-46:0],{L+37-WF{1'b0}}}; clz = 6'd45;  end
      52'b00000000000000000000000000000000000000000000001?????: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-47:0],{L+39-WF{1'b0}}}; clz = 6'd46;  end
      52'b000000000000000000000000000000000000000000000001????: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-48:0],{L+39-WF{1'b0}}}; clz = 6'd47;  end
      52'b0000000000000000000000000000000000000000000000001???: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-49:0],{L+41-WF{1'b0}}}; clz = 6'd48;  end
      52'b00000000000000000000000000000000000000000000000001??: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-50:0],{L+41-WF{1'b0}}}; clz = 6'd49;  end
      52'b000000000000000000000000000000000000000000000000001?: begin X = {{B+7{1'b0}},`TH.srcf0_q[WF-51:0],{L+43-WF{1'b0}}}; clz = 6'd50;  end
      52'b0000000000000000000000000000000000000000000000000001: begin X = {{B+8{1'b0}},`TH.srcf0_q[WF-52:0],{L+43-WF{1'b0}}}; clz = 6'd51;  end
      default: begin X = 69'b000000000001000000000000000000000000000000000000000000000000000000000; clz = 6'd52; end// this is what RTL sets srt_remainder to when operand = +-0
    endcase
  end else begin // normal
    if (`TH.srcf0_q[WF]) begin
      X = {{B+8{1'b0}},1'b1,`TH.srcf0_q[WF-1:0],{L-9-WF{1'b0}}};
      clz = 0;
    end else begin
      X = {{B+7{1'b0}},1'b1,`TH.srcf0_q[WF-1:0],{L-8-WF{1'b0}}};
      clz = 0;
    end
  end
end // we have 2^56 <= X < 2^58

NotRodDyn: assume property (`TH.rnd_mode_q inside {fpnew_pkg::RNE, fpnew_pkg::RTZ, fpnew_pkg::RDN, fpnew_pkg::RUP, fpnew_pkg::RMM}); // although not true for fpnew, true for cva6

// DoSqrt2: cover property (`TH.srcf0_q == {2'b01,{WE+WF-1{1'b0}}} && `TH.unit_done);

SpecialCases: assert property (
  (`TH.unit_done && `SQRT_64B) |-> (
    ((`TH.srcf0_q inside {'0, {1'b1,{WE+WF{1'b0}}}, {1'b0,{WE{1'b1}},{WF{1'b0}}}}) -> `TH.unit_result == `TH.srcf0_q) && 
    ((`TH.srcf0_q[WE+WF-1:WF] == '1 && `TH.srcf0_q[WF-1:0] != '0) || (`TH.srcf0_q[WE+WF] && `TH.srcf0_q != {1'b1,{WE+WF{1'b0}}})) -> `TH.unit_result == {1'b0,{WE+1{1'b1}},{WF-1{1'b0}}}
  )
); // result is correct in special cases: operand is +-0, +-inf, NaN, or negative

// First of all we check flushing works correcly:

logic flushed;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (~rst_ni) begin
    flushed <= 1;
  end else begin
    if (`TH.op_starting && ~flush) begin
      flushed <= 0;
    end else if (flush) begin
      flushed <= 1;
    end else begin
      flushed <= flushed;
    end
  end
end

// If there is a `TH.unit_done then there was no flush between now and the prev `TH.op_starting
DoneImpNoFlush: assert property (`TH.unit_done |-> ~flushed);
// If there is an opstarting without flush, then in the next 19 cycles there will be a unit done or flush at some point
NoDisappearingOps: assert property ((`TH.op_starting && ~flush) |-> ##[1:19](`TH.unit_done || flush));

// Characterisation of busy - not necessary for Lean proof: 
// if `TH.op_starting && ~flush then busy high on next cycle
Busy1: assert property ((`TH.op_starting && ~flush) |=> `TH.vfdsu_dp_fdiv_busy);
// if busy high then busy stays high until (flush || `CTRl.ex4_pipedown) - and becomes low on the next cycle
Busy2: assert property ((`TH.vfdsu_dp_fdiv_busy && ~(flush || `CTRL.ex4_pipedown)) |=> `TH.vfdsu_dp_fdiv_busy);
Busy3: assert property ((flush || `CTRL.ex4_pipedown) |=> ~`TH.vfdsu_dp_fdiv_busy);

// Now we prove what we need for correctness

OpStable: assert property (`TH.vfdsu_dp_fdiv_busy |=> ($stable(`TH.srcf0_q) && $stable(`TH.rm_q) && $stable(X)));
Sqrt64BStable : assert property (`TH.vfdsu_dp_fdiv_busy |=> $stable(`SQRT_64B)); // this together with the Busy SVAs above tell us the stored operand does not change between op_starting and unit_done
ResultEqPack: assert property (`TH.unit_result == `PACK.ex4_out_result);
Ex4UnitDone: assert property (`TH.unit_done == (~$past(flush) && $past(`CTRL.ex4_pipedown)));
Ex4ResStable: assert property (`TH.unit_done |-> $stable(`PACK.ex4_out_result));
WasBusy: assert property (`TH.unit_done |-> $past(`TH.vfdsu_dp_fdiv_busy));
NoSpecialStable: assert property ($stable(`TH.srcf0_q) -> $stable(no_special));
PackInp: assert property (`CTRL.ex4_pipedown |-> `PACK.vfdsu_ex4_frac == $past(Q_after_rnd));
PackMantissa: assert property ((`CTRL.ex4_pipedown && no_special && `SQRT_64B) |-> `PACK.ex4_out_result[WF-1:0] == (`PACK.vfdsu_ex4_frac[54] ? `PACK.vfdsu_ex4_frac[53:2] : (`PACK.vfdsu_ex4_frac[53] ? `PACK.vfdsu_ex4_frac[52:1] : `PACK.vfdsu_ex4_frac[51:0])));

logic signed [12:0] biased_expnt;
logic signed [12:0] expected_expnt;
logic signed [12:0] half_expnt;
// `TH.srcf0_q[WE+WF-1:WF] is 11 bits, bias is 1023 so 10 significant bits, and clz is at most 52, so 6 bits
// Therefore the two 0s appended to the left of `TH.srcf0_q[WE+WF-1:WF] ensure no overflow
assign biased_expnt = {2'b00,`TH.srcf0_q[WE+WF-1:WF]} - bias - clz; 
assign half_expnt = {biased_expnt[12],biased_expnt[12:1]} + bias;
// half_expnt = biased_expnt / 2 + bias >= (-1023 - 52) / 2 + 1023 = 486
// half_expnt = biased_expnt / 2 + bias < (2**11 - 1023 - 52) / 2 + 1023 = 1509
// expected_expnt is 13 bits so no possibility for overflow
assign expected_expnt = `PACK.vfdsu_ex4_frac[54] ? half_expnt + 1 : `PACK.vfdsu_ex4_frac[53] ? half_expnt : half_expnt - 1;

// Sign0: assert property ((`CTRL.ex4_pipedown && no_special && `SQRT_64B) |-> ~`PACK.ex4_out_result[WE+WF]); // not needed
PackExpnt: assert property ((`CTRL.ex4_pipedown && no_special && `SQRT_64B) |-> `PACK.ex4_out_result[WF+WE-1:WF] == expected_expnt[10:0]);
Ex3Ex4: assert property (`CTRL.ex4_pipedown == (~$past(flush) && $past(`CTRL.ex3_pipedown)));
Ex3Ex4Stable: assert property (`CTRL.ex4_pipedown |-> ($stable(`TH.rm_q) && $stable(`TH.srcf0_q)));

logic [3:0] rnd_bits;
assign rnd_bits = Q_rnd[56] ? Q_rnd[3:0] : {Q_rnd[2:0],1'b0};

// To assure that there is no possibility of overflow in the following:
NoOverflowRound: assert property ((`CTRL.ex3_pipedown && no_special && `SQRT_64B) |-> (Q_rnd[B+L-1] == 0 && Q_rnd >= 2));

RNE_add1: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RNE && `SQRT_64B
   && (rnd_bits > 4'b1000 || (rnd_bits == 4'b1000 && R>=0))) 
   |-> Q_after_rnd == (Q[56] ? (Q_rnd[B+L-1:3] + 2'b10) : (Q_rnd[B+L-1:3] + 1'b1))
);
RNE_orig: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RNE && `SQRT_64B
   && !(rnd_bits > 4'b1000 || (rnd_bits == 4'b1000 && R>=0))) 
   |-> Q_after_rnd == Q_rnd[B+L-1:3]
);
RTZ_sub1: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RTZ && `SQRT_64B
   && (rnd_bits == 4'b0000 && R<0)) 
   |-> Q_after_rnd == (Q[56] ? (Q_rnd[B+L-1:3] - 2'b10) : (Q_rnd[B+L-1:3] - 1'b1))
);
RTZ_orig: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RTZ && `SQRT_64B
   && !(rnd_bits == 4'b0000 && R<0)) 
   |-> Q_after_rnd == Q_rnd[B+L-1:3]
);
RUP_add1: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RUP && `SQRT_64B
   && (rnd_bits != 0 || R>0)) 
   |-> Q_after_rnd == (Q[56] ? (Q_rnd[B+L-1:3] + 2'b10) : (Q_rnd[B+L-1:3] + 1'b1))
);
RUP_orig: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RUP && `SQRT_64B
   && !(rnd_bits != 0 || R>0)) 
   |-> Q_after_rnd == Q_rnd[B+L-1:3]
);
RDN_sub1: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RDN && `SQRT_64B
   && (rnd_bits == 4'b0000 && R<0)) 
   |-> Q_after_rnd == (Q[56] ? (Q_rnd[B+L-1:3] - 2'b10) : (Q_rnd[B+L-1:3] - 1'b1))
);
RDN_orig: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RDN && `SQRT_64B
   && !(rnd_bits == 4'b0000 && R<0)) 
   |-> Q_after_rnd == Q_rnd[B+L-1:3]
);
RMM_add1: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RMM && `SQRT_64B
   && (rnd_bits > 4'b1000 || (rnd_bits == 4'b1000 && R>=0))) 
   |-> Q_after_rnd == (Q[56] ? (Q_rnd[B+L-1:3] + 2'b10) : (Q_rnd[B+L-1:3] + 1'b1))
);
RMM_orig: assert property (
  (`CTRL.ex3_pipedown && no_special && `TH.rm_q == fpnew_pkg::RMM && `SQRT_64B
   && !(rnd_bits > 4'b1000 || (rnd_bits == 4'b1000 && R>=0))) 
   |-> Q_after_rnd == Q_rnd[B+L-1:3]
);


// Inductive hypothesis: (`FIRST || `MIDDLE || `LAST) -> R * 2**(56 - 4*j) == 2**56 * X - Q**2
BaseCase: assert property (((`FIRST || `MIDDLE || `LAST) && j == '0) -> `FIRST);
Q_initial: assert property (`FIRST -> Q == '0); // Q_0 = 0
R_initial: assert property ((`FIRST && `SQRT_64B) -> (R == X)); // R_0 = X

J_initial: assert property (`FIRST -> j == '0);
J_next: assert property (((`MIDDLE || `LAST) && `SQRT_64B) -> (j == 1 + $past(j) && j != 0)); // should show j != 0 to eleminate possible overflow
R_next_eq: assert property (((`MIDDLE || `LAST) && `SQRT_64B) -> (R == $past(R_next)));
Q_next_eq: assert property (((`MIDDLE || `LAST) && `SQRT_64B) -> (Q == $past(Q_next)));
TimeConsistency: assert property (((`MIDDLE || `LAST) && `SQRT_64B) -> ($past(`FIRST || `MIDDLE)));
SrtBusy: assert property ((`FIRST || `MIDDLE || `LAST) -> `TH.vfdsu_dp_fdiv_busy); // needed for stability of X
Q_recur: assert property (((`FIRST || `MIDDLE) && `SQRT_64B) -> Q_next == Q + q_scaled); // Q_{j+1} = Q_j + 2**{-4j-2} * q_j
R_recur: assert property (((`FIRST || `MIDDLE) && `SQRT_64B) -> R_next == (R << 4) - (Q*q << 3) - q2_scaled); // R_{j+1} = 16 * R_j - 8 * Q_j * q_j - 16**{-j} * q_j**2
q_bound: assert property (-9 <= q && q <= 9); // not needed
// Inv: assert property (((`MIDDLE || `LAST) && `SQRT_64B) -> ((9*TwoP - 6*Q <= R) && (R <= 9*TwoP + 6*Q))); // not needed - QRndIneq is enough
QRndIneq: assert property ((`CTRL.ex3_pipedown && no_special && `SQRT_64B) |-> ((9 - 6*Q_rnd <= R) && (R <= 9 + 6*Q_rnd)));
DefOfLast: assert property (`LAST == `CTRL.ex3_pipedown);
QEquals: assert property (Q_rnd == Q);
StopEarly: assert property ((`CTRL.ex3_pipedown && no_special && j != 6'd14 && `SQRT_64B) |-> R == 0);
// Since StopEarly proves, if we have `CTRL.ex3_pipedown && no_special then we can split into two cases:
// j = 14 or j != 14
// if j = 14, then we have R = 2**56 * X - Q**2, so together with Inv, we have a good bound on Q ((Q_rnd - 4)**2 < 2**56 * X < (Q_rnd + 4)**2)
// otherwise j != 14, so we have R = 0, so since we have R * 2**(56 - 4*j) = 2**56 * X - Q**2, we have 2**56 * X == Q**2

// We have a relationship between `TH.unit_done and X. We don't have SVA for the relationship between X and `TH.srcf0_q, but X is related to `TH.srcf0_q combinationally and it's probably best to just write this in Lean directly.

// In my Lean proof I implicitly assume operand and result are non-negative by ignoring the sign bits when converting to real numbers
// This is justified:
NonNeg: assert property ((`TH.unit_done && no_special && `SQRT_64B) |-> (~`TH.unit_result[63] and ~`TH.srcf0_q[63]));

ResNoDenorm: assert property ((`TH.unit_done && no_special && `SQRT_64B) |-> `TH.unit_result[WE+WF-1:WF] != 0); // speeding up the Lean proof

// Ensuring no overflow in the operations above (justifying the use of integers in place of signed bit vectors in the Lean proof):
NoOverflow_Q_recur: assert property (((`FIRST || `MIDDLE) && `SQRT_64B) -> (~Q_next[B+L-1] && ~Q[B+L-1]));
// For R_recur, note from the definitions, R has been padded to the left by 4 bits, and Q by 13 bits. q is at most 9 in magnitude so Q*q << 3 still has at least 5 redundant leading bits
// q2_scaled has 5 padded bits to the left
NoOverflow_R_recur: assert property (((`FIRST || `MIDDLE) && `SQRT_64B) -> R[L-1] == R[L-2]);
// This shows that R has at least 5 redundant leading bits (so that R << 4 has at least one redundant leading bit), so there is no possibility for overflow

jNat: assert property (j >= 0); // justifies treating j as a natural number in lean
jBound: assert property ((`FIRST || `MIDDLE) -> j <= 13); // needed for Lean proof
OpNonZero: assert property (no_special -> `TH.srcf0_q[WE+WF-1:0] != '0);


// Bug: cover property (
//   (`MULTISLICE.in_valid_i && ~`MULTISLICE.in_ready_o && `MULTISLICE.out_valid_o) 
//   ##1 (`MULTISLICE.in_valid_i && ~`MULTISLICE.in_ready_o && ~`MULTISLICE.out_valid_o)[*5]
//   |=> `MULTISLICE.out_valid_o
// ); // bug found by Nguyen Vu, issue 183 in openhwgroup/cvfpu
// // This is a bug to do with the handshaking signals. My proof does not talk about these signals.


// R_correct: assert property (((`FIRST || `MIDDLE || `LAST) && `SQRT_64B) -> (R << (56-4*j)) == (X << 56) - Q*Q);
// To attempt a proof of this using relevant assumptions and stopats, run source r_correct.tcl
// This proof attempt timed out after 24 hours.

endmodule