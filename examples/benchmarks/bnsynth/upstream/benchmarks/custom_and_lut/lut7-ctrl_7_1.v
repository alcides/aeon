//EPFL output range: i_7 to i_32. We only synthesize for i_32
//Inputs: i_0 to i_6
module top (i_0 , i_1, i_2, i_3, i_4, i_5, i_6, i_7, i_8, i_9, i_10, i_11, i_12, i_13, i_14, i_15, i_16, i_17, i_18, i_19, i_20, i_21, i_22, i_23, i_24, i_25, i_26 , i_27 , i_28 , i_29 , i_30 , i_31 , i_32, out);

  input  i_0 , i_1, i_2, i_3, i_4, i_5, i_6, i_7, i_8, i_9, i_10, i_11, i_12, i_13, i_14, i_15, i_16, i_17, i_18, i_19, i_20, i_21, i_22, i_23, i_24, i_25 , i_26 , i_27 , i_28 , i_29 , i_30 , i_31 , i_32;
  output out;
  wire n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48,
    n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n63, n64,
    n65, n66, n67, n68, n69, n71, n72, n73, n74, n75, n76, n77, n78, n80,
    n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94,
    n95, n96, n97, n99, n100, n101, n102, n103, n104, n106, n107, n108,
    n109, n110, n111, n112, n113, n114, n115, n117, n118, n119, n120, n121,
    n123, n124, n125, n126, n127, n128, n129, n131, n132, n134, n135, n136,
    n137, n139, n140, n141, n142, n143, n145, n146, n147, n148, n149, n150,
    n151, n153, n154, n156, n158, n159, n160, n161, n162, n164, n165, n166,
    n167, n169, n170, n171, n173, n174, n175, n177, n179, n180, n181, n182,
    n183, n184, n185, n186, n188, n189, n190, n191, n192, n193, n194, n195,
    n197, n198, n200, n201, n202, n203, n205, n206, n207, sel_reg_dst_0, sel_reg_dst_0_1 , 
	sel_reg_dst_1 , sel_alu_opB_0 ,
    sel_alu_opB_1 , alu_op_0 , alu_op_1 , alu_op_2 ,
    alu_i_31 , alu_i_32 , alu_op_ext_2 , alu_op_ext_3 ,
    halt, reg_write, sel_pc_opA, sel_pc_opB, beqz, bnez, bgez, bltz, jump,
    Cin, invA, invB, sign, mem_write, sel_wb ;
  assign n35 = i_26  & ~i_27 ;
  assign n36 = i_29  & i_30 ;
  assign n37 = n35 & n36;
  assign n38 = i_27  & i_29 ;
  assign n39 = i_30  & n38;
  assign n40 = ~n37 & ~n39;
  assign n41 = ~i_28  & ~n40;
  assign n42 = ~i_27  & i_29 ;
  assign n43 = i_30  & n42;
  assign n44 = ~i_29  & ~i_30 ;
  assign n45 = ~n36 & ~n44;
  assign n46 = i_27  & ~n45;
  assign n47 = ~n43 & ~n46;
  assign n48 = i_28  & ~n47;
  assign sel_reg_dst_0  = n41 | n48;
  assign n50 = ~i_26  & ~n36;
  assign n51 = ~i_26  & ~n50;
  assign n52 = ~i_27  & ~n51;
  assign n53 = ~i_29  & ~n44;
  assign n54 = i_27  & ~n53;
  assign n55 = ~n52 & ~n54;
  assign n56 = ~i_28  & ~n55;
  assign n57 = ~i_29  & i_30 ;
  assign n58 = ~i_29  & ~n57;
  assign n59 = i_27  & ~n58;
  assign n60 = i_27  & ~n59;
  assign n61 = i_28  & ~n60;
  assign sel_reg_dst_1  = ~n56 & ~n61;
  assign n63 = ~i_26  & ~n45;
  assign n64 = i_29  & ~n36;
  assign n65 = i_26  & ~n64;
  assign n66 = ~n63 & ~n65;
  assign n67 = i_27  & ~n66;
  assign n68 = ~n52 & ~n67;
  assign n69 = ~i_28  & ~n68;
  assign sel_alu_opB_0  = ~i_28  & ~n69;
  assign n71 = ~i_26  & ~i_29 ;
  assign n72 = ~n57 & n71;
  assign n73 = i_26  & ~n45;
  assign n74 = ~n72 & ~n73;
  assign n75 = ~i_27  & ~n74;
  assign n76 = ~n54 & ~n75;
  assign n77 = ~i_28  & ~n76;
  assign n78 = i_28  & ~n53;
  assign sel_alu_opB_1  = ~n77 & ~n78;
  assign n80 = ~i_26  & i_29 ;
  assign n81 = i_30  & i_31 ;
  assign n82 = n80 & n81;
  assign n83 = i_29  & ~i_32 ;
  assign n84 = ~n36 & n83;
  assign n85 = i_29  & ~i_31 ;
  assign n86 = ~n36 & n85;
  assign n87 = i_29  & i_31 ;
  assign n88 = ~n86 & ~n87;
  assign n89 = i_32  & ~n88;
  assign n90 = ~n84 & ~n89;
  assign n91 = i_26  & ~n90;
  assign n92 = ~n82 & ~n91;
  assign n93 = i_27  & ~n92;
  assign n94 = ~i_28  & ~n93;
  assign n95 = i_26  & ~n53;
  assign n96 = i_26  & ~n95;
  assign n97 = i_28  & ~n96;
  assign alu_op_0  = ~n94 & ~n97;
  assign n99 = i_29  & i_32 ;
  assign n100 = ~n84 & ~n99;
  assign n101 = i_27  & ~n100;
  assign n102 = ~i_28  & ~n101;
  assign n103 = i_27  & ~n54;
  assign n104 = i_28  & ~n103;
  assign alu_op_1  = ~n102 & ~n104;
  assign n106 = ~i_27  & ~n36;
  assign n107 = ~n44 & n106;
  assign n108 = ~n44 & n50;
  assign n109 = i_26  & ~n58;
  assign n110 = ~n108 & ~n109;
  assign n111 = i_27  & ~n110;
  assign n112 = ~n107 & ~n111;
  assign n113 = ~i_28  & ~n112;
  assign n114 = i_28  & i_29 ;
  assign n115 = i_30  & n114;
  assign alu_op_2  = n113 | n115;
  assign n117 = ~i_27  & ~i_28 ;
  assign n118 = ~n52 & n117;
  assign n119 = i_27  & ~n74;
  assign n120 = ~n37 & ~n119;
  assign n121 = i_28  & ~n120;
  assign alu_i_31  = n118 | n121;
  assign n123 = ~i_26  & ~n53;
  assign n124 = ~i_26  & ~n123;
  assign n125 = i_27  & ~n124;
  assign n126 = i_27  & ~i_28 ;
  assign n127 = ~n125 & n126;
  assign n128 = i_27  & i_28 ;
  assign n129 = ~n45 & n128;
  assign alu_i_32  = n127 | n129;
  assign n131 = ~n106 & ~n125;
  assign n132 = ~i_28  & ~n131;
  assign alu_op_ext_2  = ~n61 & ~n132;
  assign n134 = ~n80 & ~n109;
  assign n135 = i_27  & ~n134;
  assign n136 = ~i_28  & ~n107;
  assign n137 = ~n135 & n136;
  assign alu_op_ext_3  = ~n78 & ~n137;
  assign n139 = ~i_26  & ~n58;
  assign n140 = ~i_26  & ~n139;
  assign n141 = ~i_27  & ~n140;
  assign n142 = ~i_27  & ~n141;
  assign n143 = ~i_28  & ~n142;
  assign halt = ~i_28  & ~n143;
  assign n145 = ~i_27  & ~n134;
  assign n146 = ~n59 & ~n145;
  assign n147 = ~i_28  & ~n146;
  assign n148 = ~i_27  & i_30 ;
  assign n149 = i_27  & ~n64;
  assign n150 = ~n148 & ~n149;
  assign n151 = i_28  & ~n150;
  assign reg_write = n147 | n151;
  assign n153 = i_26  & ~n109;
  assign n154 = i_28  & ~n153;
  assign sel_pc_opA = i_28  & ~n154;
  assign n156 = i_28  & ~n140;
  assign sel_pc_opB = i_28  & ~n156;
  assign n158 = ~i_26  & ~n64;
  assign n159 = ~i_26  & ~n158;
  assign n160 = ~i_27  & ~n159;
  assign n161 = ~i_27  & ~n160;
  assign n162 = i_28  & ~n161;
  assign beqz = i_28  & ~n162;
  assign n164 = i_26  & ~n65;
  assign n165 = ~i_27  & ~n164;
  assign n166 = ~i_27  & ~n165;
  assign n167 = i_28  & ~n166;
  assign bnez = i_28  & ~n167;
  assign n169 = i_27  & ~n164;
  assign n170 = i_27  & ~n169;
  assign n171 = i_28  & ~n170;
  assign bgez = i_28  & ~n171;
  assign n173 = i_27  & ~n159;
  assign n174 = i_27  & ~n173;
  assign n175 = i_28  & ~n174;
  assign bltz = i_28  & ~n175;
  assign n177 = i_28  & ~n58;
  assign jump = i_28  & ~n177;
  assign n179 = i_26  & i_27 ;
  assign n180 = ~n88 & n179;
  assign n181 = n35 & ~n65;
  assign n182 = ~i_28  & ~n181;
  assign n183 = ~n180 & n182;
  assign n184 = i_27  & ~n51;
  assign n185 = ~n106 & ~n184;
  assign n186 = i_28  & ~n185;
  assign Cin = ~n183 & ~n186;
  assign n188 = i_31  & n36;
  assign n189 = ~i_32  & ~n188;
  assign n190 = ~i_32  & ~n189;
  assign n191 = i_26  & ~n190;
  assign n192 = i_26  & ~n191;
  assign n193 = i_27  & ~n192;
  assign n194 = ~n165 & ~n193;
  assign n195 = ~i_28  & ~n194;
  assign invA = ~i_28  & ~n195;
  assign n197 = ~n90 & n179;
  assign n198 = ~i_28  & ~n197;
  assign invB = ~n186 & ~n198;
  assign n200 = ~i_27  & ~n124;
  assign n201 = i_27  & ~n96;
  assign n202 = ~n200 & ~n201;
  assign n203 = ~i_28  & ~n202;
  assign mem_write = ~i_28  & ~n203;
  assign n205 = ~i_27  & ~n96;
  assign n206 = ~i_27  & ~n205;
  assign n207 = ~i_28  & ~n206;
  assign sel_wb = ~i_28  & ~n207;
  assign sign = 1'b1;


  assign sel_reg_dst_0_1 = i_32;

  assign out = ~(sel_reg_dst_0 ^ sel_reg_dst_0_1);
endmodule
