module formula(i_0,i_1,i_2,i_3, i_4, i_5, i_6, i_7, i_8, i_9, out);
	input i_0, i_1,i_2,i_3, i_4, i_5, i_6, i_7, i_8, i_9;
	output out;
	wire w1, w2, w3, w4, w5;
	assign w1 = (~i_0 | i_5) & (i_0 | ~i_5);
	assign w2 = (~i_1 | i_6) & (i_1 | ~i_6);
	assign w3 = (~i_2 | i_7) & (i_2 | ~i_7);
	assign w4 = (~i_3 | i_8) & (i_3 | ~i_8);
	assign w5 = (~i_4 | i_9) & (i_4 | ~i_9);
	assign out = ((((w1 & w2) & w3) & w4) & w5);
endmodule
