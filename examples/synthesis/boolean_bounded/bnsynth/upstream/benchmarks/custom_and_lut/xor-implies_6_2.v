module formula(i_0,i_1,i_2,i_3,i_4,i_5,i_6, i_7,out);
	input i_0 ,i_1 ,i_2 ,i_3,i_4,i_5,i_6, i_7;
	output out;
	assign out = ((((((((i_0 ^ i_1) ^ i_2) ^ i_3) ^ i_4) ^ i_5) ^ i_6) ^ i_7)) & (~i_6 | i_7);
endmodule
