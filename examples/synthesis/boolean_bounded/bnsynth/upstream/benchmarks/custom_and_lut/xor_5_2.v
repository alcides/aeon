module formula(i_0,i_1,i_2,i_3,i_4,i_5,i_6,out);
	input i_0 ,i_1 ,i_2 ,i_3,i_4,i_5,i_6;
	output out;
	assign out = ((((((i_0 ^ i_1) ^ i_2) ^ i_3) ^ i_4) ^ i_5) ^ i_6);
endmodule
