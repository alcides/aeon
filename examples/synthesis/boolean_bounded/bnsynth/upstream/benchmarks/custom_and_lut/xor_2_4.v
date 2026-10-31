module formula(i_0,i_1,i_2,i_3,i_4,i_5,out);
	input i_0 ,i_1 ,i_2 ,i_3,i_4,i_5;
	output out;
	assign out = (((((i_0 ^ i_1) ^ i_2) ^ i_3) ^ i_4) ^ i_5);
endmodule
