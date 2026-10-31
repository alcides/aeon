module formula(i_0,i_1,i_2,i_3,i_4,out);
	input i_0 ,i_1 ,i_2 ,i_3 ,i_4;
	wire w1,w2,w3;
	output out;
	assign w1 = (i_0 | i_1);
	assign w2 = (i_2 & i_3);
	assign w3 = (w1 | w2);
	assign out = (w3 ^ i_4);
endmodule
