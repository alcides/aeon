module formula(i_0,i_1,i_2,i_3,out);
	input i_0 ,i_1 ,i_2 ,i_3;
	wire w1,w2;
	output out;
	assign w1 = (i_0 ^ i_1);
	assign w2 = (i_2 ^ i_3);
	assign out = (w1 ^ w2);
endmodule
