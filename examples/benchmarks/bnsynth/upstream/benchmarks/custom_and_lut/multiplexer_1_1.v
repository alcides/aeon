module formula(i_0,i_1, out);
	input i_0, i_1;
	output out;
	assign out = ((i_1)) & (~i_1 | i_0);
endmodule
