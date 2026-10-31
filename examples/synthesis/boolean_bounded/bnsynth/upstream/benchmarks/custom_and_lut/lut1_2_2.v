module formula(i0,i1,i2,i3,out);
	input i0,i1,i2,i3;
	output out;
	wire w1, w2, w3, h, o1;

	assign w1 = (((i0 ^ i1) ^ i2) ^ i3);
	assign w2 = (i0 & ~i1);
	assign w3 = (w2 | ~i1);

	assign out = ~(w1 ^ w3);

endmodule
