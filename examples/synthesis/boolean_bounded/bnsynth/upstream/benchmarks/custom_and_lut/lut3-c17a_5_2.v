module formula(i0,i1,i2,i3,i4, i5, i6, out);
	input i0,i1,i2,i3,i4, i5, i6;
	output out;
	wire N10,N11,N16,N19, N22_1, N22_2, N23_1, N23_2;

	assign N10 = ~(i0 & i2);
	assign N11 = ~(i2 & i3);
	assign N16 = ~(i1 & N11);
	assign N19 = ~(N11 & i4);
	assign N22_1 = ~(N10 & N16);
	assign N23_1 = ~(N16 & N19);

	assign N22_2 = ~(N10 & i5);
	assign N23_2 = ~(i5 & i6);

	assign out = ~(N22_1 ^ N22_2);

endmodule
