row(1..8).
col(1..8).
8{queen(I,J):row(I),col(J)}8.
:-queen(I,J1),queen(I,J2),J1!=J2.
:-queen(I1,J),queen(I2,J),I1!=I2.
:-queen(I1,J1),queen(I2,J2),I1!=I2,J1!=J2,I1-J1==I2-J2.
:-queen(I1,J1),queen(I2,J2),I1!=I2,J1!=J2,I1+J1==I2+J2.
queen(1,1).
:-queen(4,4).

#show queen/2.
