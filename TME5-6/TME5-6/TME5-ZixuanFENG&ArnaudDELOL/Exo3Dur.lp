row(0..8).
col(0..8).
val(1..9).

%faits
case(0,0,8).

case(1,2,3).
case(1,3,6).

case(2,1,7).
case(2,4,9).
case(2,6,2).

case(3,1,5).
case(3,5,7).

case(4,4,4).
case(4,5,5).
case(4,6,7).

case(5,3,1).
case(5,7,3).

case(6,2,1).
case(6,7,6).
case(6,8,8).

case(7,2,8).
case(7,3,5).
case(7,7,1).

case(8,1,9).
case(8,6,4).

%chaque case contient qu'une seul valeur
1{case(I,J,V):val(V)}1 :- row(I),col(J).
%chaque valeur apparait une seule fois dans chaque ligne
1{case(I,J,V):col(J)}1 :- row(I),val(V).
%chaque valeur apparait une seule fois dans chaque colonne
1{case(I,J,V):row(I)}1 :- col(J),val(V).

%chaque valeur apparait une seule fois dans chaque region
:-case(I,J1,V),case(I,J2,V),J1/3==J2/3,J1!=J2.
:-case(I1,J,V),case(I2,J,V),I1/3==I2/3,I1!=I2.
:-case(I1,J1,V),case(I2,J2,V),I1/3+3*(J1/3)==I2/3+3*(J2/3),I1!=I2,J1!=J2.

#show case/3.
