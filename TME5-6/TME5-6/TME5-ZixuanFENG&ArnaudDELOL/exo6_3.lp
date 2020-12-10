#const ne=4.

equipe(1..ne).
numJ(1..10).
1{nj(1..8)}1.
jour(J):-nj(NJ),numJ(J),J>=1,J<=NJ.

%match(Jour,Domicile,Exterieur) , maximum un match par jour pour une equipe, chaque equipe doit jouer toutes les autres equipes deux fois (dom et ext)

%pour chaque couple (E1,E2), ils jouent une fois chez E1 et une fois chez E2
1{match(J,E1,E2):jour(J)}1 :- equipe(E1),equipe(E2),E1 != E2.
1{match(J,E2,E1):jour(J)}1 :- equipe(E1),equipe(E2),E1 != E2.

%chaque equipe joue un seul match par jour
:-match(J,E,E1),match(J,E,E2),E1!=E2.
:-match(J,E,E1),match(J,E2,E).
:-match(J,E1,E),match(J,E2,E),E1!=E2.

% contrainte d'équilibre
% Match le dimanche

#const pext=50.
((ne-1)*pext/100){match(J,E1,E):jour(J),equipe(E1),J\2==0}:-equipe(E).
#const pdom=40.
((ne-1)*pdom/100){match(J,E,E1):jour(J),equipe(E1),J\2==0}:-equipe(E).

% Deux match à lextérieur de suite sont autorisés mais pas plus
1{match(J,E,E4):jour(J),J>J1,J<J3,equipe(E4)}:-equipe(E),match(J1,E1,E), match(J2,E2,E), match(J3,E3,E),J1 < J2,J2 < J3.
1{match(J,E4,E):jour(J),J>J1,J<J3,equipe(E4)}:-equipe(E),match(J1,E,E1), match(J2,E,E2), match(J3,E,E3),J1 < J2,J2 < J3.

#minimize{NJ:nj(NJ)}.
#show  match/3.
