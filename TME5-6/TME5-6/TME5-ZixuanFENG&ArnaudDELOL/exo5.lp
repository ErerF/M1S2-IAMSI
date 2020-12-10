nationalite(britannique;suedois;danois;norvegien;allemand).
boisson(the;cafe;lait;biere;eau).
cigarette(pallMall;dunhill;blend;bluemaster;princess).
animal(chien;poisson;chat;cheval;oiseau).
couleur(rouge;verte;blanche;jaune;bleue).
maison(1..5).


%faits
habiter(britannique,rouge).
garder(suedois,chien).
boire(danois,the).

% en interpretant le "à gauche" par "à gauche mais peut etre pas le voisin directement à cote" on obtient 7 answers sets donc on a restreint à seulement au voisin directement à cote pour avoir qu'une seule solution
:- habiter(X,verte),habiter(Y,blanche),position(X,P1),not position(Y,P1+1).

:- habiter(X,verte), not boire(X,cafe).

:- fumer(X,pallMall), not garder(X,oiseau).

:- habiter(X, jaune), not fumer(X,dunhill).

:- position(X,3), not boire(X,lait).

position(norvegien,1).

% si la position de celui qui fume des blend n'est pas +1 et n'est pas -1 de celle qui garde des chats, la solution n'est pas bonne

:- fumer(X,blend), garder(Y, chat),position(Y,P), not position(X,P-1), not position(X,P+1).

:- garder(X, cheval), fumer(Y, dunhill), position(Y,P), not position(X,P-1), not position(X,P+1).

:- fumer(X,bluemaster), not boire(X,biere).

fumer(allemand,princess).

:- habiter(X, bleue),position(X,P), not position(norvegien,P-1), not position(norvegien,P+1).

:- fumer(X,blend), position(X,P), boire(Y,eau), not position(Y,P-1), not position(Y,P+1).


1{boire(N,B):boisson(B)}1 :- nationalite(N).
1{boire(N,B):nationalite(N)}1 :- boisson(B).

1{fumer(N,C):cigarette(C)}1 :- nationalite(N).
1{fumer(N,C):nationalite(N)}1 :- cigarette(C).

1{garder(N,A):animal(A)}1 :- nationalite(N).
1{garder(N,A):nationalite(N)}1 :- animal(A).

1{habiter(N,A):couleur(A)}1 :- nationalite(N).
1{habiter(N,A):nationalite(N)}1 :- couleur(A).

1{position(N,A):maison(A)}1 :- nationalite(N).
1{position(N,A):nationalite(N)}1 :- maison(A).

recap(N,B,C,A,O,P) :- boire(N,B),fumer(N,C),garder(N,A),habiter(N,O),position(N,P).

%on veut voir les animaux pour voir celui qui a des poissons

#show recap/6.
