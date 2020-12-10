% Remplacer le nb de couleur et de noeud par des variables qu'on initialise en entrée de programme
noeud(1..7).
couleur(1..4).


%faits les aretes de l'exemple 
arete(1,2).
arete(1,3).
arete(1,5).
arete(2,3).
arete(2,4).
arete(2,6).
arete(3,4).
arete(3,5).
arete(3,6).
arete(4,5).
arete(4,6).
arete(5,6).
arete(5,7).
arete(6,7).

% Au maximum, une couleur par noeud puis on ne doit pas avoir la meme association avec une couleur si arete entre 2 noeuds
1{association(N,V):couleur(V)}1 :- noeud(N).
:- association(N1,V), association(N2,V), arete(N1,N2).
:- association(N1,V), association(N2,V), arete(N2,N1).

#show association/2.
