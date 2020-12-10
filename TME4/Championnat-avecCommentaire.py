#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Feb 28 16:50:19 2020

@author: Zixuan FENG & Arnaud DELOL
"""
import math
import re

#Exo2
#Q1
'''def cpt_k(ne,nj):
    k_value=set()
    for x in range(ne):
        for y in range(x+1,ne):
            for j in range(nj):
                kv=k(ne,nj,j,x,y)
                k_value.add(kv)
                print(x,y,j,kv)
                
                kv=k(ne,nj,j,y,x)
                print(y,x,j,kv)
                k_value.add(kv)
    return max(k_value)
'''

def cpt_k(ne,nj):
    return (nj-1)*(ne**2)+(ne-1)*ne+(ne-2)+1

#Q2
def k(ne,nj,j,x,y):
    return j*(ne**2)+x*ne+y+1

#Q3
def decoder(k,ne,nj):
    y=0
    x=0
    j=math.floor(k/(ne**2))
    k=k-j*(ne**2)
    
    if k%ne==0:
        y=ne-1
        x=int(k/ne)-1
    else:
        x=math.floor(k/ne)
        y=k-x*ne-1
    return j,x,y

#print(cpt_k(3,4))
#print(decoder(12,3,4))

#Exo3
#Q1.1
def auMoinsUn(l):
    return " ".join(map(str,l)) + " 0 \n"

l = [4,5,6,1,3]
print("au moins un")
print(auMoinsUn(l))

#Q1.2
def auPlusUn(l):
    s= ""
    for i in range(len(l)):
        for j in range(i+1,len(l)):
            s += "-" + str(l[i]) + " -" + str(l[j]) + " 0 \n"
    return s

l = [1,2,3]
print("au plus un")
print(auPlusUn(l))

#Q2.1
'''
    pour tout les j appartiennent a {0 , 1 , ... , nj-1},
    pour tout les x appartiennent a {0 , 1 , ... , ne-1}
    sum(m(jxy)+m(jyx))<=1
    ou y appartient a {0 , 1 , ... , ne-1}\{x}
    
    Il y a (nj*ne) contraintes de cardinalite.
'''

#Q2.2
def encoderC1(ne,nj):
    cpt = 0
    clauses = ""
    for j in range(nj):
        for x in range(ne):
            clausesEquipe = []
            for y in range(ne):
                if x != y:
                    cpt += 1
                    #print(str(j) + str(x) + str(y))
                    #print(str(j) + str(y) + str(x))
                    clausesEquipe.append(k(ne,nj,j,x,y))
                    clausesEquipe.append(k(ne,nj,j,y,x))
                    #print(clausesEquipe)
            clauses += auPlusUn(clausesEquipe)
            #print("clauses=",clauses)
    #print(cpt)
    #print("nombre de lignes/clauses: " + str(clauses.count("\n")))
    return clauses

#Q2.3
#Il y a (4*3=12) contraintes de cardinalite, donc 12*6=72 clauses au total.
print("EncoderC1")
#print(encoderC1(3,4))

#Q2.4
'''
    pour tout les x appartiennent a {0 , 1 , ... , ne-1}
    pour tout les y appartiennent a {0 , 1 , ... , ne-1}\{x}   #ne*(ne-1)/2 couples (x,y)
    sum(m(jxy))=1 and sum(m(jyx))=1                            #2 contraintes de cardinalite par couple
    ou j appartient a {0 , 1 , ... , nj-1}
    
    sum(m(jxy))=1    ==    (sum(m(jxy))>=1 and sum(m(jxy))<=1)
    
    sum(m(jxy))>=1  #1 clause
    sum(m(jxy))<=1  #nj*(nj-1)/2 clauses    
'''
'''
    ne*(ne-1) contraintes de cardinalite
    1+(nj*(nj-1)/2) clauses par contrainte
    donc, ((nj**2-nj+2)/2)*ne*(ne-1) clauses au total
'''


#Q2.5
def encoderC2(ne,nj):    
    clauses = ""
    for x in range(ne):
        for y in range(ne):
            clausesAuMoinsUn = []
            if x != y :
                for j in range(nj):
                    clausesAuMoinsUn.append(k(ne,nj,j,x,y))
                clauses += auMoinsUn(clausesAuMoinsUn)
                clauses += auPlusUn(clausesAuMoinsUn)
    #print("nombre de lignes/clauses: " + str(clauses.count("\n")))
    return clauses

print("encoderC2")
#print(encoderC2(3,4))

#Q2.6
'''
    nb(C1)+nb(C2)=(nj*ne)+ne*(ne-1)=ne*(nj+ne-1) contraintes
    pour 3 equipes sur 4 jours, il y a 3*(4+3-1)=18 contraintes
'''

#2.7
def encoder(ne,nj,filename):
    clauses = ""
    clauses = encoderC1(ne,nj)
    clauses += encoderC2(ne,nj)
    file = open(filename,"w")
    nbClauses = str(clauses.count("\n"))
    nbVar = str(cpt_k(ne,nj))
    text = "c test \nc \np cnf " + nbVar + " " + nbClauses + " \n" + clauses
    file.write(text)
    file.close
    #print(nbVar)
    #print(nbClauses)
    return clauses

print("encoder")
encoder(3,6,"test.cnf")

#Q3
'''
    s SATISFIABLE
    v -1 -2 -3 4 -5 -6 -7 -8 -9 -10 11 -12 -13 -14 -15 -16 -17 -18 -19 -20 21 -22 -23 -24 -25 -26 -27 -28 -29 -30 -31 -32 33 -34 -35 -36 -37 -38 -39 -40 -41 -42 43 -44 -45 -46 -47 -48 -49 -50 -51 -52 53 0
'''

#Q4
def decoderRes(resFile,equipesFile,ne,nj):
    equipeFile = open(equipesFile,"r")
    equipes = equipeFile.read().splitlines()
    
    res = open(resFile,"r+")
    resText = res.read().splitlines()
    res.truncate(0)
    
    solution = ""
    for line in resText:
        
        if line.lstrip().startswith("v"):
            solution = line
    if solution == "":
        return "UNSAT"

    solutionTab = solution.split(" ")
    solutionTab = solutionTab[1:-1] # pour enlever v et 0
    planning = []
    for v in solutionTab:
        if not v.startswith("-"):
            planning.append(decoder(int(v),ne,nj))
            
    #Ordre croissant par jour pas sûr que cela soit forcément nécessaire
    planning.sort(key=lambda tup: tup[0])
    print(planning)
    
    #Affichage du planning
    resPlanning = ""
    for match in planning:
        resPlanning += "Le jour " + str(match[0]) + " : l'équipe " + equipes[int(match[1])] + " joue à domicile contre " + equipes[int(match[2])]  + " \n"
    return resPlanning

#print("decoder")
#print(decoderRes("resfile","equipes",3,6))

import os
import time

#Q5
def script(ne,nj,equipesFile,filename,resFile):
    #filename = "fichierscript.cnf"
    #resFile = "resfile"
    encoder(ne,nj,filename)
    os.system("./glucose_static -model  " +filename + " >> "+ resFile)
    return decoderRes(resFile,equipesFile,ne,nj)
    
print(script(3,6,"equipes","fichierscript.cnf","resfile"))


#Exo 4: On itère jusqu'à ce que le retour ne soit plus UNSAT
def nbJours():
    resJours = []
    for ne in range(3,11):
        njMax=ne*(ne-1)
        for nj in range(1,njMax+1):
            start_time = time.time()
            res = script(ne,nj,"equipes","fichierscript.cnf","resfile")
            exec_time = time.time() - start_time

            if exec_time > 10:
                resJours.append("TIME OUT")
                break
            if res != "UNSAT":
                resJours.append(nj)
                break

    return resJours
 
print("Exercice 4")       
#print(nbJours())
''' 
Exercice 4:
    [6, 6, 'TIME OUT', 10, 'TIME OUT', 'TIME OUT', 'TIME OUT', 'TIME OUT']
    
    3 Equipes : 6 jours
    4 equipes : 6 jours
    5 equipes : TIME OUT
    6 equipes :  10 jours
    7 equipes : TIME OUT
    8 equipes :TO
    9 equipes : TO
    10 equipes : TO
'''

import itertools

#Exo5
#Q1
'''
1.(a)
    pour tout x appartient a {0 , 1 , ... , ne-1}
    sum(m(jyx))>=seuil
    ou y appartient a {0 , 1 , ... , ne-1}\{x}
       j appartient a {1 , 3 , ... , ceil(nj/2)}  #numero des dimanches
       seuil=(ne-1)*pext                          #nb de matchs a l'exterieur*pext
  (b)
    pour tout x appartient a {0 , 1 , ... , ne-1}
    sum(m(jxy))>=seuil
    ou y appartient a {0 , 1 , ... , ne-1}\{x}
       j appartient a {1 , 3 , ... , ceil(nj/2)}  #numero des dimanches
       seuil=(ne-1)*pdom                          #nb de matchs a domicile*pext
2.(a)
    pour tout x appartient a {0 , 1 , ... , ne-1}
    pour tout j appartient a {0 , 1 , ... , nj-1}
    m(j,a,x)+m(j+1,b,x)+m(j+2,c,x)<=2
    ou a,b,c appartiennent a {0 , 1 , ... , ne-1}\{x} et sont 2 a 2 different
  (b)
    pour tout x appartient a {0 , 1 , ... , ne-1}
    pour tout j appartient a {0 , 1 , ... , nj-1}
    m(j,x,a)+m(j+1,x,b)+m(j+2,x,c)<=2
    ou a,b,c appartiennent a {0 , 1 , ... , ne-1}\{x} et sont 2 a 2 different    
'''

#Q2
'''
    On généralise la méthode par paire utilisé avec k = 1 et taille des clauses = k+1 = 2
'''
def auPlusK(l,k):
    c = list(itertools.combinations(l,k+1))
    #print(c)
    s= ""
    for comb in c:
        for v in comb:
            s += "-" + str(v) + " "
        s += " 0 \n"
    return s

l = [1,2,3,4]
print("au plus k")
print(auPlusK(l,2))

#Q3
'''
Contrainte Dimanche :
    Dimanche = jour impair
    pour chaque equipe e,somme des var ou j est impair et y =e >= k
    donc sum not <= n -k
'''
def encoderDimanche(ne,nj,pext,pdom):     
    kext = math.ceil((ne-1)*pext) #nb matches a l'extérieur qui doivent avoir lieu le dimanche
    kdom = math.ceil((ne-1)*pdom) # nb matches à domicile qui doivent avoir lieu le dimanche
    # la somme des matches joués doivent être supérieur à ces k 
    # on fait donc la somme du contraire doit être inférieur à n - k

    clauses = ""
    for y in range(ne):
        clausesEquipeExt = []
        clausesEquipeDom = []
        for j in range(1,nj,2):
            for x in range(ne):
                if x != y:
                    print(j,"   ",x,"   ",y)
                    clausesEquipeExt.append(k(ne,nj,j,x,y))
                    clausesEquipeDom.append(k(ne,nj,j,y,x))
        #n1=n2=math.ceil(nj/2)*(ne-1)
        n1 = len(clausesEquipeExt)        
        clauses += auPlusK(clausesEquipeExt,n1-kext)
        n2 = len(clausesEquipeDom)
        clauses += auPlusK(clausesEquipeDom,n2-kdom)
        
    return clauses

print("encoderDimanche")
print(encoderDimanche(3,6,0.5,0.4))


def encoderAlter(ne,nj):
    #s'il y a <= 3 equipes, 
    #pas possible de jouer 3 matchs consecutifs ni a l'exterieur ni a domicile
    clauses=""
    if ne<=3:
        return clauses
    
    for x in range(ne):
        for j in range(nj-2):            
            resteEquipes=list(range(ne))
            resteEquipes.remove(x)
            couples = list(itertools.combinations(resteEquipes,3))
            for c in couples:
                clauseConsecExt=[]
                clauseConsecDom=[]
                clauseConsecExt.append(k(ne,nj,j,c[0],x))
                clauseConsecExt.append(k(ne,nj,j,c[1],x))
                clauseConsecExt.append(k(ne,nj,j,c[2],x))
                clauseConsecDom.append(k(ne,nj,j,x,c[0]))
                clauseConsecDom.append(k(ne,nj,j,x,c[1]))
                clauseConsecDom.append(k(ne,nj,j,x,c[2]))
                
                clauses+=auPlusK(clauseConsecExt,2)
                clauses+=auPlusK(clauseConsecDom,2)
    return clauses 
    
print("encoderAlter")
print(encoderAlter(4,6))

def encoder2(ne,nj,pext,pdom,filename):
    clauses = ""
    clauses = encoderC1(ne,nj)
    clauses += encoderC2(ne,nj)
    clauses += encoderDimanche(ne,nj,pext,pdom)
    clauses += encoderAlter(ne,nj)
    file = open(filename,"w")
    nbClauses = str(clauses.count("\n"))
    nbVar = str(cpt_k(ne,nj))
    text = "c test \nc \np cnf " + nbVar + " " + nbClauses + " \n" + clauses
    file.write(text)
    file.close
    return clauses

print("Encoder2")
encoder2(3,6,0.5,0.4,"test.cnf")
    
def script2(ne,nj,pext,pdom,equipesFile,filename,resFile):
    encoder2(ne,nj,pext,pdom,filename)
    os.system("./glucose_static -model  " +filename + " >> "+ resFile)
    return decoderRes(resFile,equipesFile,ne,nj)
    
print("Voici le planning pour 3 equipes sur 6 jour:")
print(script2(3,6,0.5,0.4,"equipes","test.cnf","resfile"))