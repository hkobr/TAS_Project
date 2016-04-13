--------------------------- Projet TAS ----------------------------------

Auteurs : 
Hassan Kobrosli
Mohamed-Amin Affes

Options :
-trace

-concrete

-constant

-interval : Domaine des intervalles

-disjonctivecompletion : Extension du domaine des intervalles par complétion disjonctive

-delay n : n du type int, permet de faire join pendant n tours de boucle avant de faire l'élargissement (widen)

-unroll n : n du type int, permet de dérouler la boucle n fois

3.1.1 :

_ Sémantique de rand(l,h) : Si l>h, rand renvoie bottom, si l<=h, un nombre de [l, h]

_ L'exécution d'un programme s'arrête si le programme arrive à la fin ou si l'instruction halt est appelée.

_ Si le programme comporte une boucle infinie, le programme s'arrête si il y a présence d'un point fixe.


3.1.3 :

L'ajout du modulo a été choisi. Des Tokens ont été ajoutés dans le lexer et le parser. Ajout de la prise en compte du modulo dans l'AST.

Finalement, ajout du modulo dans les différents domaines de valeurs.

4 :

L'extension choisie est la complétion disjonctive. Pour cela, nous définissons un nouveau domaine dont le type t est récursif et est soit bottom, soit un intervalle, soit une union de deux objets de type t.
Cela donne une meilleure précision dans les programmes composés de "if" dont la condition repose sur la valeur de l'instruction rand. Par exemple, dans le programme 

{
int x;
int y;
x = rand(0,10);
y = rand(0,1);
if(y==0){
	x = -x;
}
print(x,y);
}

x aura pour valeur [0,10] U [-10,0] dans ce nouveau domaine.
Dans le domaine des intervalles, x avait pour valeur [-10,10].