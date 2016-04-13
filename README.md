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
-delay n : n du type int
-unroll n : n du type int

3.1.1 :
_ Sémantique de rand(l,h) : Si l>h, rand renvoie bottom, si l<=h, un nombre de [l, h]
_ arrive à la fin, soit halt
_ seulement sil présence d'un point infixe


3.1.3 :
L'ajout du modulo a été choisi. Des Tokens ont été ajoutés dans le lexer et le parser. Ajout de la prise en compte du modulo dans l'AST.
Finalement, ajout du modulo dans les différents domaines de valeurs.

4 :
L'extension choisie est la complétion disjonctive. Pour cela, nous définissons un nouveau domaine dont le type t est récursif et est soit bottom, soit un intervalle, soit une union de deux objets de type t.
En résulte une meilleure précision, notamment 