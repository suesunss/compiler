%token AFF IS CLASS VAR EXTENDS DEF STATIC OVERRIDE RETURNS YIELD IF THEN ELSE
%token KNEW FINAL WHILE DO
%token <S> ID CID String
%token <I> Cste
%token <C> RELOP
%token High

%right ';'
%right THEN ELSE DO AFF 
%nonassoc YIELD
%nonassoc RELOP
%left '&'
%left '+' '-'
%left '*' '/'
%left High

%type <I> Prog finalOpt staticOpt overOpt OptSM
%type <pT> initOpt block blockOpt d expr eList eListOpt envoi cible ArgLOpt ArgL  
%type <pV>  varDecl varDeclLOpt paramL paramLOpt param
%type <pC> classHeader superClassOpt class classL
%type <pM> methodeLOpt methodDecl funcID


%{
#include "tp.h"
#include "tp_y.h"

extern int yylex();
extern void yyerror(char *);

ClassP classAnalysee; /* Une variable globale -- point sur la classe qui est en cours d'analyse */
ClassP racineClass=NIL(Class);
TreeP racine=NIL(Tree);
IdP listId = NIL(Id);

extern int compile(TreeP mainBlock);
%}

%%
Prog : classL AtMain block 
{ 
	$$ = compile($3);
	TreeP classeLNode = NEW(1,Tree);
	classeLNode->op = RACINE_CLASS;
	classeLNode->u.pClass = $1;
	racine = makeTree(RACINE,3,classeLNode,NIL(Tree),$3);
	racineClass = $1;
}
;

AtMain :
;


/* s'arranger pour avoir la liste des classes definies (et aussi les classes predefinies ?) */
classL :
{	$$ = NIL(Class);}
| class classL
{	$1->next = $2;
	$$ = $1;
}
;

/* si on ne l'a pas deja fait directement dans les productions, enregistrer ici les
 * composants dans la structure qui represente la classe
 */

class : classHeader superClassOpt IS '{' varDeclLOpt methodeLOpt blockOpt '}'
{	
	$1 = makeClasse($1, $2, $5, $6, $7);
	$$ = $1;
}
; 

classHeader : finalOpt CLASS CID '(' paramLOpt ')'
{
	$$ = checkAndDefineClasse($3, $1, $5, classAnalysee);
}
;

finalOpt : 
{ $$ = FALSE; }
| FINAL	   
{ $$ = TRUE; }
;

superClassOpt :
{	$$ = NIL(Class);}
| EXTENDS CID '('  ArgLOpt ')'
{	
	$$ = getClasseCopie(listClass, $2);
	/*pClass->classMereParams=$4;*/
}
;


blockOpt :   
{ $$ =  makeTree(BLOCANO, 3, NIL(Tree), NIL(Tree), NIL(Tree)); }
| block     
{ $$ = $1; }
;

/* nom du bloc et type de retour du yield */
block : 
'{' ID ':' CID  '|' eListOpt '}'
{ $$ = makeTree(BLOCLAB, 3, makeLeafStr(ID, $2), makeLeafStr(CID, $4), $6); }
|'{' eListOpt '}'
{ $$ = makeTree(BLOCANO, 3, NIL(Tree), NIL(Tree), $2); }
;

/* chainer les champs ou les enregistrer directement dans la bonne structure
 * ou creer une (nouvelle) structure pour transmettre à al fois la liste des
 * champs et la liste des methodes.
 */
 
varDeclLOpt :
{	$$ = NIL(VarDecl);}
| varDecl varDeclLOpt
{	
	$1 ->next=$2;
	$$ = $1;
}
;

varDecl :  VAR staticOpt param initOpt ';'
{ 	
	$$ = makeChamp($2, $3, $4);
}
;


/* chainer les methodes ou les enregistrer directement dans la bonne structure */
methodeLOpt :
{	$$ = NIL(Methode);}
| methodDecl methodeLOpt
{	
	$1 ->next = $2;
	$$ =$1;
}
;



staticOpt : 
{ $$ = FALSE; }
| STATIC    
{ $$ = TRUE; }
;


initOpt :       { $$ = NIL(Tree); }
|  AFF expr       
{ /* Ici pour l'instant on n'a pas la partie gauche de l'affectation !
   * Faudra la raccorder a l'endroit ou la production est utilisee.
   */
  $$ = makeTree(AFF, 2, NIL(Tree), $2);
}
;

methodDecl : DEF staticOpt finalOpt overOpt funcID block
{	
	$5->isStatic=$2;
	$5->isFinal=$3;
	$5->isRedef=$4;
	$5->corps= $6;
	$$ = $5;
}
;


overOpt :   { $$ = FALSE; }
 | OVERRIDE { $$ = TRUE; }
;


funcID : ID '(' paramLOpt ')' RETURNS CID
{	
	MethodeP pMeth=NEW(1,Methode);
	pMeth->name = $1;
	pMeth->lvar = $3;
	pMeth->typeRetour = getClasseCopie(listClass, $6);
	pMeth->classApp = classAnalysee;
	$$ = pMeth;
}
;

paramLOpt :	
{ 	$$ = NIL(VarDecl); }
| paramL	
{ 	$$ = $1; }
;


paramL : 
 param  	
{ 	$$ = $1;}
| param ',' paramL 	
{ 	
	$1->next = $3;  
	$$ = $1;
}
;


param : ID ':' CID	
{	VarDeclP res = NEW(1, VarDecl);
  	res->name = $1; 
	res->type = getClasseCopie(listClass, $3);
	$$ = res;
 }
;


expr : expr '+' expr		
{ $$ = makeTree(ADD, 2, $1, $3); }
| expr '-' expr		
{ $$ = makeTree(MINUS, 2, $1, $3); }	
| expr '*' expr		
{ $$ = makeTree(MUL, 2, $1, $3); }	
| expr '/' expr		
{ $$ = makeTree(DIV, 2, $1, $3); }	
| '+' expr %prec High
{ $$ = makeTree(UPLUS, 1, $2);}
| '-' expr %prec High	
{ $$ = makeTree(UMINUS, 1, $2); }
| expr '&' expr		
{ $$ = makeTree(AND, 2, $1, $3); }	
| expr RELOP expr  	 	
{ $$ = makeTree($2, 2, $1, $3); }	
| KNEW CID '(' ArgLOpt ')' 
{ $$ = makeTree(KNEW, 2, makeLeafStr(CID, $2), $4); }
| envoi			
{ $$ = $1; }
| IF expr THEN expr ELSE expr	
{ $$ = makeTree(ITE, 3, $2, $4, $6); }
| IF expr THEN expr		
{ $$ = makeTree(ITE, 3, $2, $4, NIL(Tree)); }
| WHILE expr DO expr		
{ $$ = makeTree(WHILEDO, 2, $2, $4); }
| cible AFF expr 		
{ $$ = makeTree(AFF, 2, $1, $3); }
| YIELD ID ':' expr %prec YIELD
{ $$ = makeTree(YIELDLAB, 2, makeLeafStr(ID, $2), $4); }
| YIELD expr %prec YIELD	
{ $$ = makeTree(YIELDANO, 2, NIL(Tree), $2); }
;



eListOpt : 
{ $$ = makeTree(LIST, 2, makeLeafStr(ID, "void"), NIL(Tree)); }
| 	eList 
{ $$ = $1; }
;

eList : 
	d OptSM
{ 
	TreeP exp;
  	if ($2) exp = NIL(Tree);
  	else exp = makeTree(LIST, 2, makeLeafStr(ID, "void"), NIL(Tree));
  	$$ = makeTree(LIST, 2, $1, exp);
}
| 	d ';' eList	
{ $$ = makeTree(LIST, 2, $1, $3); }
;

OptSM : 
{ $$ = TRUE; }
| 	';'  
{ $$ = FALSE; }
;

d: VAR param initOpt 
{ 
	TreeP pTree = NEW(1,Tree);
	pTree->op = PARAM;
	pTree->nbChildren = 0;
	pTree->u.lvar = $2;
	$$ = makeTree(LOCVAR, 2, pTree, $3); 
}
| expr		     { $$ = $1; }
;

envoi : 	
	String   
{ $$ = makeLeafStr(STR, $1); }
| 	Cste		 
{ $$ = makeLeafInt(Cste, $1); }
| 	cible	 	 
{ $$ = $1; }
| 	block          
{ $$ = $1; }
| 	CID '.' ID '(' ArgLOpt ')' 
{ $$ = makeTree(CENVOI, 3,  makeLeafStr(CID, $1), makeLeafStr(ID, $3), $5); }
| 	envoi '.' ID '(' ArgLOpt ')'
{ $$ = makeTree(ENVOI, 3, $1, makeLeafStr(ID, $3), $5); }
;


cible :
	ID	
{ $$ = makeLeafStr(ID, $1); }
| 	envoi '.' ID	
{ $$ = makeTree(SELECT, 2, $1, makeLeafStr(ID, $3)); }
| 	CID '.' ID 
{ $$ = makeTree(CSELECT, 2, makeLeafStr(CID, $1), makeLeafStr(ID, $3)); }
| 	'(' expr ')'
{ $$ = $2; }
;


ArgLOpt :	
{ $$ = NIL(Tree); }
| 	ArgL	
{ $$ = $1; }
;


ArgL : 	expr	
{ $$ = makeTree(LISTARG, 2, $1, NIL(Tree)); }
| 	expr ',' ArgL    
{ $$ = makeTree(LISTARG, 2, $1, $3); }
;

