#include <stdlib.h>

#define TRUE 1
#define FALSE 0

typedef unsigned char bool;

#define NEW(howmany,type) (type *) calloc((unsigned) howmany, sizeof(type))
#define NIL(type) (type *) 0

#define CATEGORIE_STATIC 1

/* Etiquettes additionnelles pour les arbres de syntaxe abstraite.
 * Certains tokens servent directement d'etiquette. Attention ici a ne pas
 * donner des valeurs identiques a celles des tokens.
 */
#define NE	1	/* les operateurs de comparaison classiques */
#define EQ	2
#define LT	3
#define LE	4
#define GT	5
#define GE	6
#define UMINUS	7	/* '-' unaire */
#define UPLUS	8	/* '+' unaire */
#define STR	9	/* Constante de type String */
#define LIST	10	/* pour chainer des sequences d'expressions ou autres */
#define SELECT	11	/* acces a un champ non static */
#define ENVOI	12	/* appel de methode non static */
#define CSELECT 13	/* acces a un champ static */
#define CENVOI	14	/* appel de methode static */
#define LOCVAR	15	/* declaration de variable locale */
#define BLOCANO	16	/* Bloc sans etiquette explicite */
#define BLOCLAB	17	/* Bloc avec etiquette explicite */
#define YIELDANO  18    /* Sortie du bloc englobant */
#define YIELDLAB 19	/* Sortie de bloc nomme */
#define WHILEDO 20	/* while_do_ */
#define ITE	21	/* if_then_else_ */
#define ADD	22
#define MINUS	23
#define MUL	24
#define DIV	25
#define AND	26
#define PARAM 	27
#define RACINE	28
#define RACINE_CLASS	29
#define LISTARG 30

/* Codes d'erreurs */
#define NO_ERROR	0
#define USAGE_ERROR	1
#define LEXICAL_ERROR	2
#define SYNTAX_ERROR    3
#define CONTEXT_ERROR	40	/* default value for this stage */
#define DECL_ERROR	41	/* more precise information */
#define TYPE_ERROR	42
#define EVAL_ERROR	50
#define UNEXPECTED	10O

#define SIZE_ERROR 200
#define RED "\033[31m" /* Red */
#define BLACK "\033[30m" /* Black */

typedef struct _varDecl VarDecl, *VarDeclP;
typedef struct _methode Methode, *MethodeP;
typedef struct _class Class, *ClassP;
typedef enum _natureId natureId;

typedef enum {
  Unknown = 0, Local = 1, Global = 2, Param = 3, VarAtt = 4, Result = 5,
  Self = 6, Super = 7, Void = 8
} idKind;

enum natureId{
  Fonction, ParametreClasse, ParametreFon, Variable, BlocLable
};

typedef struct _varDecl {
  char *name;
  struct _class *type;		
  int categorie;	/* 1 -- static, 0 -- non static */
  struct _tree *init;	/*initialisation de la variable*/
  struct _varDecl *next;
  /*uniquement pour la generation du code*/
  int intStrObjet; /*1 -- int, 2--Str 3--Objet*/
} VarDecl, *VarDeclP;


/* la structure d'un arbre (noeud ou feuille) */
typedef struct _tree {
  short op;         /* etiquette de l'operateur courant */
  short nbChildren; /* nombre de sous-arbres */
  union {
    char *str;      /* valeur de la feuille si op = Id ou STR */
    int val;        /* valeur de la feuille si op = Cste */
    struct _method *fun; /* Feuille de type 'nom de fonction' */
    struct _class *pClass;
    struct _varDecl *lvar;
    struct _tree **children; /* tableau des sous-arbres */
  } u;
  /*utilise pour VC*/
  int isEnvoiMessage;
  int recupType;
  struct _tree *next;
} Tree, *TreeP;

typedef struct _listeTree {
  TreeP elem;
  struct _listeTree *next;
}listeTree, *LTreeP;


typedef struct _class
{ 
    char *name;
    int isFinal;
    int isExtend;
    struct _varDecl     *params; /*parametres de constructeur*/
    struct _varDecl     *lvar;  /*champs*/
    struct _methode     *methodeL;
    struct _tree    *constructor;
    struct _class   *classMere;
    struct _class *next;
    /*utilise pour VC*/
    struct _tree *appel_constructeur_mere; /*uniquement pour les checks*/
} Class, *ClassP;

typedef struct _methode
{ 
	char *name;
	int isStatic; /* 1 si vrai, 0 si non */
  	int isFinal;  /* 1 si vrai, 0 si non -- final */
  	int isRedef;  /* 1 si vrai, 0 si non  -- override*/
	struct _tree *corps;
	struct _class *typeRetour;	
	struct _varDecl *lvar;       /*liste de parametres d'une methode*/
    struct _class *classApp;    /*class d'appartenance de cette methode*/
    struct _methode *next;
} Methode, *MethodeP;


typedef struct _id
{
    char *name;
    enum natureId nature;
    struct _class *type;
    int profondeur;
    int rang;

    struct _id *next;
}Id, *IdP; 

typedef struct _erreur
{
  char* message;
  Class classe; /*La classe qui a une erreur*/
  Methode methode; /*La methode qui a une erreur */
  VarDecl variable; 
  int ligne;
  struct _erreur *next;
}Erreur,*ErreurP;


typedef union 
{
    char *S;
    char C;
    int I;
    struct _tree *pT;
    struct _varDecl *pV;
    struct _methode *pM;
    struct _class *pC;
}YYSTYPE;

/* Structure representant une liste de tree, utile pour la vérification
* des selections et des envois de message
*/

#define YYSTYPE YYSTYPE

extern ClassP classAnalysee;
extern TreeP racine;
extern ClassP listClass;
extern IdP listId;
extern ErreurP listeErreur;
extern VarDeclP listVar;

TreeP makeTree(short op, int nbChildren, ...);
TreeP makeLeafInt(short op, int val);
TreeP makeLeafStr(short op, char *str);
TreeP makeLeafLVar(short op, VarDeclP lvar);
TreeP getChild(TreeP tree, int rank);

void pprint(TreeP tree);
void printVar(VarDeclP var);
void printMethode(MethodeP methode);
void printClasse(ClassP classe);
void pprintTreeMain(TreeP tree);

void afficheListeErreur(ErreurP listeE);
void pushErreur(char* message,ClassP classe,MethodeP methode,VarDeclP variable);

/*-------------------partie verification contextuelle-----------------------*/
bool estDansListClasse(ClassP listeClasse, char *nom);
ClassP makeDefClasse(char *nom, int final, VarDeclP params);
ClassP checkAndDefineClasse(char *nom, int final, VarDeclP params, ClassP classAnalysee);
ClassP makeClasseApresDef(ClassP res,TreeP corps_constructeur,MethodeP liste_methodes, VarDeclP liste_champs, ClassP classe_mere, int isExtend);
bool varEstDansListe(VarDeclP listeVar, char *nom);
VarDeclP copyVar(VarDeclP var);
VarDeclP makeListVar(char *nom, ClassP type, int cat, TreeP init);
IdP makeId(char *name, enum natureId nature, ClassP type, int profondeur, int rang);
bool addId(IdP liste, IdP id);
bool checkIdExiste(IdP id);
bool checkIdVarExisteParNom(char *name);
bool checkIdBlocExisteParNom(char *name);
ClassP getTypeIdVar(char *name);
ClassP getTypeIdBloc(char *name);
bool checkIdBlocExiste(IdP id);
void moveIdFromListParProfondeur(int profon);
void moveIdBlocFromListParProfondeur(int profon);
ClassP getClasse(ClassP listeClass, char *nom);
ClassP getClasseCopie(ClassP listeClass, char *nom);
bool memeVar(VarDeclP var1, VarDeclP var2);
MethodeP getMethode(ClassP classe, MethodeP methode);
MethodeP makeMethode(char *nom, int staticOpt, int finalOpt, int redefOpt, TreeP corps, ClassP typeRetour, VarDeclP params, ClassP classApp);
ClassP makeClasse(ClassP classDef, ClassP classe_mere, VarDeclP varL, MethodeP methodeL, TreeP constructeur);
VarDeclP makeChamp(int staticOpt, VarDeclP param, TreeP init);
ClassP makeClassePredefinie(char *nom, VarDeclP params,TreeP corps_constructeur,MethodeP liste_methodes,VarDeclP liste_champs, ClassP classe_mere, int isExtend, int Final);

bool checkProgramme(TreeP prog);
bool checkClass(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl);
bool checkHeritage(ClassP classe);
bool classExtendsDeclareeAvant(ClassP actuelle,ClassP heritee);
bool checkListAttribut(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl);
bool verifAttributClasse(ClassP classe);
ClassP getType(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl);
bool equalsType(ClassP gauche, ClassP droite);
bool isHeritage(ClassP gauche, ClassP droite);
ClassP getTypeAttribut(char* nom, ClassP classe, MethodeP methode, VarDeclP listeDecl, bool isStatic, bool agerer);
bool checkDoublon(char** variable,int n);
bool compareParametreMethode(VarDeclP declaration, TreeP appelMethode, ClassP classe, MethodeP methode, VarDeclP listeDecl, char* nom);
LTreeP transFormSelectOuEnvoi(TreeP arbre, LTreeP liste);
ClassP estCoherentEnvoi(LTreeP liste, ClassP classe, MethodeP methode, VarDeclP listeDecl);
ClassP transformerAppel(TreeP appelMethode, ClassP liste, ClassP courant, MethodeP methode, VarDeclP listeDecl);
ClassP appartient(ClassP mere, TreeP fille, bool isEnvoiMessage, MethodeP methode, VarDeclP listeDecl, LTreeP tmp,short etiquette, bool isStatic, bool agerer);
ClassP getTypeMethode(char * nom, ClassP classe, short precedant, TreeP appelMethode, MethodeP methode, VarDeclP listeDecl, bool isStatic);
bool checkListMethode(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl);
bool checkMethode(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl);
bool checkListOptArg(VarDeclP var, MethodeP methode);
bool methodeDansClasse(ClassP classe, MethodeP methode);
bool finalMethode(ClassP classe, MethodeP methode);
bool checkBloc(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc);
bool checkConstructeurExtends(VarDeclP parames, TreeP appelMethode, ClassP classe, MethodeP methode, VarDeclP listeDecl, char *nom);
bool checkUneDeclarationDansBloc(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc);
bool checkUneExprDansBloc(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc);
bool checkEListSuite(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc);


/*-------------------partie generation du code-----------------------*/
#define FLAG_INT 1
#define FLAG_STR 2
#define FLAG_OBJ 4
#define FLAG_FONC 8

typedef struct _etiquette
{
    char *name;
    int position;
    int flag;       /* FLAG_INT 1; FLAG_STR 2; FLAG_OBJ 4; FLAG_FONC 8*/
    char *typeCID;
    struct _etiquette *next;
}Etiquette, *EtiquetteP;

#define ENV_CLASS 0
#define ENV_OBJ 1 

typedef struct _envClass
{
    char *name;
    char *CIDName;
    int positionGP;
    int nbChamp;
    EtiquetteP p_etiquette;
    bool flag;      /* FLAG_CLASS 0 FLAG_OBJ 1*/
    struct _envClass *next;
}EnvClass,*EnvClassP;

typedef struct _bloc
{
    char *nom;
    int indice;
    struct _bloc *next;
}Bloc,*BlocP;

/*------------------------------------------*/

/*---------------init.h--------------------*/
void generation_addint(int fp);
void generation_subint(int fp);
void generation_mulint(int fp);
void generation_divint(int fp);
void generation_concat(int fp);
void generation_classList(int fp, ClassP classListe);
void generation_lesFonction(int fp, ClassP classListe);
void generation_bloc(int fp, TreeP crops, char *fonctionName, bool flag,EnvClassP listeVarEnv);
void init_generation(int fp, ClassP classListe);
void generation_class(int fp, ClassP p_class);
void generation_fonctionListe(int fp, char *className, MethodeP p_methode);
void generation_fonction(int fp, char *className, MethodeP p_methode);
int getNbFonction(ClassP p_cls);
void generationCode(TreeP racine, ClassP listeClass,char *filepath);
EnvClassP generation_Inst(int fp, TreeP tree ,int *nbVar,EnvClassP listeVarEnv);
void generation_expr(int fp, TreeP tree,EnvClassP listeVarEnv);
/*----------------------------------------*/


/*class_envir.h*/
EnvClassP creerEnvClass(ClassP listeClass);
void creerEtiquetteL(ClassP tempClass, EnvClassP tempEnvClass);

/* retourner l'element final de la liste*/
EtiquetteP creerEtiquetteVarL(ClassP p_class, EnvClassP p_envClass, int *nbChamp);
EtiquetteP creerEtiquetteMethodeL(ClassP p_class, EnvClassP p_envClass, int *nbChamp);

EnvClassP getEnvClass(char *nom, EnvClassP tete);
int getClassIndiceGP(char *nom, EnvClassP tete);
int getChampIndice(char *name, EnvClassP p_envClass);
/*-------------------------------------------*/


/*------------------------------------------*/
int getBlocIndice(BlocP tete, char *nom);
BlocP pushEtiquetteBlocLabel(BlocP tete, char *nom);
BlocP pushEtiquetteBlocAnonym(BlocP tete);
EnvClassP pushVar(int fp, EnvClassP envir, EnvClassP tete, char *nom, char *typeCID);
EnvClassP popVar(int fp,EnvClassP tete,int popNb);