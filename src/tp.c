#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include "tp.h"
#include "tp_y.h"

extern char *strdup(const char *s);
extern int yyparse();
extern int yylineno;

int profondeur;
int rang;

/*---------------------------------*/
int nbEtiquette=0;
BlocP blocTete=NULL;
int nbFpVariable=0;
EnvClassP listeClassEnv=NULL;
int nbITELabelIndice=0;
int nbWhileLabelIndice=0;
/*---------------------------------*/


bool dansCheckBlocMain = FALSE;
/* Les en-tetes de ces fonctions peuvent etre adaptes si besoin */
extern void prologue();
extern int runVC(TreeP mainExp);
extern int genCode(TreeP mainExp);
extern void checkReservedId(char *name, char *context);

int compile(TreeP mainExp);

ClassP listClass = NIL(Class);   /* Liste de toutes les classe declarees dans le programme */
ErreurP listeErreur = NIL(Erreur); /*Liste des erreurs*/
VarDeclP listVar = NIL(VarDecl);    /*liste des variables*/


/* Niveau de 'verbosite'.
 * Par defaut, n'imprime que le resultat et les messages d'erreur
 */
bool verbose = FALSE;

/* Verif. contextuelles ou pas. Par defaut, on les effectue */
bool noVC = FALSE;

/* Generation de code ou pas. Par defaut, on produit le code */
bool noCode = FALSE;

/* Pose de points d'arret ou pas dans le code produit */
bool debug = FALSE;

/* code d'erreur a retourner */
int errorCode = NO_ERROR;

char *filePath;


int main(int argc, char **argv) {

  int fi;
  int i, res;

  for(i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      switch (argv[i][1]) {
      case 'd': case 'D':
	       debug = TRUE; continue;
      case 'v': case 'V':
	       verbose = TRUE; continue;
      case 'e': case 'E':
	       noCode = TRUE; continue;
      case 'c': case 'C':
	       noVC = TRUE; continue;
      case '?': case 'h': case 'H':
      	fprintf(stderr, "Appel: tp -v -c -e -d -o file.out programme.txt\n");
      	exit(USAGE_ERROR);
      case'o':
        filePath=argv[++i];
        break;
      default:
      	fprintf(stderr, "Option inconnue: %c\n", argv[i][1]);
      	exit(USAGE_ERROR);
      }
    } else break;
  }

  if (i == argc) {
    fprintf(stderr, "Fichier programme manquant\n");
    exit(USAGE_ERROR);
  }

  if ((fi = open(argv[i++], O_RDONLY)) == -1) {
    fprintf(stderr, "erreur: Cannot open %s\n", argv[i-1]);
    exit(USAGE_ERROR);
  }

  /* redirige l'entree standard sur le fichier... */
  close(0); dup(fi); close(fi);

  /* pour d'eventuelles choses a faire AVANT de lancer l'analyseur
   * syntaxique (initialisations de strucutres ou var. globales par exemple.
   */
  prologue();

  /* lance l'analyse syntaxique et donc les actions semantiques associees
   * aux productions. yyparse renvoie une valeur non nulle en cas d'erreur
   * de syntaxe. 
   * Ici on suppose que les verifications contextuelles et la generation de
   * code seront effectuees via la fonction 'compile' qui sera lancee par
   * l'action semantique de la regle associee a l'axiome.
   */
  res = yyparse();

  if(res == 1)  exit(0);

  bool vc = TRUE;
  if(!noVC)
  {
    vc = runVC(racine);
    afficheListeErreur(listeErreur); 
  }

  if(vc == 1 && !noCode)
  {
    generationCode(racine,listClass, filePath);
  }

  return 0;
}


void setError(int code) {
  errorCode = code;
  if (code != NO_ERROR) { noCode = TRUE; /* abort(); */ }
}


/* yyerror:  fonction importee par Bison et a fournir explicitement. Elle
 * est appelee quand Bison detecte une erreur syntaxique.
 * Ici on se contente d'un message minimal.
 */
void yyerror(char *ignore) {
  printf("erreur de syntaxe: Ligne %d\n", yylineno);
  setError(SYNTAX_ERROR);
}


/* Tronc commun pour la construction d'arbre */
TreeP makeNode(int nbChildren, short op) {
  TreeP tree = NEW(1, Tree);
  tree->op = op;
  tree->nbChildren = nbChildren;
  tree->u.children = nbChildren > 0 ? NEW(nbChildren, TreeP) : NIL(TreeP);
  return(tree);
}


/* Construction d'un arbre a nbChildren branches, passees en parametres */
TreeP makeTree(short op, int nbChildren, ...) {
  va_list args;
  int i;
  TreeP tree = makeNode(nbChildren, op); 
  va_start(args, nbChildren);
  for (i = 0; i < nbChildren; i++) { 
    tree->u.children[i] = va_arg(args, TreeP);
  }
  va_end(args);
  return(tree);
}


/* Retourne le rankieme fils d'un arbre (de 0 a n-1) */
TreeP getChild(TreeP tree, int rank) {
  if (tree->nbChildren < rank -1) { 
    fprintf(stderr, "Incorrect rank in getChild: %d\n", rank);
    abort();
  }
  return tree->u.children[rank];
}


void setChild(TreeP tree, int rank, TreeP arg) {
  if (tree->nbChildren < rank -1) { 
    fprintf(stderr, "Incorrect rank in getChild: %d\n", rank);
    abort();
  }
  tree->u.children[rank] = arg;
}


/* Constructeur de feuille dont la valeur est une chaine de caracteres */
TreeP makeLeafStr(short op, char *str) {
  TreeP tree = makeNode(0, op);
  tree->u.str = str;
  return tree;
}


/* Constructeur de feuille dont la valeur est un entier */
TreeP makeLeafInt(short op, int val) {
  TreeP tree = makeNode(0, op); 
  tree->u.val = val;
  return(tree);
}

TreeP makeLeafLVar(short op, VarDeclP lvar) {
  TreeP tree = makeNode(0, op); 
  tree->u.lvar = lvar;
  return(tree);
}

/*ClassP makeSuperClass(char* name,TreeP params)
{
	ClassP ClassP= NEW(1, Class);
	ClassP->name=name;
	ClassP->classMereParams=params;
	
	return ClassP;
}*/

/* si on est la, c'est qu'il n'y a ni erreur lexicale, ni erreur syntaxique */
int compile(TreeP mainExp) {
  if (noVC) {
    fprintf(stderr, "Leaving before contextual verifications...\n");
    return 0;
  } else { runVC(mainExp); }
  if (errorCode != NO_ERROR) {
    fprintf(stderr, "Contextual errors. No code generation...\n");
    return errorCode;
  }
  if (noCode == FALSE) { genCode(mainExp); }
  return errorCode; 
}

/*===========================================================================================*/

/* Renvoie vrai si une classe est dans une liste de classe */
bool estDansListClasse(ClassP listClass, char *nom){
  ClassP parcour = listClass;
  while((parcour!=NULL) && (strcmp(parcour->name, nom)!=0)){
    parcour=parcour->next; 
  }
  if(parcour == NULL){
    char *message = calloc(SIZE_ERROR,sizeof(char));
  sprintf(message,"Erreur init 20");
    return FALSE;
  }
  else{
    return TRUE;
  }
}

/* Permet de creer une classe qui contient uniquement un nom */
ClassP makeDefClasse(char *nom, int final, VarDeclP params){
  ClassP res = NEW(1, Class);
  res->name = nom;
  res->isFinal = final;
  res->params = params;

  return res;
}

ClassP checkAndDefineClasse(char *nom, int final, VarDeclP params, ClassP classAnalysee){
    /*verifer s'il existe deja une meme classe*/
    ClassP class;
    if(estDansListClasse(listClass, nom) == TRUE){
      printf("Erreur de la definition de classe, idClass = %s existe deja\n", nom);
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,"Erreur - la classe %s est deja declare",nom);
      class = NULL;
    }
    /*sinon, on cree une classe et l'ajoute dans la liste*/
    else{
        class = makeDefClasse(nom, final, params);
        classAnalysee = class;

        if(listClass == NULL){
            listClass = class;    
        }
        else{
            ClassP temp = listClass;
            while(temp->next != NULL){
            temp = temp->next;     
            }
            temp->next = class;   
        }
    }
    return class;
}

/** construit une structure classe (pouvant etre une liste de classe) apres l'appel de makeDefClasse */
ClassP makeClasseApresDef(ClassP res,TreeP corps_constructeur,MethodeP liste_methodes, VarDeclP liste_champs, ClassP classe_mere, int isExtend){
  res->constructor=corps_constructeur;
  res->methodeL=liste_methodes;
  res->lvar=liste_champs;
  res->classMere=classe_mere;
  if(res->classMere != NULL)
  {
    if(res->classMere->constructor != NULL)
      res->appel_constructeur_mere = classe_mere->constructor;
    else
      res->appel_constructeur_mere = NULL;
  }
  res->isExtend=isExtend;
  /* res->next=NULL;*/ /* verifier si ça ne pose pas de pb */
  return res;
}

bool varEstDansListe(VarDeclP listeVar, char *nom){
    VarDeclP tmp = listeVar;
    while(tmp!=NULL){
        if(strcmp(tmp->name, nom) == 0){
            return TRUE;
        }
        tmp = tmp->next;
    }
    return FALSE;
}

VarDeclP copyVar(VarDeclP var){
    if(var == NULL) return NULL;
    VarDeclP tmp_var = var;
    VarDeclP copy = makeListVar(tmp_var->name, tmp_var->type, tmp_var->categorie, tmp_var->init);
    VarDeclP tmp_copy = copy;
    tmp_var = tmp_var->next;
    tmp_copy = tmp_copy->next;
    while(tmp_var!=NULL){
        tmp_copy = makeListVar(tmp_var->name, tmp_var->type, tmp_var->categorie, tmp_var->init);
        tmp_var = tmp_var->next;
        tmp_copy = tmp_copy->next;
    }
    tmp_copy = NULL;
    return copy;
}

/* Creer une (ou une liste de) variable pouvant etre un parametre, un champ, .. */
VarDeclP makeListVar(char *nom, ClassP type, int cat, TreeP init){
  char *message = calloc(SIZE_ERROR,sizeof(char));
  if(strcmp(nom,"void")==0)
  {
    sprintf(message,"Id %s est reserve au langage", nom);
    pushErreur(message,type,NULL,NULL);
  }

  VarDeclP res=NEW(1,VarDecl);
  /*res->next=NIL(VarDecl); verifier si ça ne pose pas de pb */
  res->name=nom;
  res->type=type;
  res->init=init;
  res->categorie=cat; /* si cat=0 ==> var non static. si cat=1 ==> var static */
  if(type!=NULL)
  {
    if(strcmp(type->name, "Integer"))
    res->intStrObjet = 1;
    else if(strcmp(type->name,"String"))
    res->intStrObjet = 2;
    else
    res->intStrObjet = 3;
  }
  return res;
}


/* Creer une erreur et l'ajoute a la pile */
void pushErreur(char* message,ClassP classe,MethodeP methode,VarDeclP variable)
{
  ErreurP nouvelle = NEW(1,Erreur);
  nouvelle->message = NEW(SIZE_ERROR,char);
  strcpy(nouvelle->message,message);
  
  if(classe!=NULL) nouvelle->classe = *classe;
  if(methode!=NULL) nouvelle->methode = *methode;
  if(variable!=NULL) nouvelle->variable = *variable;
  
  if(listeErreur==NULL)
  {
    listeErreur = nouvelle;
  }
  else
  {
    ErreurP tmp = listeErreur;
    listeErreur = nouvelle;
    nouvelle->next = tmp;
  }
}

void afficheListeErreur(ErreurP listeE)
{
  if(listeE==NULL)
  {
    printf("Aucune erreur : OK\n");
    return;
  }
  else
  {
    ErreurP tmp = listeE;
    int i = 1;
    while(tmp!=NULL)
    {
     printf("Erreur %d : %s\n",i,tmp->message);
     /*printf(RED);*/
      tmp = tmp->next;
      i++;
    }
  }
}


/* Fonction permettant le parcours de l'arbre*/
bool checkProgramme(TreeP prog)
{
  char *message = calloc(SIZE_ERROR,sizeof(char));
  if(prog == NULL) return FALSE;
  /* Acces statique au bloc Main */
  TreeP bloc = getChild(prog,2);
  bool  checkLC = FALSE;
  Class tmp;
  ClassP liste = NULL;
  if(listClass == NULL)
  {
    checkLC = TRUE;
  }
  else
  {
    tmp = *listClass;
    liste = NEW(1,Class);
    *liste = tmp;
  }

  dansCheckBlocMain = FALSE;
  /*printf("Entree check classL\n");*/
  if(!checkLC)
  {
     while(liste!=NULL)
     {
        if(strcmp(liste->name, "Integer")!=0 && strcmp(liste->name, "String")!=0 && strcmp(liste->name, "Void")!=0)
          checkLC = checkClass(bloc,prog,liste, NULL, NULL) && checkLC;
        else
          checkLC = TRUE;
        liste = liste->next;
     }
  }

  bool blockMain = FALSE;
  dansCheckBlocMain = TRUE;
  if(bloc->op == BLOCANO)
  {
    TreeP eListOpt = getChild(bloc,2);
    if(eListOpt->op == LIST && getChild(eListOpt,1) == NIL(Tree))
      {
        blockMain = TRUE;
      }
      else
      {
        blockMain = checkBloc(bloc,prog,NULL, NULL, NULL,0);
      }
  } 
  if(bloc->op == BLOCLAB)
  {
      ClassP typeRetourBloc = getClasseCopie(listClass, getChild(bloc,1)->u.str);
      TreeP eListOpt = getChild(bloc,2);
      if(eListOpt->op == LIST && getChild(eListOpt,0)->u.str != NULL && getChild(eListOpt,0)->op == ID && strcmp(getChild(eListOpt,0)->u.str, "void") == 0)
      {
        blockMain = TRUE;
      }
      else
      {
        blockMain = checkBloc(bloc,prog,NULL, NULL, NULL,0);
      }
      ClassP typeRe = getType(getChild(bloc,2),racine,NULL,NULL,NULL);
      if(typeRe == NULL)
        printf("it isnull\n");
      if(!equalsType(typeRetourBloc, typeRe))
      {
        sprintf(message,"Dans le main bloc, la valeur renvoyee ne correspond pas le type de bloc %s", typeRetourBloc->name);
        pushErreur(message,NULL,NULL,NULL);
        blockMain = FALSE;
      }
  } 
  if(listClass==NULL)
    return blockMain;
  
  return blockMain && checkLC;

}

/* Renvoi le pointeur de classe avec un nom donnée */
ClassP getClasse(ClassP listeClass, char *nom){
  ClassP parcour = listeClass;
  while((parcour!=NULL) && (strcmp(parcour->name,nom)!=0)){
    parcour=parcour->next; 
  }
  if(parcour == NULL){
    char *message = calloc(SIZE_ERROR,sizeof(char));
    sprintf(message,"Classe %s inexistante ", nom);
    pushErreur(message,NULL,NULL,NULL);
    return NULL;
  }
  else{
    /*parcour->next = NULL;*/
    return parcour;
  }
}


/** Renvoie une copie de la classe cherchee */
ClassP getClasseCopie(ClassP listeClass, char *nom){
  ClassP retour = getClasse(listeClass, nom);
  if(retour ==NULL)
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));
    sprintf(message,"Classe %s inexistante ", nom);
    pushErreur(message,NULL,NULL,NULL);
    return NULL;
  }
  Class classe = *retour;
  ClassP classeFin = NEW(1,Class);
  *classeFin = classe;
  classeFin->next = NULL;
  return classeFin;
}

/* Renvoi vrai si var1 = var2 */
bool memeVar(VarDeclP var1, VarDeclP var2){
  if(var1 == NIL(VarDecl)){
    if(var2 == NIL(VarDecl)) return TRUE;
    return FALSE;
  }
  if(var2 == NIL(VarDecl)) return FALSE;
  if(strcmp(var1->name, var2->name)!=0) return FALSE;
  if(strcmp(var1->type->name, var2->type->name) != 0) return FALSE; 
  if(var1->categorie != var2->categorie)  return FALSE; 
  return memeVar(var1->next, var2->next);
}

/** Renvoie un pointeur de la methode recherchee d'une classe */ 
MethodeP getMethode(ClassP classe, MethodeP methode)
{
  if(classe==NULL || methode==NULL){
    return NULL;
  }
  MethodeP tmp_liste_methodes_classe = getClasseCopie(listClass,classe->name)->methodeL;
  MethodeP tmp_liste_methode = methode;
  if(methode == NULL) return FALSE;

  while(tmp_liste_methodes_classe != NULL){
    /* si 2 methodes ont le meme noms, les memes classes de retour (meme noms) et memes param ==> meme methode */
    if(strcmp(tmp_liste_methodes_classe->name, tmp_liste_methode->name)==0 
        && strcmp(tmp_liste_methodes_classe->typeRetour->name, tmp_liste_methode->typeRetour->name)==0 
        && memeVar(tmp_liste_methodes_classe->lvar, tmp_liste_methode->lvar)==TRUE){
      return tmp_liste_methodes_classe;
    }
    tmp_liste_methodes_classe = tmp_liste_methodes_classe->next;
  }
  return NULL;
}

/* Creation de la structure Methode  - pas utilisee*/
/*res->next = NIL(Methode);*/  
/* verifier si ça ne pose pas de pb */

MethodeP makeMethode(char *nom, int staticOpt, int finalOpt, int redefOpt, TreeP corps, ClassP typeRetour, VarDeclP params, ClassP classApp){
  
  MethodeP res=NEW(1, Methode);
  res->name=nom;
  res->isStatic = staticOpt;
  res->isFinal = finalOpt;
  res->isRedef = redefOpt;
  res->corps=corps;
  res->lvar=params;
  res->typeRetour=typeRetour; 
  res->classApp=classApp;
  
  return res;
}



/*construire une classe et l'initialiser (classe definie par utilisateur)*/
ClassP makeClasse(ClassP classDef, ClassP classe_mere, VarDeclP varL, MethodeP methodeL, TreeP constructeur){
    TreeP constructor = NULL;
    if(classDef == NULL)
    { printf("Erreur de la definition de class, il faut commencer par class class_id...\n");}
    else{
        int isExtend;
        if(classe_mere == NIL(Class) || classe_mere == NULL){isExtend=0;}
        else { isExtend = 1;}
        if(constructeur->op == BLOCANO && getChild(constructeur,0) == NIL(Tree) && getChild(constructeur,1) == NIL(Tree) && getChild(constructeur,2) == NIL(Tree))
          constructor = NULL;
        else
          constructor = constructeur;
        classDef = makeClasseApresDef(classDef, constructor, methodeL, varL, classe_mere, isExtend);
        /*s'il existe les redefinitions des methodes*/
        if(isExtend == 1){
            MethodeP temp_liste_methode_classMere = classe_mere->methodeL;
            while(temp_liste_methode_classMere != NULL){
                MethodeP methodeRedifinie = getMethode(classDef, temp_liste_methode_classMere);
                if(methodeRedifinie != NULL){
                    if(methodeRedifinie->isRedef == 0)
                        methodeRedifinie->isRedef = 1;
                }
                temp_liste_methode_classMere = temp_liste_methode_classMere->next;
            }
        }

    }

    return classDef;
}


/*construire un champ pour une classe*/
VarDeclP makeChamp(int staticOpt, VarDeclP param, TreeP init){
    VarDeclP res;
    if(param->type != NULL)
    {
      res = makeListVar(param->name, getClasseCopie(listClass, param->type->name), staticOpt, init);
    }
    else
    {
      res = makeListVar(param->name, NULL, staticOpt, init);
    }
    return res;
}

/* Construit entierement une classe predefinie*/
ClassP makeClassePredefinie(char *nom, VarDeclP params,TreeP corps_constructeur,MethodeP liste_methodes,VarDeclP liste_champs, ClassP classe_mere, int isExtend, int isFinal){
  
    ClassP res = NEW(1, Class);
    res->name = nom;
    res->params = params;
    res->constructor = corps_constructeur;
    res->methodeL = liste_methodes;
    res->lvar = liste_champs;
    res->classMere = classe_mere; 
    res->isExtend = isExtend;
    res->isFinal = isFinal;
    /* res->next=NULL;*/ /* verifier si ça ne pose pas de pb */
    return res;
}

/*checkClass(bloc,prog,liste, NULL, NULL)*/
bool checkClass(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl)
{
    printf("[classe analysee: %s]\n",courant->name);
    /*
    * bool checkHeritage(classe);
    * bool checkListAttribut(Class classe);
    * bool checkListMethode(Class classe);
    ----
    * bool checkCorp(Methode methode)
    ----
    * bool checkListMethodeStatic(Class classe); // n'utilise pas genre les attribut de classe comme en java
    */

    /* Le nom de la classe doit avoir une majuscule, ici, on traite dans la partie lexicale en fait*/
    bool nomMaj = FALSE;

    listId = NULL;    /*chaque fois qu'on evalue une nouvelle classe*/
    profondeur = 0;
    rang = 0;

    if(courant->name!=NULL && (courant->name[0] >= 'A' && courant->name[0] <= 'Z'))
        nomMaj = TRUE;

    /*TRUE : OK FALSE : NOK*/
    bool heritage = FALSE;
    /*FIXME : boucle qui verifie que la classe mere n'est pas dans la liste d'erreur !!!
    * Si c'est le cas -> renvoye faux directement => et ajouter une erreur du style
    * "Corrigez la classe Mere %s avant",class->classe_mere->nom (utilisez sprintf)
    */

    if(courant->isExtend)
    {
        if(courant->classMere==NULL)
        {
            heritage = FALSE;
        }
        else
        {
            heritage = checkHeritage(courant);
        }
    }
    else
    {
        heritage = TRUE;
    }

    if(listId == NULL)
    {
        VarDeclP temp_params = courant->params;
        IdP temp_listId = listId;
        IdP temp_listIdAjoute;
        if(temp_params != NULL)
        {
          while(temp_params != NULL)
          {
            IdP newId = NEW(1, Id);
            newId->name = temp_params->name;
            newId->nature = ParametreClasse;
            newId->type = getClasseCopie(listClass, temp_params->type->name);
            newId->profondeur = profondeur;
            newId->rang = rang;

            if(temp_listId != NULL)
            {
              while(temp_listId->next != NULL)
                temp_listId = temp_listId->next;
            }
            if(temp_listId == NULL)
            {
              temp_listId = newId;
              temp_listIdAjoute = newId;
            }
            else
              temp_listId->next = newId;
            rang ++;
            temp_params = temp_params->next;
          }
          listId = temp_listIdAjoute;
        }
    }

    bool attribut = checkListAttribut(arbre,ancien,courant,methode,listeDecl);

    if(!attribut)
    {
        return FALSE;
    }

    bool methodeC = checkListMethode(arbre,ancien,courant,methode,listeDecl);
    /*printf("Class:%s\n", courant->name);
    IdP tempList = listId;
    while(tempList != NULL)
    {
      printf("ID: %s, kind: %d, type: %s, profondeur : %d, rang: %d\n", tempList->name, 
        tempList->nature,
        tempList->type->name,
        tempList->profondeur, tempList->rang);
      tempList = tempList->next;
    }*/
    /*verfier ces 4 parties sont correctes*/
    /*return (nomMaj && heritage && attribut && methodeC);*/

    return (nomMaj && heritage && attribut && methodeC);
}


/*
 * Verifie qu'il n'y a pas de cycle d'héritage
 * VRAI : OK (si la classe n'herite d'aucune classe on considere qu'il n'y a pas de cycle)
 * FAUX : classe mere non declare avant
 */
bool checkHeritage(ClassP classe)
{
    return classExtendsDeclareeAvant(classe,classe->classMere);
}

/*
 * Verifie que la classe heritee est declare avant la classe actuelle
 * Car si on fait class actuelle extends class herite il y a une necessite de 
 * declaration au dessus (de la classe heritee)
 */
bool classExtendsDeclareeAvant(ClassP actuelle,ClassP heritee)
{
    /*classe mere inexistante*/
    if(heritee==NULL)
        return TRUE;
    ClassP listTmp = listClass;

    while(listTmp!=NULL && strcmp(actuelle->name,listTmp->name)!=0)
    {
        /*On a trouve la classe elle est bien declaree avant*/
        if(strcmp(heritee->name,listTmp->name)==0)
        {
          return TRUE;
        }

        listTmp = listTmp->next;
    }
    /*affichage d'erreur directement*/
    char *message = calloc(SIZE_ERROR,sizeof(char));
    sprintf(message,"Erreur init 23");
    return FALSE;
}

/*construire un identificateur*/
IdP makeId(char *name, enum natureId nature, ClassP type, int profondeur, int rang)
{
  IdP newId = NEW(1, Id);
  newId->name = name;
  newId->nature = nature;
  newId->type = getClasseCopie(listClass, type->name);
  newId->profondeur = profondeur;
  newId->rang = rang;

  return newId;
}

/*ajoute un identificateur dans la liste*/
bool addId(IdP liste, IdP id)
{
  IdP tempListe = liste;
  if(id == NULL)
    return FALSE;
  if(tempListe == NULL)
  {
    tempListe = id;
    id->next = NULL;
    listId = tempListe;
  }
  else
  {
    while(tempListe->next != NULL)
      tempListe = tempListe->next;
    tempListe->next = id;
    id->next = NULL;
  }
  return TRUE;
}

/*check si un identificateur deja existe(meme profondeur)*/
bool checkIdExiste(IdP id)
{
  IdP templistId = listId;
  while(templistId != NULL)
  {
    if(strcmp(templistId->name, id->name) == 0)
    {
      if(templistId->profondeur == id->profondeur)
        if(templistId->rang < id->rang)
          return TRUE;
    }
    templistId = templistId->next;
  }
  return FALSE;
}

bool checkIdBlocExiste(IdP id)
{
  IdP templistId = listId;
  while(templistId != NULL)
  {
    if(strcmp(templistId->name, id->name) == 0 && templistId->nature == BlocLable)
    {
      if(templistId->profondeur != id->profondeur)
        if(templistId->rang < id->rang)
          return TRUE;
    }
    templistId = templistId->next;
  }
  return FALSE;
}

bool checkIdVarExisteParNom(char *name)
{
  IdP templistId = listId;
  while(templistId != NULL)
  {
    if(strcmp(templistId->name, name) == 0)
      if(templistId->nature == Variable || templistId->nature == ParametreFon || templistId->nature == ParametreClasse)
        return TRUE;
    templistId = templistId->next;
  }
  return FALSE;
}

bool checkIdBlocExisteParNom(char *name)
{
  IdP templistId = listId;
  while(templistId != NULL)
  {
    if(strcmp(templistId->name, name) == 0)
      if(templistId->nature == BlocLable)
        return TRUE;
    templistId = templistId->next;
  }
  return FALSE;
}

ClassP getTypeIdVar(char *name)
{
  IdP templistId = listId;
  while(templistId != NULL)
  {
    if(strcmp(templistId->name, name) == 0)
    {
      if(templistId->nature == Variable || templistId->nature == ParametreFon)
        return templistId->type;
    }
    templistId = templistId->next;
  }
  return NULL;
}

ClassP getTypeIdBloc(char *name)
{
  IdP templistId = listId;
  while(templistId != NULL)
  {
    if(strcmp(templistId->name, name) == 0)
    {
      if(templistId->nature == BlocLable)
        return templistId->type;
    }
    templistId = templistId->next;
  }
  return NULL;
}

/*pop les variables locales*/
void moveIdFromListParProfondeur(int profon)
{
  bool remove = FALSE;
  /*printf("move from profondeur:%d\n", profon);*/
  IdP templistId = listId;
  if(templistId->profondeur == profon && (templistId->nature == Variable || templistId->nature == ParametreFon))
  {
    listId = templistId->next;
    free(templistId);
  }
  else
  {
    while(templistId->next != NULL)
    {
      if(templistId->next->profondeur == profon && (templistId->next->nature == Variable || templistId->next->nature == ParametreFon))
      {
        IdP temp = templistId->next;
        templistId->next = temp->next;
        free(temp);
        remove = TRUE;
      }
      if(remove == FALSE)
        templistId = templistId->next;
      else
        remove = FALSE;
    }
  }
}

void moveIdBlocFromListParProfondeur(int profon)
{
  bool remove = FALSE;
  /*printf("move from profondeur:%d\n", profon);*/
  IdP templistId = listId;
  if((templistId->profondeur > profon) && templistId->nature == BlocLable)
  {
    listId = templistId->next;
    free(templistId);
  }
  else
  {
    while(templistId->next != NULL)
    {
      if((templistId->next->profondeur > profon) && templistId->next->nature == BlocLable)
      { 
        IdP temp = templistId->next;
        templistId->next = temp->next;
        free(temp);
        remove = TRUE;
      }
      if(remove == FALSE)
        templistId = templistId->next;
      else
        remove = FALSE;
    }
  }
}


bool checkListAttribut(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl)
{
    /*printf("enter checkListAttribut\n");*/
    if(courant!=NULL && !verifAttributClasse(courant))
    {
        char *message = calloc(SIZE_ERROR,sizeof(char));
        if(courant!=NULL)
        {
            sprintf(message,"Attributs duppliqué dans la classe %s ",courant->name);
            pushErreur(message,courant,NULL,NULL);
        }
        else
        {
            sprintf(message,"Attributs duppliqué");
            pushErreur(message,NULL,NULL,NULL);
        }
        return FALSE;
    }
    /*
    * Parcourir les attributs de la classe actuel & verifier qu'il n'y a aucune qui se ressemble !
    */
    VarDeclP tmp = courant->lvar;
    while(tmp!=NULL)
    {
        if(tmp->type==NULL)
        {
            char* message = NEW(SIZE_ERROR,char);
            sprintf(message,"Erreur: la type de l'attribut %s n'existe pas",tmp->name);
            pushErreur(message,NULL,NULL,tmp);
            return FALSE;
        }

        if(tmp->init != NIL(Tree) || tmp->init != NULL)
        {
          ClassP type = getType(getChild(tmp->init,1),arbre,courant,methode,listeDecl);
          if(type != NULL && !equalsType(tmp->type,type))
          {
            char* message = NEW(SIZE_ERROR,char);
            sprintf(message,"Erreur affectation d'un %s par un %s",tmp->type->name,type->name);
            pushErreur(message,courant,methode,NULL);
            return FALSE;
          }
        }
        IdP newId = makeId(tmp->name, Variable, tmp->type, profondeur, rang);
        addId(listId, newId);
        rang++;
        tmp = tmp->next;
    }
    return TRUE;
}

/*
 * True : si la classe n'a pas des attributs en doublons
 * False : KO
 */
bool verifAttributClasse(ClassP classe)
{
    if(classe->lvar==NULL)
    {
        return TRUE;
    }

    VarDeclP tmp = classe->lvar;
    VarDeclP reste = tmp->next;
    while(tmp!=NULL)
    {
        reste = tmp->next;

        while(reste!=NULL)
        {
          if(strcmp(reste->name,tmp->name)==0)
          {
            char *message = calloc(SIZE_ERROR,sizeof(char));
            sprintf(message,"Erreur init 33");
            return FALSE;
          }
          reste = reste->next;
        }
        tmp = tmp->next;
    }
    return TRUE;
}


ClassP getType(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl)
{
    if(courant!=NULL)
    {
        courant = getClasseCopie(listClass,courant->name);
    }
    if(arbre==NULL)
    {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Arbre est vide");
        /*pushErreur(message,classAnalysee,methode,NULL);*/
        return NULL;
    }
    ClassP tmpDebug = NULL;
    /* Dans le cas d'une selection, récupérer le dernier élèment */ 
    ClassP type = NULL;
    ClassP type2 = NULL;
    LTreeP liste = NULL;
    ClassP typeDeRetourBlocLab = NULL;
    ClassP typeDeRetourExpBloc = NULL;
    ClassP typeAFFgauche;
    ClassP typeAFFdroit;

    bool instCorrecte = FALSE;
    char* message = NEW(SIZE_ERROR,char);
    char *nomC = NULL;
    char * nomClass =NULL;
    ClassP tmp = NULL;

    switch(arbre->op)
    {
        case UMINUS:
        case UPLUS:
            type = getType(getChild(arbre,0),arbre,courant,methode,listeDecl);

            if(type!=NULL && strcmp(type->name,"Integer")!=0)
            {
              sprintf(message,"Erreur plus unaire n'est pas applicable sur %s car ce n'est pas un entier",type->name);
              pushErreur(message,type,NULL,NULL);
              return NULL;
            }
            else if(type==NULL)
            {
              sprintf(message,"Erreur plus unaire de type");
              pushErreur(message,type,NULL,NULL);
              return NULL;
            }
            else
            {
              return type;
            }
        break;

        case ADD: 
        case MINUS: 
        case MUL:
        case DIV:
            type = getType(getChild(arbre,0),arbre,courant,methode,listeDecl);
            type2 = getType(getChild(arbre,1),arbre,courant,methode,listeDecl);
            
            /*printf("type1: %s, type2: %s\n", type->name, type2->name);*/
            /*printf("type = NULL ? %s type2 = NULL ? %s\n",type->name,type2->name);*/
            if(equalsType(type,type2)){
               return type;
            }
            else
            {
              if(type!=NULL)
              {
                if(type2!=NULL)
                {
                  sprintf(message,"Erreur operation arithmetique entre un objet de type %s et %s",type->name,type2->name);
                }
                else
                {
                  sprintf(message,"Le type a cote de %s n'est pas reconnu",type->name);
                }
              }
              else
              {
                sprintf(message,"Erreur de type operation arithmetique, type de gauche iconnu");
              }
              pushErreur(message,classAnalysee,methode,NULL);
              return NULL;
            }

        break;

        case NE :
        case EQ :
        case LT :
        case LE :
        case GT :
        case GE :
            type = getType(getChild(arbre,0),arbre,courant,methode,listeDecl);
            type2 = getType(getChild(arbre,1),arbre,courant,methode,listeDecl);
            /*les operateurs de comparison ne sont disponibles que dans la classe Integer*/
            if(equalsType(type,type2) && (strcmp(type->name,"Integer")==0 || strcmp(type->name,"Integer")==0))
            {
              return type;
            }
            else
            {
              if(type!=NULL)
              {
                if(type2!=NULL)
                {
                  sprintf(message,"Erreur operation de comparaison entre un objet de type %s et %s",type->name,type2->name);
                }
                else
                {
                  sprintf(message,"Le type a cote de %s n'est pas reconnu",type->name);
                }
              }
              else
              {
                if(type2!=NULL)
                {
                  sprintf(message,"Erreur de type operation de comparaison %s et %s ",type2->name,getChild(arbre,0)->u.str);
                }
                else
                {
                  sprintf(message,"Erreur de type operation de comparaison");
                }
              }
              pushErreur(message,classAnalysee,methode,NULL);
              return NULL;
            }
        break; 

        case AND :

            type = getType(getChild(arbre,0),arbre,courant,methode,listeDecl);
            type2 = getType(getChild(arbre,1),arbre,courant,methode,listeDecl);
            /*l'operateur & n'est disponible que dans la classe String*/
            if(type!=NULL && strcmp(type->name,"String")!=0){  
              sprintf(message,"Erreur l'attribut %s n'est pas un string",type->name);
              pushErreur(message,type,NULL,NULL);
              return NULL;
            } 
            if(type2!=NULL && strcmp(type2->name,"String")!=0){
              sprintf(message,"Erreur l'attribut %s n'est pas un string",type2->name);
              pushErreur(message,type,NULL,NULL);
              return NULL;   
            }
            return type;
        break;

        case SELECT : 
        case CSELECT :
            liste = transFormSelectOuEnvoi(arbre,liste);
            return estCoherentEnvoi(liste, courant, methode,listeDecl);
        break;

        case CENVOI:
        case ENVOI:
            liste = transFormSelectOuEnvoi(arbre,liste);
            return estCoherentEnvoi(liste, courant, methode,listeDecl);
        break;

        case Cste:
            return getClasseCopie(listClass,"Integer");
        break;

        case STR:
            return getClasseCopie(listClass,"String");
        break;

        case ID:

          if(strcmp(arbre->u.str,"void")==0)
          {
            return getClasseCopie(listClass,"Void");
          }
          if(strcmp(arbre->u.str,"this")==0)
          {
            if(courant!=NULL)
            {
              return getClasseCopie(listClass,courant->name);
            }
            else
            {
              return NULL;
            }
          }
          if(strcmp(arbre->u.str,"super") == 0 && ancien!=NULL && (ancien->op==YIELDLAB || ancien->op==YIELDANO) && ancien->op!=CENVOI && ancien->op!=ENVOI && ancien->op!=SELECT && ancien->op!=CSELECT)
          {
            sprintf(message,"super n'est pas utilisable dans le yield! ");
            pushErreur(message,type,NULL,NULL);
            return NULL;
          }

          tmpDebug = getTypeAttribut(arbre->u.str, courant, methode, listeDecl,FALSE,FALSE);
          if(tmpDebug == NULL)
          {
            tmpDebug = getTypeAttribut(arbre->u.str, courant->classMere, NULL, listeDecl,FALSE,FALSE);
          }
            
          if(tmpDebug == NULL)
          {
            bool checkIdExiste = checkIdVarExisteParNom(arbre->u.str);
            if(checkIdExiste)
              tmpDebug = getClasseCopie(listClass,getTypeIdVar(arbre->u.str)->name); 
            else
              tmpDebug = NULL;
          }
            
          return tmpDebug;
        
        break;

        case CID:
          return getClasseCopie(listClass,arbre->u.str);
        break;

        case BLOCLAB:
          typeDeRetourBlocLab = getClasseCopie(listClass,getChild(arbre, 1)->u.str);
          typeDeRetourExpBloc = getType(getChild(arbre,2), arbre, courant,methode,listeDecl);
          if(!equalsType(typeDeRetourBlocLab, typeDeRetourExpBloc))
          {
            sprintf(message,"Le type de valeur de retour dans le bloc ne correspond pas au type donnee dans la signature");
            pushErreur(message,NULL,NULL,NULL);
            return NULL;
          }
          else
            return typeDeRetourExpBloc;
        break;
        
        case BLOCANO:
          return getType(getChild(arbre,2),arbre,courant,methode,listeDecl);

        break;

        case KNEW: 
          nomClass = getChild(arbre,0)->u.str;
          tmp = getClasseCopie(listClass,nomClass);
          if(tmp == NULL)
          {
            sprintf(message,"Erreur d'instanciation : %s n'existe pas",nomClass);
            pushErreur(message,type,NULL,NULL);
          }
          else
          {
            nomC = calloc(100,sizeof(char));
            sprintf(nomC,"constructeur %s",nomClass);
            
            instCorrecte = compareParametreMethode(tmp->params,getChild(arbre,1),courant,methode,listeDecl,nomC);
            if(!instCorrecte)
            {
              sprintf(message,"Erreur d'instanciation : %s mal appelee",nomClass);
              pushErreur(message,type,NULL,NULL);
            }
            else
            {
              return tmp;
            }
          }
        break;

        case LIST:
          if(getChild(arbre,0)->u.str != NULL && strcmp(getChild(arbre,0)->u.str, "void") == 0 && getChild(arbre,1) == NULL)
          {
            return getClasseCopie(listClass, "Void");
          }  
          else if(getChild(arbre,0) != NULL 
                  && getChild(arbre,1)->nbChildren == 2 
                  && getChild(arbre,1)->op == LIST 
                  && getChild(getChild(arbre,1),0)->u.str != NULL
                  && strcmp(getChild(getChild(arbre,1),0)->u.str, "void") == 0)
          {
            if(getChild(arbre,0)->op == LOCVAR)
              return getClasseCopie(listClass, "Void");
            else
              return getType(getChild(arbre,0), arbre, courant,methode, listeDecl);
          }
          else
          {
            return getType(getChild(arbre,1), arbre, courant,methode, listeDecl);
          }
        break;

        case AFF:
          if(getChild(arbre,0) == NULL && getChild(arbre,1) != NULL)
            return getType(getChild(arbre,1), arbre, courant, methode,listeDecl);
          else
          {
            if(getChild(arbre,0) != NULL)
              typeAFFgauche = getType(getChild(arbre,0), arbre, courant, methode, listeDecl);
            if(getChild(arbre,1) != NULL)
              typeAFFdroit = getType(getChild(arbre,1),arbre, courant, methode, listeDecl);
            if(typeAFFgauche != NULL && typeAFFdroit != NULL
               &&equalsType(typeAFFgauche, typeAFFdroit))
              return typeAFFgauche;
            else
            {
              sprintf(message,"Erreur d'affectation dans le bloc, probleme de typage");
              pushErreur(message,NULL,NULL,NULL);
              return NULL;
            }
          }
        break;

        default : 
        printf("L'etiquette %d n'a pas ete gerer\n", arbre->op);

    }
    return NULL;
}


bool equalsType(ClassP gauche, ClassP droite)
{
    if(gauche!=NULL)
    {
      gauche = getClasseCopie(listClass,gauche->name);
    }
    if(droite!=NULL)
    {
      droite = getClasseCopie(listClass,droite->name);
    }
    if(gauche==NULL)
    {
      char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 31");
      return FALSE;
    }
    if(droite==NULL)
    {
      char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 32");
      return FALSE;
    }
    if(strcmp(gauche->name,droite->name)==0)
    {
      return TRUE;
    }
    else
    {
        if(!droite->isExtend)
        {
          return FALSE;
        }
        if(equalsType(gauche,droite->classMere))
        {
          return TRUE;
        }
        else
        {
          return isHeritage(gauche,droite->classMere);
        }
    }
    return FALSE;
}

/*verifier si class de droite est heritee de celle de gauche*/
bool isHeritage(ClassP gauche, ClassP droite)
{
  if(!droite->isExtend)
  {
    return (strcmp(gauche->name,droite->name)==0);
  }
  else
  {
    return isHeritage(gauche,droite->classMere);
  }
}

/*Retourne le type d'une varibable suivant les paramètre de la méthode, de la classe et de la liste de déclaration*/ 
ClassP getTypeAttribut(char* nom, ClassP classe, MethodeP methode, VarDeclP listeDecl, bool isStatic, bool agerer)
{
  bool estDansParamMeth = FALSE;
  bool estDansListeDecl =  FALSE;
  bool estDansAttributClasse = FALSE;
  ClassP res = NULL;

  if(classe!=NULL)
  {
    classe = getClasseCopie(listClass,classe->name);
  }
  if(nom!=NULL && nom[0]=='"')
  {
    return getClasseCopie(listClass,"String");
  }
  /*fonction atoi(): transformer un string a Interger, renvoie 0 si failure*/
  if(nom!=NULL && atoi(nom)!=0)
  {
    return getClasseCopie(listClass,"Integer");
  }
  
  /*suivant les paramètre de la méthode*/
  if(methode != NULL)
  {
    
    VarDeclP paramParcours = methode->lvar;
    char** variable = calloc(1,sizeof(char*));
    int i = 0;
    while(paramParcours!=NULL)
    {
      variable[i] = calloc(30,sizeof(char));
      strcpy(variable[i],paramParcours->name);
      i++;
      paramParcours = paramParcours->next;
    }
     /*Si on trouve deux variable ayant le meme nom (FALSE)*/
    if(!checkDoublon(variable,i-1))
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,"Erreur doublons dans les parametre de la methode %s",methode->name);
      pushErreur(message,classe,methode,NULL);
      return FALSE;
    }
    int j = 0;
    for (j = 0; j <= i-1 ; j++)
    {
      /*free(variable[j]);*/
    }
    /*free(variable);*/


    VarDeclP param = methode->lvar;

    while(param!=NULL)
    {
      if(strcmp(nom,param->name)==0)
      {
        estDansParamMeth = TRUE;
        Class copie = *param->type;
        ClassP pointeurCopie = NEW(1,Class);
        *pointeurCopie = copie;
        res = pointeurCopie;
        res->next = NULL;
        break;
      }

      param = param->next;
    }
  }
  
  if(listeDecl!=NULL)
  {
    VarDeclP listDeclParcours = listeDecl;
    char** variable = calloc(1,sizeof(char*));
    int i = 0;
    while(listDeclParcours!=NULL)
    {
      variable[i] = calloc(30,sizeof(char));
      strcpy(variable[i],listDeclParcours->name);
      i++;
      listDeclParcours = listDeclParcours->next;
    }

    /* Si on trouve deux variable ayant le meme nom (FALSE)*/
    if(!checkDoublon(variable,i-1))
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,"Erreur doublons dans la liste de declaration");
      pushErreur(message,classe,methode,NULL);
      return FALSE;
    }

    int j = 0;
    for (j = 0; j <= i-1 ; j++)
    {
      /*free(variable[j]);*/
    }
    /*free(variable);*/

    VarDeclP listDeclaration = listeDecl; 

    while(listDeclaration!=NULL)
    {
      if(strcmp(nom,listDeclaration->name)==0 && estDansParamMeth==TRUE)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Erreur l'attribut %s est redeclaree 1",nom);
        pushErreur(message,classe,methode,NULL);
        return NULL;
      }
      else if(strcmp(nom,listDeclaration->name)==0 && estDansParamMeth==FALSE){
        estDansListeDecl = TRUE;
        if(listDeclaration->type==NULL)
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,"Type inconnu");
          pushErreur(message,classe,methode,NULL);
          return NULL;
        }
        Class copie = *listDeclaration->type;
        ClassP pointeurCopie = NEW(1,Class);
        *pointeurCopie = copie;
        res = pointeurCopie;
        res->next = NULL;
        break;
      }
      listDeclaration = listDeclaration->next;
    }
    /*printf("1.1.6 estDansListeDecl %d \n",estDansListeDecl);*/
  }

  /*printf("classe->liste_champs null ? %d\n",classe==NULL?TRUE:FALSE);*/
  if(classe != NULL && classe->lvar != NULL)
  {
    VarDeclP listeClasseParcours = classe->lvar;
    char** variable = calloc(1,sizeof(char*));
    int i = 0;

    /*printf("---DEBUT LISTE DECL ----\n");*/
    while(listeClasseParcours!=NULL)
    {
      variable[i] = calloc(30,sizeof(char));
      strcpy(variable[i],listeClasseParcours->name);
      i++;
      listeClasseParcours = listeClasseParcours->next;
    }
    
    /*Si on trouve deux variable ayant le meme nom (FALSE)*/
    if(!checkDoublon(variable,i-1))
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,"Erreur doublons dans les attribut de la classe %s",classe->name);
      pushErreur(message,classe,methode,NULL);
      return FALSE;
    }
    int j = 0;
    for (j = 0; j <= i-1 ; j++)
    {
      /*free(variable[j]);*/
    }
    /*free(variable);*/

    VarDeclP listeClasse = classe->lvar;
    while(listeClasse != NULL)
    {
      if(strcmp(nom,listeClasse->name)==0 && (estDansListeDecl==TRUE))
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Erreur l'attribut %s est redeclaree %s",nom,classe->name);
        pushErreur(message,classe,methode,NULL);
        return NULL;
      }
      else if(strcmp(nom,listeClasse->name)==0 && estDansListeDecl==FALSE){
        if(!agerer)
        {
          estDansAttributClasse = TRUE;
          Class copie = *listeClasse->type;
          ClassP pointeurCopie = NEW(1,Class);
          *pointeurCopie = copie;
          res = pointeurCopie;
          res->next = NULL;
          break;
        }
        else if((listeClasse->categorie == CATEGORIE_STATIC && isStatic)||
                (listeClasse->categorie != CATEGORIE_STATIC && !isStatic))
        {
          estDansAttributClasse = TRUE;
          Class copie = *listeClasse->type;
          ClassP pointeurCopie = NEW(1,Class);
          *pointeurCopie = copie;
          res = pointeurCopie;
          res->next = NULL;
          break;
        }
        else
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,"Erreur l'attribut %s n'a pas le droit d'etre utilise de cette maniere",nom);
          pushErreur(message,classe,methode,NULL);
          return NULL;
        }
      }
      listeClasse = listeClasse->next;
    }
  }
  if(estDansAttributClasse == TRUE){}  /*seulement pour warning - -*/
  return res;
}



/* Si VRAI : aucun doublon */
bool checkDoublon(char** variable,int n)
{
  /*printf("DEBUT checkDoublon\n");*/
  int i = 0;
  int j = 0;
  for (i = 0; i <= n; i++)
  {
    for (j = i+1; j <= n; j++)
    {
      if(variable[i]!=NULL && variable[j]!=NULL && strcmp(variable[i],variable[j])==0)
      {
        char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 24");
        return FALSE;
      }
    }
  }
  return TRUE;
}

bool checkConstructeurExtends(VarDeclP params, TreeP appelMethode, ClassP classe, MethodeP methode, VarDeclP listeDecl, char *nom)
{
  if(classe != NULL)
    classe = getClasseCopie(listClass, classe->name);
  if(params == NULL && appelMethode == NULL)
    return TRUE;
  if((params != NULL && appelMethode == NULL) || (params == NULL && appelMethode != NULL))
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Probleme d'appel de constructeur de la classe mere");
    pushErreur(message,classe,NULL,NULL);
    return FALSE;
  }

  VarDeclP paramsMere = params;
  VarDeclP paramsFils = methode->lvar;
  VarDeclP champsFils = classe->lvar;
  int cptMere = 0;
  int cptFils = 0;
  int cptChampsFils = 0;
  while(paramsMere != NULL)
  {
    cptMere ++;
    paramsMere = paramsMere->next;
  }  
  while(paramsFils != NULL)
  {
    cptFils++;
    paramsFils = paramsFils->next;
  }
  while(champsFils != NULL)
  {
    if(champsFils->categorie == 0)
      cptChampsFils++;
    champsFils = champsFils->next;
  }
  if(cptMere != (cptFils - cptChampsFils))
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Probleme d'appel de constructeur de la classe mere");
    pushErreur(message,classe,NULL,NULL);
    return FALSE;
  }
  return TRUE;
}

/*compareParametreMethode(courant->classMere->params,courant->appel_constructeur_mere,courant,methodeFakeConstructeur,NULL,nomC)*/
/*check les arguments dans un appel de methode selon les params de la methode*/
bool compareParametreMethode(VarDeclP declaration, TreeP appelMethode, ClassP classe, MethodeP methode, VarDeclP listeDecl, char* nom)
{
  if(classe!=NULL)
  {
    classe = getClasseCopie(listClass,classe->name);
  }
  if((appelMethode==NULL && declaration!=NULL)||(appelMethode!=NULL && declaration==NULL))
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Probleme d'appel de constructeur de la classe mere");
    pushErreur(message,classe,NULL,NULL);
    return FALSE;
  }
  else if (appelMethode==NULL && declaration==NULL)
  {
    return TRUE;
  }

  /*Transformer a->b->c*/
  ClassP liste = NULL;

  liste = transformerAppel(appelMethode,liste,classe,methode,listeDecl);

  ClassP pointeur = liste;

  if(classe!=NULL)
  while(pointeur!=NULL)
  {
    pointeur = pointeur->next;
  }

  if(liste==NULL)
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 29");
    return FALSE;
  }

  ClassP tmp = liste;
  VarDeclP tmpDeclarationOfficiel = declaration;

  if(tmp==NULL && tmpDeclarationOfficiel==NULL)
  {
    return TRUE;
  }

  Class contenuTMP = *tmp;
  ClassP tmp2 = NEW(1,Class);
  *tmp2 = contenuTMP;
  int cpt = 0;
  
  while(tmp2!=NULL)
  {
    cpt++;
   /* printf("AppelMethode : %s\n", tmp2->name);*/
    tmp2 = tmp2->next;
  }
  /*printf("AppelMethode contient : %d\n", cpt);*/

  VarDecl contenuDeclaration = *tmpDeclarationOfficiel;
  VarDeclP tmpDeclarationOfficiel2 = &contenuDeclaration;
  int cptDeclaration = 0;
  while(tmpDeclarationOfficiel2!=NULL)
  {
    cptDeclaration++;
    /*printf("ParamOfficiel : %s\n",tmpDeclarationOfficiel2->type->name);*/
    tmpDeclarationOfficiel2 = tmpDeclarationOfficiel2->next;
  }
  /*printf("DeclarationOfficiel contient : %d element\n",cptDeclaration );*/
   
  if(cpt!=cptDeclaration)
  {
    char* message = NEW(SIZE_ERROR,char);
    sprintf(message,"Erreur la methode %s() attend %d parametre(s) et vous lui avez passez %d parametre(s)",nom,cptDeclaration,cpt);
    pushErreur(message,NULL,NULL,NULL);
    return FALSE;
  }

  while(tmp!=NULL)
  {
    if(tmpDeclarationOfficiel==NULL)
    {
      char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 29");
      return FALSE;
    }

    if(!equalsType(tmpDeclarationOfficiel->type,tmp))
    {
      char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 30");
      return FALSE;
    }

    tmpDeclarationOfficiel = tmpDeclarationOfficiel->next;
    tmp = tmp->next;
  }
  return TRUE;
}

/* Cree une liste chainee lorsqu'il y a une selection ou un envoi de message */
LTreeP transFormSelectOuEnvoi(TreeP arbre, LTreeP liste)
{
    /*printf("arbre -> op %d\n",arbre->op);*/
    if(liste==NULL)
    {
      liste = NEW(1,struct _listeTree);
      /*(arbre,1): ID*/  
      liste->elem = getChild(arbre,1);
      if(arbre->nbChildren == 3)
      {
        /*(arbre,2):ArgLOpt*/
        /*envoi de message : nbChildren: 3*/
        liste->elem->next = getChild(arbre,2);
        liste->elem->isEnvoiMessage = TRUE;
      }
      else
      {
        liste->elem->isEnvoiMessage = FALSE;
      }
    }
    else
    {
      listeTree tmp = *liste;
      if(arbre->nbChildren == 0)
      {
        return liste;
      }
      /*on met le nouveau arbre en avant*/
      liste->elem = getChild(arbre,1);
      liste->next = NEW(1,listeTree);
      *liste->next = tmp;

      if(arbre->nbChildren == 3)
      {
        liste->elem->next = getChild(arbre,2);
        liste->elem->isEnvoiMessage = TRUE;
      }
      else
      {
        liste->elem->isEnvoiMessage = FALSE;
      }
    }

    /*printf("verifier:%d getChild(arbre,0) %d \n",arbre->op, getChild(arbre,0)->op);*/
    if(getChild(arbre,0)->op == ID || getChild(arbre,0)->op == CID|| getChild(arbre,0)->op == STR || getChild(arbre,0)->op == Cste)
    {
      if(liste!=NULL)
      {
        /*printf("J'AI FINIS MA TRANSFORMOTION \n");*/
        listeTree tmp = *liste;
        liste->elem = getChild(arbre,0);
        liste->next = NEW(1,listeTree);
        *liste->next = tmp;
      } 
      /*printf("JE RETOURNE MAS TRANSFORMATION \n");*/
      return liste;
    }
    else if(getChild(arbre,0)->op==SELECT || getChild(arbre,0)->op==CSELECT || 
            getChild(arbre,0)->op==CENVOI || getChild(arbre,0)->op==ENVOI)
    {
      return transFormSelectOuEnvoi(getChild(arbre,0),liste);
    }
    else
    {
      if(liste!=NULL)
      {
        listeTree tmp = *liste;
        liste->elem = getChild(arbre,0);
        liste->elem->recupType = 1;
        liste->next = NEW(1,listeTree);
        *liste->next = tmp;
      } 
      return liste;
    }
}


ClassP estCoherentEnvoi(LTreeP liste, ClassP classe, MethodeP methode, VarDeclP listeDecl)
{
  /*printf("JE FAIS EST COHERENT ENVOIE  \n");*/
  LTreeP tmp = liste;
  ClassP init = NULL;
  bool isStatic = FALSE;
  bool agerer = FALSE;
  /*printf(" la valeur de bizarre est  %d, \n", tmp->elem->recupType);*/
  char* message = NEW(SIZE_ERROR,char);
  
  if(liste!=NULL || tmp->elem!=NULL)
  {    
    if(methode!=NULL && classe!=NULL)
    {
      sprintf(message,"Erreur la methode %s est mal forme - Classe : %s",methode->name,classe->name);
    }
    else
    {
      sprintf(message,"Erreur envoi de message");
    }
  }

  if(tmp->elem->op == ID)
  {
      if(classe!=NULL && (strcmp(tmp->elem->u.str,"super")==0))
      {
        if(methode!=NULL && methode->isStatic)
        {
            sprintf(message,"Erreur super present dans une methode statique");
            pushErreur(message,classe,methode,NULL);
            return NULL; 
        }
        else
        {
            init = classe->classMere;
        }
      }
      else if(classe!=NULL && (strcmp(tmp->elem->u.str,"this")==0))
      {
        if(methode!=NULL && methode->isStatic)
        {
          sprintf(message,"Erreur this present dans une methode statique");
          pushErreur(message,classe,methode,NULL);
          return NULL; 
        }
        else
        {
          init = classe;
        }
      }
      else
      {
          /*si il y a this ou super dans le bloc main -> erreur*/
          if((classe==NULL) && ((strcmp(tmp->elem->u.str,"this")==0)||(strcmp(tmp->elem->u.str,"super")==0)))
          {
            sprintf(message,"Erreur this ou super present dans le bloc main");
            pushErreur(message,classe,methode,NULL);
            return NULL; 
          }
          else
          {
            /*printf("getTypeAttribut de %s \n",tmp->elem->u.str);*/
            /*ici true*/
            if(dansCheckBlocMain)
            {
              init = getTypeAttribut(tmp->elem->u.str, classe, methode, listeDecl, FALSE, FALSE);
            }
            else
            {
              init = getTypeAttribut(tmp->elem->u.str, classe, methode, listeDecl, FALSE, FALSE);
            }
           /*printf("getTypeAttribut fin\n");*/
          }
      } 
      if(init == NULL)
      {
          /*FIXME dans le gettypeAttribut rajouter les cas pour "string" et 1*/
          char* message = NEW(SIZE_ERROR,char);
          /*printf("%s inconnu \n",tmp->elem->u.str);*/
          sprintf(message,"%s inconnu ",tmp->elem->u.str);
          pushErreur(message,classe,methode,NULL);
          return NULL; 
      }
      else
      {
        /*printf("INIT = %s\n", init->nom);*/
      }
  }
  else if(tmp->elem->op == CID)
  {
        isStatic = TRUE;
        agerer = TRUE;
        init = getClasseCopie(listClass, tmp->elem->u.str);
        if(init==NULL)
        {
          char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Inconnu %s",tmp->elem->u.str);
          pushErreur(message,classe,methode,NULL);
          return NULL; 
        }
  }
  else if(tmp->elem->op == KNEW)
  {
      char * nomClass = getChild(tmp->elem,0)->u.str;
      ClassP tmp = getClasseCopie(listClass, nomClass);
      if(tmp == NULL)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"La classe %s n'est pas declare ",nomClass);
        pushErreur(message,classe,methode,NULL);
        return NULL; 
      }
      else
      {
        init = tmp;
      }

  }
  else if(tmp->elem->op == STR)
  {
      /*printf("STR\n");*/
      init = getClasseCopie(listClass,"String");
  }
  else if(tmp->elem->op == Cste)
  {
      /*printf("CTSENTIER\n");*/
      init = getClasseCopie(listClass,"Integer");
  }
  else if(tmp->elem->recupType == 1)
  {
      /*printf("L'element est un type bizareeeee ===============\n");*/
      init = getType(tmp->elem,NULL,classe,methode,listeDecl);
      if(init != NULL)
      {
        /*printf("Toi la tu me soul hein : %s", init->nom);*/
      }
  }

  short etiquette = tmp->elem->op;
  ClassP tempoAffiche;
  while(tmp!=NULL)
  {
      tmp = tmp->next;
      if(tmp == NULL)
      {
          break;
      }
      TreeP tmpElem = tmp->elem;
      tempoAffiche = init;
      if(tmp->elem->op == CID || tmp->elem->op == KNEW || strcmp(tmp->elem->u.str,"super") == 0 || strcmp(tmp->elem->u.str,"this")==0 || tmp->elem->op == Cste || tmp->elem->op == STR)
      {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message," Identificateur de classe, instanciation, super ou this en plein milieu dans la classe %s: %s ",classe->name, tmp->elem->u.str);
          pushErreur(message,classe,methode,NULL);
          return NULL; 
      }
      
      if(tmp->elem->next != NULL || tmp->elem->isEnvoiMessage == TRUE)
      {
          if(init==NULL)
          {
             sprintf(message,"EnvoiMessage : il y a un probleme au niveau de celui ci");
             pushErreur(message,classe,methode,NULL);
             return NULL; 
          }
          else
          {
            if(tmp->elem->next == NULL)
            {
              /*printf("PROBLEME : LISTE ARG POUR LUI EST NUL");*/
            }
            init = appartient(init,tmpElem,TRUE,methode,listeDecl,tmp,etiquette,isStatic,agerer);
          }
           
          if(init==NULL)
          {   
              char* message = NEW(SIZE_ERROR,char);
              if(tempoAffiche == NULL)
              {
                sprintf(message,"EnvoiMessage : il y a un probleme au niveau de celui ci");
              }
              else
              {
                sprintf(message,"Erreur la methode %s n'appartient pas a %s. Veuillez verifier la classe",tmp->elem->u.str,tempoAffiche->name);
              }
              pushErreur(message,classe,methode,NULL);
              return NULL; 
          }               
              tempoAffiche = init;
      }
      else if(tmp->elem->isEnvoiMessage == FALSE)
      { 
          init = appartient(init,tmpElem,FALSE,methode,listeDecl,tmp,etiquette, isStatic,agerer);
          if(init == NULL)
          {
              char* message = NEW(SIZE_ERROR,char);
              if(tmp->elem == NULL)
              {
                sprintf(message,"Probleme envoie de message");
              }
              else if(tmp->elem != NULL && tempoAffiche != NULL)
              {
                sprintf(message,"Erreur la varibable  %s n'appartient pas a %s. Veuillez verifier la classe",tmp->elem->u.str,tempoAffiche->name); 
              }
              pushErreur(message,classe,methode,NULL);
              return NULL; 
          }
          tempoAffiche = init;
      }
      /*printf("etiquette avant\n");*/
      etiquette = tmp->elem->op;
      /*printf("etiquette apres\n");*/
  }
  return init;  
}


/*transformerAppel(appelMethode,liste,classe,methode,listeDecl)*/
ClassP transformerAppel(TreeP appelMethode, ClassP liste, ClassP courant, MethodeP methode, VarDeclP listeDecl)
{
  if(courant!=NULL)
  {
    courant = getClasseCopie(listClass,courant->name);
  }
  if(liste == NULL)
  {
    if(appelMethode->op != LISTARG)
    {
      ClassP getTypeRetour = getType(appelMethode,appelMethode,courant, methode, listeDecl);
      if(getTypeRetour==NULL)
      {
        char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 3");
        pushErreur(message,NULL,NULL,NULL);
        return NULL;
      }
      getTypeRetour = getClasseCopie(listClass,getTypeRetour->name);
      return getTypeRetour;
    }
    else
    {
      ClassP getTypeRetour = getType(getChild(appelMethode,1),appelMethode, courant, methode, listeDecl);
      if(getTypeRetour==NULL)
      {
        char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 4");
        pushErreur(message,NULL,NULL,NULL);
        return NULL;
      }
      getTypeRetour = getClasseCopie(listClass,getTypeRetour->name);
      ClassP POINTEUR = getTypeRetour; 
      while(POINTEUR!=NULL)
      {
        POINTEUR = POINTEUR->next;
      }
      liste = getTypeRetour;
    }
  }
  else
  {
    if(appelMethode->op != LIST)
    {
      Class tmp = *liste;
      ClassP getTypeRetour = getType(appelMethode,NULL, courant, methode, listeDecl);
      if(getTypeRetour != NULL)
      {
        getTypeRetour = getClasseCopie(listClass,getTypeRetour->name);
        liste = getTypeRetour;
        liste->next = NEW(1,Class);
        *liste->next = tmp;
        ClassP POINTEUR = liste;
        while(POINTEUR!=NULL)
        {
          POINTEUR = POINTEUR->next;
        }
        return liste;
      }
      else
      {
        char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 5");
        pushErreur(message,NULL,NULL,NULL);
        return NULL;
      }
    }
    else
    {
      Class tmp = *liste;
      ClassP getTypeRetour = getType(getChild(appelMethode,1),appelMethode, courant, methode, listeDecl);
      if(getTypeRetour!=NULL)
      {
        getTypeRetour = getClasseCopie(listClass,getTypeRetour->name);
        liste = getTypeRetour;
        liste->next = NEW(1,Class);
        *liste->next = tmp;
        /*return liste;*/
      }
      else
      {
        char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 5");
        pushErreur(message,NULL,NULL,NULL);
        return NULL;
      }
      
    }
  }
  return transformerAppel(getChild(appelMethode,0),liste,courant,methode,listeDecl);
}


ClassP appartient(ClassP mere, TreeP fille, bool isEnvoiMessage, MethodeP methode, VarDeclP listeDecl, LTreeP tmp,short etiquette, bool isStatic, bool agerer)
{  
  if(mere!=NULL)
  {
    mere = getClasseCopie(listClass,mere->name);
  }
  
  if(fille == NULL || mere == NULL){
    char* message = NEW(SIZE_ERROR,char);
    sprintf(message,"fonction tp.c appartient : Erreur Arbre");
    pushErreur(message,mere,methode,NULL);
    return NULL;
  }
  if(isEnvoiMessage)
  { 
    MethodeP listMeth = NULL;
    if(mere!=NULL)
    {
      /*printf("avant-----q-s-qs--s-q %s -> \n",mere->name);*/
    }
    else
    {
      /*printf("avant-----q-s-qs--s-q ");*/
    }

    if(mere->methodeL!=NULL)
    {
      /*printf("les listes ne sont pas null! \n");*/
      Methode copieConforme = *mere->methodeL;
      listMeth = NEW(1,Methode);
      *listMeth = copieConforme;
    }
    else
    {
        /*printf("La classe %s n'a pas de methode \n",mere->name );*/
        listMeth = mere->methodeL; 
        if(mere->lvar == NULL)
        {
          /*printf("TOUJOUR PAS La classe %s n'a pas de methode \n",mere->name );*/
        }
        else
        {
          /*printf("OUAH MAGIQUE\n");*/
        }
    }
    bool isVerifOk = FALSE;
    while(listMeth != NULL)
    {
      /*printf("NOMMETH %s\n",listMeth->name );
      printf("Je compare methode : %s et filles %s\n", listMeth->name,fille->u.str);*/
      if(strcmp(listMeth->name,fille->u.str)==0)
      {
        /*Verifie si les parametre de de listMeth->param & fille 
        printf("Allez isVerif  : ? %s \n",listMeth->name);
        printf("l'etiquette transmis ici : %d\n", etiquette);
        tmp -> elem -> suiavnt ??? */
        isVerifOk = getTypeMethode(listMeth->name,mere,etiquette,tmp->elem->next,methode,listeDecl,isStatic)!=NULL?TRUE:FALSE;
        /*printf("Fin isVerif %d \n",isVerifOk);*/

        if(isVerifOk)
        {
          return listMeth->typeRetour;
        }
        else
        {
          /*printf("MON VERIF N'EST PAS BON\n");*/
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,"Erreur la methode %s est mal appele ou n'existe pas",tmp->elem->u.str);
          pushErreur(message,mere,listMeth,NULL);
          return NULL;
        }
      }
      listMeth = listMeth->next;
    }
    char* message = NEW(SIZE_ERROR,char);
    sprintf(message,"Erreur la methode %s n'a pas ete trouvee",tmp->elem->u.str);
    pushErreur(message,mere,methode,NULL);
    return NULL;
  }
  else
  {
      if(dansCheckBlocMain)
      {
        return getTypeAttribut(tmp->elem->u.str, mere, methode, NULL,isStatic, agerer);  
      }
      else
      {
        return getTypeAttribut(tmp->elem->u.str, mere, methode, listeDecl,isStatic, agerer);  
      }    
  }
}

ClassP getTypeMethode(char * nom, ClassP classe, short precedant, TreeP appelMethode, MethodeP methode, VarDeclP listeDecl, bool isStatic)
{
  if(classe!=NULL)
  {
    classe = getClasseCopie(listClass,classe->name);
  }
  if(classe == NULL || nom == NULL)
  {
    char* message = NEW(SIZE_ERROR,char);
    sprintf(message,"tp.c getTypeMethode : Erreur Arbre");
    pushErreur(message,classe,methode,NULL);
    return NULL;
  }
  MethodeP tmp = classe->methodeL;
  while(tmp != NULL)
  {
    if(precedant == CID)
    {
      if(strcmp(nom,tmp->name) == 0 && tmp->isStatic && isStatic)
      {
        bool verifOk = compareParametreMethode(tmp->lvar,appelMethode, classe,methode, listeDecl, nom);
        if(verifOk)
        {
          return tmp->classApp;
        }
      }
    }
    else if(precedant == ID)
    {
      if(strcmp(nom,tmp->name)==0 && !tmp->isStatic && !isStatic)
      {
        bool verifOk = compareParametreMethode(tmp->lvar,appelMethode, classe, methode, listeDecl, nom);
        if(verifOk)
        {
          return tmp->classApp;
        }
      }
    }
    else if(precedant == STR || precedant == Cste)
    {
      bool verifOk = compareParametreMethode(tmp->lvar,appelMethode, classe,methode, listeDecl, nom);
      if(verifOk)
      {
        return tmp->classApp;
      }
    }
    else
    {
      bool verifOk = compareParametreMethode(tmp->lvar,appelMethode, classe,methode, listeDecl, nom);
       if(verifOk)
      {
        return tmp->classApp;
      }
    }

    tmp = tmp->next;
  }
  char *message = calloc(SIZE_ERROR,sizeof(char));
  sprintf(message,"La methode de classe ou statique %s est mal appelee",nom);
  pushErreur(message,NULL,NULL,NULL);
  return NULL;
}

bool checkListMethode(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl)
{
  /*check le constructeur*/
  if(courant->isExtend)
  {
    char * nomC = calloc(100,sizeof(char));
    sprintf(nomC,"constructeur %s",courant->classMere->name);
    /*check constructeur*/
    /*constructeur est un bloc, ici, on le traite comme une methode*/
    MethodeP methodeFakeConstructeur = NEW(1,Methode);
    methodeFakeConstructeur->corps = courant->constructor;
    methodeFakeConstructeur->name = calloc(100,sizeof(char));
    sprintf(methodeFakeConstructeur->name,"constructeur %s",courant->name);
    methodeFakeConstructeur->lvar = courant->params;

    bool constCorrecte = checkConstructeurExtends(courant->classMere->params,courant->appel_constructeur_mere,courant,methodeFakeConstructeur,NULL,nomC);
    constCorrecte = checkBloc(methodeFakeConstructeur->corps,NULL,courant,methodeFakeConstructeur,listeDecl,0) && constCorrecte;

    if(!constCorrecte)
    {
      char *message = calloc(100,sizeof(char));
      sprintf(message,"Erreur d'appel constructeur : %s mal appelee",courant->name);
      pushErreur(message,courant,NULL,NULL);
      return FALSE;
    }
  }
  else if(strcmp(courant->name,"Integer")!=0 && strcmp(courant->name,"String")!=0 && strcmp(courant->name,"Void")!=0)
  {
    char * nomC = calloc(100,sizeof(char));
    sprintf(nomC,"constructeur %s",courant->name);   
        
    MethodeP methodeFakeConstructeur = NEW(1,Methode);
    methodeFakeConstructeur->corps = courant->constructor;
    methodeFakeConstructeur->name = calloc(100,sizeof(char));
    sprintf(methodeFakeConstructeur->name,"constructeur %s",courant->name);
    methodeFakeConstructeur->lvar = courant->params;


    /* Pour liste de declaration, faire une fusion de liste champs et param constructeur*/
    bool constCorrecte = checkBloc(courant->constructor,NULL,courant,methodeFakeConstructeur,listeDecl,0);

    if(!constCorrecte)
    {
      char *message = calloc(100,sizeof(char));
      sprintf(message,"Erreur d'appel constructeur : %s mal appelee",classAnalysee->name);
      pushErreur(message,classAnalysee,NULL,NULL);
      return FALSE;
    }
  }


  if(courant->methodeL == NULL)
  {
    return TRUE;
  }


  Methode copie = *courant->methodeL;
  MethodeP tmp = NEW(1,Methode);
  *tmp = copie;

  while(tmp!=NULL)
  {
    IdP newId = makeId(tmp->name, Fonction, tmp->typeRetour, profondeur, rang);
    addId(listId, newId);
    rang++;
    printf("-- methode analysee de la classe %s: %s()\n", courant->name, tmp->name);
    
    /*traiter recursivement les methodes jusqu'a une methode fause se trouve*/
    if(!checkMethode(arbre,ancien,courant,tmp,listeDecl))
    {
      
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,"Erreur la methode %s() est mal construite",tmp->name);
      pushErreur(message,NULL,tmp,NULL);
      return FALSE;
    }
    tmp = tmp->next;
  }
  return TRUE;
}

bool checkMethode(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl)
{
    /*printf("class courant: %s\n", courant->name);*/
    if(methode->typeRetour==NULL)
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,"Erreur type de retour de la methode %s inconnu",methode->name);
      pushErreur(message,classAnalysee,methode,NULL);
      return FALSE;
    }
    bool statique = FALSE;
    bool redef = FALSE;
    bool final = FALSE;
    /*printf("Check la methode: %s\n",methode->name);*/
    bool typeRetour = (methode->typeRetour!=NULL);
    bool pvar = checkListOptArg(methode->lvar,methode);

    if(methode->isStatic)
    {
      statique = TRUE;
      redef = TRUE;
      final = TRUE;
    }
    else
    {
      statique = TRUE;
      if(methode->isRedef)
      {
        redef = methodeDansClasse(methode->classApp->classMere,methode);
        final = finalMethode(methode->classApp->classMere, methode);
        if(!final)
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,
                  "Erreur dans la methode override %s de la classe %s, celle de classe mere est final(ne peut pas etre redefinie)",
                  methode->name,methode->classApp->classMere->name);
          pushErreur(message,classAnalysee,methode,NULL);
          return FALSE;
        }
        if(!redef)
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,
                  "Erreur dans la methode override %s de la classe %s, la classe mere n'a pas cette methode",
                  methode->name,methode->classApp->classMere->name);
          pushErreur(message,classAnalysee,methode,NULL);
          return FALSE;
        }
      }
      else
      {
        redef = TRUE;
        final = TRUE;
      }
    }
    /*ajoute id de la fonction dans la liste*/
    /*IdP newId = NEW(1,Id);
    newId->name = methode->name;
    newId->nature = Fonction;
    newId->type = getClasseCopie(listClass, methode->typeRetour->name);
    newId->profondeur = profondeur;
    newId->rang = rang;

    bool existe = checkIdExiste(newId);
    if(existe == TRUE)
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,
              "Dans la classe %s, id %s ne peut pas designer a la fois un champ et la methode, cet id deja existe",
              courant->name, newId->name);
      pushErreur(message,courant,NULL,NULL);
      return FALSE;
    }
    else
    {
      bool addUnId = addId(listId, newId);
      if(addUnId == FALSE)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Cannot add to the listId");
        return FALSE;
      }
    }*/
    /*ajoute les parametres de methode dans listId*/

    VarDeclP tempParamsMethode = methode->lvar;
    int cptParams = 0;
    while(tempParamsMethode!=NULL)
    {
      IdP newId = NEW(1,Id);
      newId->name = tempParamsMethode->name;
      newId->nature = ParametreFon;
      newId->type = getClasseCopie(listClass, tempParamsMethode->type->name);
      newId->profondeur = profondeur+1;
      newId->rang = cptParams;

      bool existe = checkIdExiste(newId);
      
      if(existe == TRUE)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,
                "Deux parametres de la methode %s ont le meme nom %s",
                methode->name, newId->name);
        pushErreur(message,courant,NULL,NULL);
        return FALSE;
      }
      else
      {
        bool addUnId = addId(listId, newId);
        if(addUnId == FALSE)
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,"Cannot add to the listId");
          return FALSE;
        }
      }
      cptParams++;
      tempParamsMethode = tempParamsMethode->next;
    }
    /*if(strcmp(courant->name, "A") == 0)
    {
      printf("Class:%s\n", courant->name);
      IdP tempList = listId;
      while(tempList != NULL)
      {
        printf("ID: %s, kind: %d, type: %s, profondeur : %d, rang: %d\n", tempList->name, 
          tempList->nature,
          tempList->type->name,
          tempList->profondeur, tempList->rang);
        tempList = tempList->next;
      }
    }*/

    bool bloc = FALSE;     

    if(methode->corps==NULL)
    {
      bloc = TRUE;
    }
    else
    {
      if(methode->corps->op == AFF)
      {
        ClassP retourAffect = getType(getChild(methode->corps,0),arbre,courant,methode,NULL);
        if(equalsType(methode->typeRetour,retourAffect))
        {
          bloc = TRUE;
        }
        else
        {
          bloc = FALSE;
        }
      }
      else
      {
        if(cptParams == 0)
          bloc = checkBloc(methode->corps,arbre,courant,methode,listeDecl, 0);
        else
          bloc = checkBloc(methode->corps,arbre,courant,methode,listeDecl, cptParams-1);
      }     
    }
    moveIdBlocFromListParProfondeur(profondeur);
    /*printf("typeRetour %d statique %d redef %d pvar %d bloc ? : %d\n",typeRetour,statique,redef, pvar, bloc );*/
    return (bloc && typeRetour && final && statique && redef && pvar);
}

bool checkListOptArg(VarDeclP var, MethodeP methode)
{
    VarDeclP tmp = var;

    while(tmp!=NULL)
    {
      if(tmp->type==NULL)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Verifier les argument de la methode %s",methode->name);
        pushErreur(message,methode->classApp,methode,NULL);
        return FALSE;
      }
      tmp = tmp->next;
    }

    return TRUE;   
}

/* Renvoi vrai si la methode est dans la classe, faux sinon */
bool methodeDansClasse(ClassP classe, MethodeP methode){
  if(classe==NULL || methode==NULL)
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 21");
    return FALSE;
  }
  MethodeP tmp_liste_methodes_classe = getClasseCopie(listClass,classe->name)->methodeL;
  MethodeP tmp_liste_methode = methode;
  if(methode == NULL) return FALSE;

  while(tmp_liste_methodes_classe != NULL){
    /* si 2 methodes ont le meme noms, les memes classes de retour (meme noms) et memes param ==> meme methode */
    if(strcmp(tmp_liste_methodes_classe->name, tmp_liste_methode->name)==0 && strcmp(tmp_liste_methodes_classe->typeRetour->name, tmp_liste_methode->typeRetour->name)==0 && memeVar(tmp_liste_methodes_classe->lvar, tmp_liste_methode->lvar)==TRUE ){
      return TRUE;
    }
    tmp_liste_methodes_classe = tmp_liste_methodes_classe->next;
  }

  return FALSE;
}

/* Renvoi vrai si la methode peut etre redefinie, faux sinon(celle de la classeMere est final) */
bool finalMethode(ClassP classe, MethodeP methode){
  if(classe==NULL || methode==NULL)
  {
    char *message = calloc(SIZE_ERROR,sizeof(char));sprintf(message,"Erreur init 21");
    return FALSE;
  }
  MethodeP tmp_liste_methodes_classe = getClasseCopie(listClass,classe->name)->methodeL;
  MethodeP tmp_liste_methode = methode;
  if(methode == NULL) return FALSE;

  while(tmp_liste_methodes_classe != NULL){
    /* si 2 methodes ont le meme noms, les memes classes de retour (meme noms) et memes param ==> meme methode */
    if(strcmp(tmp_liste_methodes_classe->name, tmp_liste_methode->name)==0 && strcmp(tmp_liste_methodes_classe->typeRetour->name, tmp_liste_methode->typeRetour->name)==0 && memeVar(tmp_liste_methodes_classe->lvar, tmp_liste_methode->lvar)==TRUE ){
      if(tmp_liste_methodes_classe->isFinal == TRUE)
        return FALSE;
    }
    tmp_liste_methodes_classe = tmp_liste_methodes_classe->next;
  }

  return TRUE;
}

bool checkBloc(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc)
{
  bool resultat = FALSE;
  char* message = NEW(SIZE_ERROR,char);
  /*printf("check BLOC\n");*/
  if(arbre == NIL(Tree) || arbre == NULL)
  {
    return TRUE; 
  }

  /*verifier si c'est un bloc vide*/
  int nbChildrenArbre = arbre->nbChildren;
  int i = 0;
  int nombreNULL = 0;
  while(i<nbChildrenArbre)
  {
    if(getChild(arbre,i) == NULL)
      nombreNULL++;
    i++;
  }
  if(nombreNULL == nbChildrenArbre)
    return TRUE;

  /*printf("checkBloc, OP: %d\n", arbre->op);
  printf("class:%s\n", courant->name);*/
  if(arbre->op == BLOCLAB)
  {
    profondeur++;
    char *lableBloc = getChild(arbre, 0)->u.str;
    ClassP typeRetourBloc = getClasseCopie(listClass, getChild(arbre,1)->u.str);
    /*ajoute id de bloc dans la liste*/
    IdP newId = NEW(1,Id);
    newId->name = lableBloc;
    newId->nature = BlocLable;
    newId->type = getClasseCopie(listClass, typeRetourBloc->name);
    newId->profondeur = profondeur;
    newId->rang = rangBloc;
    rangBloc++;

    bool existe = checkIdBlocExisteParNom(lableBloc);
  
    if(existe == TRUE)
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,
              "Deux blocs de la methode %s() ne peuvent pas avoir le meme label: %s",
              methode->name,newId->name);
      pushErreur(message,NULL,NULL,NULL);
      return FALSE;
    }
    else
    {
      bool addUnId = addId(listId, newId);
      if(addUnId == FALSE)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Cannot add to the listId");
        return FALSE;
      }
    }

    /*IdP tempList = listId;
    while(tempList != NULL)
    {
        printf("ID: %s, kind: %d, type: %s, profondeur : %d, rang: %d\n", tempList->name, 
        tempList->nature,
        tempList->type->name,
        tempList->profondeur, tempList->rang);
        tempList = tempList->next;
    }*/

    /*printf("bloc lable:%s\n", lableBloc);
    printf("bloc type:%s\n", typeRetourBloc->name);*/
    /*l'analyse eListOpt*/
    TreeP eListOpt = getChild(arbre,2);

    /*eListOpt -> vide*/
    if(eListOpt->op == LIST && getChild(eListOpt,0)->u.str != NULL && getChild(eListOpt,0)->op == ID && strcmp(getChild(eListOpt,0)->u.str, "void") == 0)
    {
      if(strcmp(typeRetourBloc->name, "Void") != 0)  
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,
              "Dans le bloc, le bloc nomme %s est vide, mais le type de retour n'est pas Void",
              lableBloc);
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
      }
    }
    else 
    {
        TreeP eList = eListOpt;
        if(eList->op == LIST && getChild(eList,1) != NIL(Tree)  
          && getChild(eList,1)->nbChildren == 2 && getChild(eList,1)->op == LIST
          && getChild(getChild(eList,1),0)->u.str != NULL && getChild(getChild(eList,1),0)->op == ID && strcmp(getChild(getChild(eList,1),0)->u.str, "void") == 0)
        {
          TreeP d = getChild(eList,0); /*d avec sm dans le bloc*/
          if(d->op == LOCVAR)
          {
            bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkLocalVar == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
          else
          {
            bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkExpr == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
      }
      else if(eList->op == LIST && getChild(eList,1) == NIL(Tree))
      {
          TreeP d = getChild(eList,0); /*d sans sm dans le bloc*/
          if(d->op == LOCVAR)
          {
            bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkLocalVar == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
          else
          {
            bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            /*printf("%d\n", checkExpr);*/
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkExpr == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
      }
      else
      {
          /*une liste de declarations de variables ou expressions*/
          TreeP d = getChild(eList,0);
          TreeP eListSuite = getChild(eList,1);
          if(d->op == LOCVAR)
          {
            bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            if(checkLocalVar == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
          else
          {
            bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            if(checkExpr == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }

          bool elistSuiteOK = checkEListSuite(eListSuite, eList, courant, methode, listeDecl, rangBloc) && resultat;
          if(!elistSuiteOK)
          { 
            sprintf(message,"Dans le bloc, probleme d'expression");
            pushErreur(message,courant,methode,listeDecl);
            resultat = FALSE; 
          }
      }
    }
    profondeur--;
  }
  else
  {
    if(arbre->op == BLOCANO)
    {
      profondeur++;
      TreeP eListOpt = getChild(arbre,2);
      TreeP eList = eListOpt;

      if(eListOpt->op == LIST && getChild(eListOpt,1) != NIL(Tree)
        && getChild(eListOpt,1)->nbChildren == 2 && getChild(eListOpt,1)->op == LIST
        && getChild(eListOpt,1)->u.str != NULL && strcmp(getChild(eListOpt,1)->u.str, "void")==0)
      {
        resultat = TRUE;
      }
      else
      {
        if(eList->op == LIST && getChild(eList,1) != NIL(Tree)  
        && getChild(eList,1)->nbChildren == 2 && getChild(eList,1)->op == LIST
        && getChild(getChild(eList,1),0)->u.str != NULL && getChild(getChild(eList,1),0)->op == ID && strcmp(getChild(getChild(eList,1),0)->u.str, "void") == 0)
        {
          TreeP d = getChild(eList,0); /*d avec sm dans le bloc*/
          if(d->op == LOCVAR)
          {
            bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkLocalVar == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
          else
          {
            bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkExpr == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
        }
        else if(eList->op == LIST && getChild(eList,1) == NIL(Tree))
        {
          TreeP d = getChild(eList,0); /*d sans sm dans le bloc*/
          if(d->op == LOCVAR)
          {
            bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkLocalVar == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
          else
          {
            bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            moveIdFromListParProfondeur(profondeur);
            if(checkExpr == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
        }
        else
        {
          /*une liste de declarations de variables ou expressions*/
          TreeP d = getChild(eList,0);
          TreeP eListSuite = getChild(eList,1);
          if(d->op == LOCVAR)
          {
            bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            if(checkLocalVar == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }
          else
          {
            bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
            rangBloc++;
            if(checkExpr == TRUE)
              resultat = TRUE;
            else
              resultat = FALSE;
          }

          bool elistSuiteOK = checkEListSuite(eListSuite, eList, courant, methode, listeDecl, rangBloc) && resultat;
          if(!elistSuiteOK)
          { 
            sprintf(message,"Dans le bloc, probleme d'expression");
            pushErreur(message,courant,methode,listeDecl);
            resultat = FALSE; 
          }  
        }
      }
      profondeur--;
    }
  }
  return resultat;
}

bool checkEListSuite(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc)
{  
  bool resultat = FALSE;
  bool checkSuite = TRUE;
  TreeP eList = arbre;
  TreeP eListOpt = NULL;
  bool isBlocAgain = FALSE;
  char *lableBloc = NULL;
  ClassP typeRetourBloc = NULL;

  if(eList->op == BLOCLAB || eList->op == BLOCANO)
  {
    isBlocAgain = TRUE;
    profondeur++;
    if(eList->op == BLOCLAB)
    {
      lableBloc = getChild(eList,0)->u.str;
      typeRetourBloc = getClasseCopie(listClass, getChild(eList,1)->u.str);
      eListOpt = getChild(eList,2);
      IdP newId = NEW(1,Id);
      newId->name = lableBloc;
      newId->nature = BlocLable;
      newId->type = getClasseCopie(listClass, typeRetourBloc->name);
      newId->profondeur = profondeur;
      newId->rang = rangBloc;
      rangBloc++;

      bool existe = checkIdBlocExiste(newId);
      printf("existe?:%d\n", existe);
      if(existe == TRUE)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,
                "Deux blocs d'une methode ne peuvent pas avoir le meme label %s",
                newId->name);
        pushErreur(message,NULL,NULL,NULL);
        return FALSE;
      }
      else
      {
        bool addUnId = addId(listId, newId);
        if(addUnId == FALSE)
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,"Cannot add to the listId");
          return FALSE;
        }
      }

      if(eListOpt->op == LIST && getChild(eListOpt,0)->u.str != NULL && strcmp(getChild(eListOpt,0)->u.str, "void") == 0)
      {
        if(strcmp(typeRetourBloc->name, "Void") != 0)
        {
          char* message = NEW(SIZE_ERROR,char);
          sprintf(message,
                "Dans le bloc, le bloc nomme %s est vide, mais le type de retour n'est pas Void",
                lableBloc);
          pushErreur(message,NULL,NULL,NULL);
          return FALSE;
        }
      }
      eList = eListOpt;
    }
    else
    {
      TreeP eListOpt = getChild(eList,2);
      if(eListOpt->op == LIST && getChild(eListOpt,1) != NIL(Tree)
        && getChild(eListOpt,1)->nbChildren == 2 && getChild(eListOpt,1)->op == LIST
        && getChild(eListOpt,1)->u.str != NULL && strcmp(getChild(eListOpt,1)->u.str, "void")==0)
          return TRUE;
      eList = eListOpt;
    }
  }

  /*Les codes au-dessus sert juste a parcourir l'arbre a partir du BLOCLAB/BLOCANO jusqu'a eList*/  
  
  if(eList->op == LIST && getChild(eList,1) != NIL(Tree)  
  && getChild(eList,1)->nbChildren == 2 && getChild(eList,1)->op == LIST
  && getChild(getChild(eList,1),0)->u.str != NULL && getChild(getChild(eList,1),0)->op == ID && strcmp(getChild(getChild(eList,1),0)->u.str, "void") == 0)
  {
    TreeP d = getChild(eList,0); /*d avec sm dans le bloc*/
    if(d->op == LOCVAR)
    {
      bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
      rangBloc++;
      moveIdFromListParProfondeur(profondeur);
      if(checkLocalVar == TRUE)
        resultat = TRUE;
      else
        resultat = FALSE;
    }
    else
    {
      bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
      rangBloc++;
      moveIdFromListParProfondeur(profondeur);
      if(checkExpr == TRUE)
        resultat = TRUE;
      else
        resultat = FALSE;
    }
  }
  else if(eList->op == LIST && getChild(eList,1) == NIL(Tree))
  {
    TreeP d = getChild(eList,0); /*d sans sm dans le bloc*/
    if(d->op == LOCVAR)
    {
      bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
      rangBloc++;
      moveIdFromListParProfondeur(profondeur);
      if(checkLocalVar == TRUE)
        resultat = TRUE;
      else
        resultat = FALSE;
    }
    else
    {
      bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
      rangBloc++;
      moveIdFromListParProfondeur(profondeur);
      if(checkExpr == TRUE)
        resultat = TRUE;
      else
        resultat = FALSE;
    }
  }
  else
  {
    TreeP d = getChild(eList,0); 
    if(d->op == LOCVAR)
    {
      bool checkLocalVar = checkUneDeclarationDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
      rangBloc++;
      if(checkLocalVar == TRUE)
        resultat = TRUE;
      else
        resultat = FALSE;
    }
    else
    {
      bool checkExpr = checkUneExprDansBloc(d, arbre, courant, methode, listeDecl, rangBloc);
      rangBloc++;
      if(checkExpr == TRUE)
        resultat = TRUE;
      else
        resultat = FALSE;
    }
    checkSuite = checkEListSuite(getChild(eList,1), eList, courant, methode, listeDecl, rangBloc);
  }
  if(isBlocAgain == TRUE)
  {
    moveIdFromListParProfondeur(profondeur);
    profondeur--;
  }
  return resultat && checkSuite;
}


/*check une declaration de variable dans le bloc*/
bool checkUneDeclarationDansBloc(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc)
{
  if(arbre->op == LOCVAR)
  {
    rangBloc++;
    VarDeclP localVar = getChild(arbre,0)->u.lvar;
    TreeP initOpt = getChild(arbre,1);
    char *name = localVar->name;
    ClassP type = localVar->type;

    /*printf("localVar name: %s\n", name);
    printf("localVar type: %s\n", type->name);*/

    if(type == NULL)
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,
              "Dans la declarations de variable, le type de variable %s n'existe pas",
              localVar->name);
      pushErreur(message,NULL,NULL,localVar);
      return FALSE;
    }

    ClassP typeIni = getType(initOpt,arbre,courant,methode,listeDecl);

    if(typeIni != NULL)
    {
      if(type != NULL && !equalsType(type,typeIni))
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Erreur affectation de variable %s de type %s par un %s", name, type->name,typeIni->name);
        pushErreur(message,courant,methode,localVar);
      }
    }

    IdP newId = NEW(1,Id);
    newId->name = localVar->name;
    newId->nature = Variable;
    newId->type = getClasseCopie(listClass, type->name);
    newId->profondeur = profondeur;
    newId->rang = rangBloc;

    bool existe = checkIdExiste(newId);
    if(existe == TRUE)
    {
      char* message = NEW(SIZE_ERROR,char);
      sprintf(message,
              "Dans la declarations de variable %s, cet identificateur deja existe!",
              localVar->name);
      pushErreur(message,NULL,NULL,localVar);
      return FALSE;
    }
    else
    {
      bool addUnId = addId(listId, newId);
      if(addUnId == FALSE)
      {
        char* message = NEW(SIZE_ERROR,char);
        sprintf(message,"Cannot add to the listId");
        return FALSE;
      }
    }

    /*printf("Class:%s\n", courant->name);
    IdP tempList = listId;
    while(tempList != NULL)
    {
      printf("ID: %s, kind: %d, type: %s, profondeur : %d, rang: %d\n", tempList->name, 
        tempList->nature,
        tempList->type->name,
        tempList->profondeur, tempList->rang);
        tempList = tempList->next;
    }*/
  }
  return TRUE;
}

bool checkUneExprDansBloc(TreeP arbre, TreeP ancien, ClassP courant, MethodeP methode, VarDeclP listeDecl, int rangBloc)
{

  if(arbre == NULL)
    return TRUE;

  char* message = NEW(SIZE_ERROR,char);

  /*printf("d-op:%d\n", arbre->op);*/

  if(arbre->op == BLOCLAB || arbre->op == BLOCANO)
  {
    bool checkBlocInterne = checkBloc(arbre, ancien, courant, methode, listeDecl, rangBloc);
    if(!checkBlocInterne)
    {
      sprintf(message,"Erreur dans le bloc englobant.");
      pushErreur(message,courant,methode,listeDecl);
    }
    return checkBlocInterne;
  }

  /**/
  if(arbre->nbChildren == 0)
  {
      /*IdP tempList = listId;
      while(tempList != NULL)
      {
          printf("ID: %s, kind: %d, type: %s, profondeur : %d, rang: %d\n", tempList->name, 
          tempList->nature,
          tempList->type->name,
          tempList->profondeur, tempList->rang);
          tempList = tempList->next;
      }*/
      if(arbre->op == ID)
      {
        if(arbre->u.str != NULL)
        {
          char *name = arbre->u.str;

          bool idExiste = checkIdVarExisteParNom(name);
          
          if(!idExiste)
          {
            sprintf(message,"Dans le bloc de la methode %s() de la classe %s, identificateur %s n'est pas defini", methode->name, courant->name, name);
            pushErreur(message,courant,methode,listeDecl);
            return FALSE;
          }
          else
          {
            return TRUE;
          }
        }
      }
      else if(arbre->op == Cste)
      {
        return TRUE; /*type avec bloc?*/
      }
      else
      {
        return (getType(arbre,NULL,courant,methode,listeDecl)!=NULL);
      }  
  }

  ClassP type = NULL;
  ClassP type1 = NULL;
  ClassP type2 = NULL;
  TreeP cible = NULL;
  TreeP exprAff = NULL;

  /*IF-THEN-ELSE*/
  TreeP condition = NULL;
  TreeP e1 = NULL;
  TreeP e2 = NULL;

  /*PLUS/MINUS UNAIRE*/
  TreeP ex = NULL;

  /*KNEW*/
  char *nomClass = NULL;
  ClassP tmp = NULL;

  bool checkE1 = FALSE;
  bool checkE2 = FALSE;

  char* name = NULL;

  LTreeP liste = NULL;
  ClassP typeMessage = NULL;

  char* yieldNom = NULL;
  TreeP yieldExpr = NULL;


  bool resultat = FALSE;

  TreeP e;
  e = arbre;  

  switch(e->op)
  {
    case AFF:
      cible = getChild(e,0);
      exprAff = getChild(e,1);
      if(cible->op == ID && cible->u.str != 0)
      {
        char *nameID = cible->u.str;
        bool idExiste = checkIdVarExisteParNom(nameID);
                
        if(!idExiste)
        {
          sprintf(message,"Dans le bloc, erreur d'affectation, id %s n'est pas defini", nameID);
          pushErreur(message,courant,methode,listeDecl);
          return FALSE;
        }
        ClassP typeID = getTypeIdVar(nameID);
        ClassP typeExpr = NULL;
        bool checkExprDroit = checkUneExprDansBloc(exprAff, e, courant,methode, listeDecl,rangBloc);
        if(checkExprDroit)
          typeExpr = getType(exprAff, e, courant, methode, listeDecl);

        if(typeID != NULL && typeExpr != NULL && !equalsType(typeID, typeExpr))
        {
          sprintf(message,"Dans le bloc, expression d'affectation, probleme de typage : %s par %s", typeID->name, typeExpr->name);
          pushErreur(message,courant,methode,listeDecl);
          return FALSE;
        }
        return TRUE;
      }
      else if(cible->op == SELECT || cible->op == CSELECT)
      {
        /*a regler!*/
        LTreeP liste = NULL;
        ClassP type = NULL;
        liste = transFormSelectOuEnvoi(cible,liste);
        type = estCoherentEnvoi(liste, courant, methode,listeDecl);

        if(type == NULL)
        {
          sprintf(message,"Dans le bloc, expression d'affectation, probleme de select");
          pushErreur(message,courant,methode,listeDecl);
          return FALSE;
        }
      }

      type1 = getType(getChild(e,0), e, courant, methode, listeDecl);
      type2 = getType(getChild(e,1), e, courant, methode, listeDecl);
      if(!equalsType(type1, type2))
      {
        if(type1!=NULL)
        {
          if(type2!=NULL)
          {
            sprintf(message,"Expression d'affectation : affectation incorrecte entre deux types differents %s & %s",type1->name,type2->name);
          }
          else
            sprintf(message,"Expression d'affectation : affectation incorrecte entre deux types differents : %s et un type inconnu",type1->name);
        }
        else
        {
          if(type2!=NULL)
          {
            sprintf(message,"Expression d'affectation : affectation incorrecte entre deux types differents : un type inconnu et %s",type2->name);
          }
          else
          {
            sprintf(message,"Expression d'affectation : affectation incorrecte, deux types inconnus");
          }
        }
        pushErreur(message,courant,methode,listeDecl);
        resultat = FALSE;
      }
      else
      {
        resultat = TRUE;
      }

      if(!resultat)
      {
        sprintf(message,"Instruction : erreur d'affectation");
        pushErreur(message,courant,methode,listeDecl);
      }
      return resultat;
    break;

    case ITE:
      if(getChild(e,2) != NIL(Tree)) /*if --- then --- else*/
      {
        condition = getChild(e,0);
        e1 = getChild(e,1);
        e2 = getChild(e,2);
        ClassP typeCondition  = getType(condition, e, courant, methode, listeDecl);
        if(typeCondition == NULL)
        {
          sprintf(message,"Dans expression IF-THEN-ELSE, probleme dans la condition");
          pushErreur(message,courant,methode,listeDecl);
          resultat = FALSE;
          return resultat;
        }
        else
        {
          if(!equalsType(typeCondition, getClasseCopie(listClass, "Integer")))
          {
              sprintf(message,"Dans le bloc, la condition dans IF-THEN-ELSE n'est pas un Integer");
              pushErreur(message,courant,methode,listeDecl);
              resultat = FALSE;
              return resultat;
          }
        }

        checkE1 = checkUneExprDansBloc(e1, e, courant, methode, listeDecl, rangBloc);
        checkE2 = FALSE;
        if(!checkE1)
        {
          sprintf(message,"Dans le bloc, IF-THEN-ELSE, l'expression dans la branche THEN n'est pas bonne");
          pushErreur(message,courant,methode,listeDecl);
          resultat = FALSE;
          return resultat;
        }
        else
        {
          checkE2 = checkUneExprDansBloc(e2, e, courant, methode, listeDecl, rangBloc);
          if(!checkE2)
          {
            sprintf(message,"Dans le bloc, IF-THEN-ELSE, l'expression dans la branche ELSE n'est pas bonne");
            pushErreur(message,courant,methode,listeDecl);
            resultat = FALSE;
            return resultat;
          }
        }
      }
      else /*if --- then*/
      {
        condition = getChild(e,0);
        e1 = getChild(e,1);
        ClassP typeCondition  = getType(condition, e, courant, methode, listeDecl);
        if(typeCondition == NULL)
        {
          sprintf(message,"Dans expression IF-THEN-ELSE, probleme dans la condition");
          pushErreur(message,courant,methode,listeDecl);
          resultat = FALSE;
          return resultat;
        }
        else
        {
          if(!equalsType(typeCondition, getClasseCopie(listClass, "Integer")))
          {
              sprintf(message,"Dans le bloc, la condition dans IF-THEN-ELSE n'est pas un Integer");
              pushErreur(message,courant,methode,listeDecl);
              resultat = FALSE;
              return resultat;
          }
        }

        checkE1 = checkUneExprDansBloc(e1, e, courant, methode, listeDecl, rangBloc);
        if(!checkE1)
        {
          sprintf(message,"Dans le bloc, IF-THEN-ELSE, l'expression dans la branche THEN n'est pas bonne");
          pushErreur(message,courant,methode,listeDecl);
          resultat = FALSE;
          return resultat;
        }
      }
      resultat = TRUE; /*sans erreur*/
      return resultat;
    break;

    case WHILEDO:
      condition = getChild(e,0);
      e1 = getChild(e,1);
      ClassP typeCondition  = getType(condition, e, courant, methode, listeDecl);
      if(typeCondition == NULL)
      {
        sprintf(message,"Dans le bloc, l'expression WHILE-DO, probleme dans la condition");
        pushErreur(message,courant,methode,listeDecl);
        resultat = FALSE;
        return resultat;
      }
      else
      {
        if(!equalsType(typeCondition, getClasseCopie(listClass, "Integer")))
        {
            sprintf(message,"Dans le bloc, l'expression WHILE-DO, la condition n'est pas un Integer");
            pushErreur(message,courant,methode,listeDecl);
            resultat = FALSE;
            return resultat;
        }
      }

      checkE1 = checkUneExprDansBloc(e1, e, courant, methode, listeDecl, rangBloc);
      if(!checkE1)
      {
        sprintf(message,"Dans le bloc, l'expression WHILE-DO, La branche DO n'est pas bonne");
        pushErreur(message,courant,methode,listeDecl);
        resultat = FALSE;
        return resultat;
      }

      resultat = TRUE;
      return resultat;
    break;

    case UMINUS:
    case UPLUS:
      ex = getChild(e,0);
      bool checkCetteExpr = checkUneExprDansBloc(ex,e,courant,methode,listeDecl,rangBloc);
      if(!checkCetteExpr)
      {
        sprintf(message,"Dans le bloc, l'expression PLUS/MINUS UNIAIR n'est pas bonne");
        pushErreur(message,courant,methode,listeDecl);
        resultat = FALSE;
        return resultat;
      }

      type = getType(ex,e,courant,methode,listeDecl);

      if(type!=NULL && strcmp(type->name,"Integer")!=0)
      {
        sprintf(message,"Dans le bloc, erreur: plus unaire n'est pas applicable sur %s car ce n'est pas un entier",type->name);
        pushErreur(message,type,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      else if(type==NULL)
      {
        sprintf(message,"Erreur plus unaire de type");
        pushErreur(message,type,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      else
      {
        resultat = TRUE;
        return resultat;
      }
    break;

    case ADD: 
    case MINUS: 
    case MUL:
    case DIV:
      e1 = getChild(e,0);
      e2 = getChild(e,1);
      checkE1 = checkUneExprDansBloc(e1, e, courant, methode, listeDecl, rangBloc);
      checkE2 = checkUneExprDansBloc(e2, e, courant, methode, listeDecl, rangBloc);
      if(!checkE1)
      {
        sprintf(message,"Erreur expression binaire dans le bloc, expression a gauche");
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      else
      {
        if(!checkE2)
        {
          sprintf(message,"Erreur expression binaire dans le bloc, expression a droit");
          pushErreur(message,NULL,NULL,NULL);
          resultat = FALSE;
          return resultat;
        }
      }

      type = getType(e1,e,courant,methode,listeDecl);
      type2 = getType(e2,e,courant,methode,listeDecl);
      /*printf("type1: %s, type2: %s\n", type->name, type2->name);*/
      /*printf("type = NULL ? %s type2 = NULL ? %s\n",type->name,type2->name);*/
      if(equalsType(type,type2)){
         resultat = TRUE;
      }
      else
      {
        if(type!=NULL)
        {
          if(type2!=NULL)
          {
            sprintf(message,"Dans le bloc, erreur operation arithmetique entre un objet de type %s et %s",type->name,type2->name);
          }
          else
          {
            sprintf(message,"Dans le bloc, erreur operation arithmetique, le type a cote de %s n'est pas reconnu",type->name);
          }
        }
        else
        {
          sprintf(message,"Dans le bloc, erreur operation arithmetique, deux types iconnus");
        }
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
      }
      return resultat;
    break;

    case AND:
      e1 = getChild(e,0);
      e2 = getChild(e,1);
      checkE1 = checkUneExprDansBloc(e1, e, courant, methode, listeDecl, rangBloc);
      checkE2 = checkUneExprDansBloc(e2, e, courant, methode, listeDecl, rangBloc);
      if(!checkE1)
      {
        sprintf(message,"Erreur expression & dans le bloc, expression a gauche");
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      else
      {
        if(!checkE2)
        {
          sprintf(message,"Erreur expression & dans le bloc, expression a droit");
          pushErreur(message,NULL,NULL,NULL);
          resultat = FALSE;
          return resultat;
        }
      }

      type = getType(e1,e,courant,methode,listeDecl);
      type2 = getType(e2,e,courant,methode,listeDecl);
      if(type!=NULL && strcmp(type->name,"String")!=0)
      {  
        sprintf(message,"Erreur expression & dans le bloc, le type a gauche n'est pas String");
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
        return resultat;
      } 
      if(type2!=NULL && strcmp(type2->name,"String")!=0)
      {
        sprintf(message,"Erreur expression & dans le bloc, le type a gauche n'est pas String");
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
        return resultat;   
      }
      resultat = TRUE;
      return resultat;
    break;

    case NE :
    case EQ :
    case LT :
    case LE :
    case GT :
    case GE :
      e1 = getChild(e,0);
      e2 = getChild(e,1);
      checkE1 = checkUneExprDansBloc(e1, e, courant, methode, listeDecl, rangBloc);
      checkE2 = checkUneExprDansBloc(e2, e, courant, methode, listeDecl, rangBloc);
      if(!checkE1)
      {
        sprintf(message,"Erreur expression RELOP dans le bloc, expression a gauche");
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      else
      {
        if(!checkE2)
        {
          sprintf(message,"Erreur expression RELOP dans le bloc, expression a droit");
          pushErreur(message,NULL,NULL,NULL);
          resultat = FALSE;
          return resultat;
        }
      }

      type = getType(e1,e,courant,methode,listeDecl);
      type2 = getType(e2,e,courant,methode,listeDecl);
      if(equalsType(type,type2) && (strcmp(type->name,"Integer") == 0 || strcmp(type->name,"Integer")==0))
      {
        resultat = TRUE;
      }
      else
      {
        if(type!=NULL)
        {
          if(type2!=NULL)
          {
            sprintf(message,"Dans le bloc, erreur operation de comparaison entre un objet de type %s et %s",type->name,type2->name);
            pushErreur(message,NULL,NULL,NULL);
            resultat = FALSE;
            return resultat;
          }
          else
          {
            sprintf(message,"Dans le bloc, erreur operation de comparaison, le type a cote de %s n'est pas reconnu",type->name);
            pushErreur(message,NULL,NULL,NULL);
            resultat = FALSE;
            return resultat;
          }
        }
        else
        {
          if(type2!=NULL)
          {
            sprintf(message,"Dans le bloc, erreur operation de comparaison, le type a cote de %s n'est pas reconnu",type2->name);
            pushErreur(message,NULL,NULL,NULL);
            resultat = FALSE;
            return resultat;
          }
          else
          {
            sprintf(message,"Dans le bloc, erreur operation de comparaison, les types des deux expressions inconnues");
            pushErreur(message,NULL,NULL,NULL);
            resultat = FALSE;
            return resultat;
          }
        }
        sprintf(message,"Dans le bloc, erreur operation de comparaison, les types des deux expressions ne sont pas Integer");
        pushErreur(message,NULL,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      return resultat;
    break;

    case KNEW:
      nomClass = getChild(e,0)->u.str;
      tmp = getClasseCopie(listClass,nomClass);
      if(tmp == NULL)
      {
        sprintf(message,"Dans le bloc, erreur d'instanciation de l'objet: classe %s n'existe pas",nomClass);
        pushErreur(message,type,NULL,NULL);
        resultat = FALSE;
        return resultat;
      }
      else
      {
        bool instCorrecte = FALSE;
        char *nomC = calloc(100,sizeof(char));
        sprintf(nomC,"constructeur %s",nomClass);
        
        instCorrecte = compareParametreMethode(tmp->params,getChild(e,1),courant,methode,listeDecl,nomC);
        if(!instCorrecte)
        {
          sprintf(message,"Dans le bloc, erreur d'instanciation : %s mal appelee, les arguments ne correspondent pas",nomClass);
          pushErreur(message,type,NULL,NULL);
          resultat = FALSE;
          return resultat;
        }
        else
        {
          resultat = TRUE;
        }
      }
      return resultat;
    break;

    case STR:
      return TRUE;
    break;

    case Cste:
      return TRUE;
    break;

    case ID:
      printf("here...");
      name = getChild(e,0)->u.str;
      if(name != NULL)
      {
        bool idExiste1= checkIdVarExisteParNom(name);
        if(idExiste1)
        {
          resultat = TRUE;
          return resultat;
        }
        else
        {
          sprintf(message,"Dans le bloc, identificateur %s n'est pas defini avant",name);
          pushErreur(message,NULL,NULL,NULL);
          resultat = FALSE;
          return resultat;
        }
      }
    break;

    case ENVOI:
    case CENVOI:
      
      liste = transFormSelectOuEnvoi(e,liste);
      typeMessage = estCoherentEnvoi(liste, courant, methode,listeDecl);

      if(typeMessage == NULL)
      {
        sprintf(message,"Dans le bloc, probleme d'envoie de message");
        pushErreur(message,courant,methode,listeDecl);
        return FALSE;
      }
    break;

    case YIELDLAB:
      yieldNom = getChild(e,0)->u.str;
      yieldExpr = getChild(e,1);

      bool nomExiste = checkIdBlocExisteParNom(yieldNom);

      if(!nomExiste)
      {
        sprintf(message,"Dans l'expression YIELD nom:expr, bloc nomme: %s n'existe pas", yieldNom);
        pushErreur(message,courant,methode,listeDecl);
        resultat = FALSE;
        return resultat;
      }

      checkE1 = checkUneExprDansBloc(yieldExpr, e, courant, methode, listeDecl, rangBloc);
      if(checkE1)
      {
        ClassP type = getType(yieldExpr,e,courant,methode,listeDecl);
        ClassP typeBloc = getTypeIdBloc(yieldNom);
        if(!equalsType(type, typeBloc))
        {
          sprintf(message,"Dans l'expression YIELD nom:expr, bloc nomme: %s doit renvoyer une valuer de type %s, mais ici expr renvoie une valeur de type %s", yieldNom, typeBloc->name, type->name);
          pushErreur(message,courant,methode,listeDecl);
          resultat = FALSE;
        }
      }
      else
      {
        sprintf(message,"Dans l'expression YIELD nom:expr, expr est mal formee");
        pushErreur(message,courant,methode,listeDecl);
        resultat = FALSE;
      }
      return resultat;
    break;

    case YIELDANO:
      resultat = TRUE;
    break;

    case LISTARG:
      resultat = TRUE;
    break;

    default:
      printf("L'etiquette %d n'a pas ete gerer(checkUneExprDansBloc)\n", e->op);
  }

  resultat = TRUE;
  return resultat;
}

/*----------------------------partie generation du code-----------------------------------------------------*/

void generationCode(TreeP racine, ClassP listeClass,char *filePath)
{
  int fp;
  if(filePath == NULL)
    filePath="code.txt";
  if ( (fp = open(filePath, O_RDWR | O_CREAT | O_TRUNC ,0666)) == -1)
  {
    printf("Error opening file.\n");
    exit(1);
  }

    listeClassEnv=creerEnvClass(listClass);

    EnvClassP tempClass = listeClassEnv;
    while(tempClass!=NULL)
    {
        printf("-----------------------------------\n");
        printf("name %s ,positionGP %d ,nbChamp %d\n",tempClass->name,tempClass->positionGP,tempClass->nbChamp);
        EtiquetteP tempEtiquette=tempClass->p_etiquette;
        while(tempEtiquette!= NULL)
        {   
            char *ch1,*ch2;
            if(tempEtiquette->flag==1)
            {
                ch1="Integer";
                ch2="";
            }
            if(tempEtiquette->flag==2)
            {
                ch1="String";
                ch2="";
            }
            if(tempEtiquette->flag==4)
            {
                ch1="Objet";
                ch2="";
            }
            if(tempEtiquette->flag==8)
            {
                ch1="Fonction";
                ch2=tempEtiquette->typeCID;
            }

            printf("%s ,%d ,%s, %s\n",tempEtiquette->name,tempEtiquette->position,ch1,ch2);
            tempEtiquette=tempEtiquette->next;
        }
        tempClass=tempClass->next;
        printf("-----------------------------------\n");
    }

    EnvClassP listeVarEnv=NULL;

  /*int i=getClassIndiceGP("DefaultPoint", listEnvClass);
  printf("GP position : %d\n",i);
  EnvClassP env_class=getEnvClass("DefaultPoint", listEnvClass);
  int champIndice=getChampIndice("estGris", env_class);
  printf("champ position : %d\n",champIndice);*/
    
    

    init_generation(fp, listeClass);

    write(fp,"main: START",strlen("main: START"));
    write(fp,"\n",strlen("\n"));
    printf("--------------main---------------\n");
  generation_bloc(fp,racine->u.children[2],"main", FALSE,listeVarEnv);

  write(fp,"STOP",strlen("STOP"));
  write(fp,"\n",strlen("\n"));

  close(fp);
}

void init_generation(int fp,ClassP classListe)
{

    write(fp,"JUMP init",strlen("JUMP init"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));

    generation_addint(fp);
  generation_subint(fp);
  generation_mulint(fp);
  generation_divint(fp);
  generation_concat(fp);

/*-----------------------------------------------*/
    write(fp,"Integer_printInt: NOP",strlen("Integer_printInt: NOP"));
    write(fp,"\n",strlen("\n"));

    write(fp,"PUSHS \"Int:\"",strlen("PUSHS \"Int:\""));
    write(fp,"\n",strlen("\n"));

    write(fp,"WRITES",strlen("WRITES"));
    write(fp,"\n",strlen("\n"));

    write(fp,"LOAD 0",strlen("LOAD 0"));
    write(fp,"\n",strlen("\n"));

    write(fp,"WRITEI",strlen("WRITEI"));
    write(fp,"\n",strlen("\n"));

    write(fp,"PUSHS \"\\n\"",strlen("PUSHS \"\\n\""));
    write(fp,"\n",strlen("\n"));

    write(fp,"WRITES",strlen("WRITES"));
    write(fp,"\n",strlen("\n"));

    write(fp,"RETURN",strlen("RETURN"));
    write(fp,"\n",strlen("\n"));
    write(fp,"\n",strlen("\n"));

/*-----------------------------------------------*/
    write(fp,"String_println: NOP",strlen("String_println: NOP"));
    write(fp,"\n",strlen("\n"));

    write(fp,"LOAD 0",strlen("LOAD 0"));
    write(fp,"\n",strlen("\n"));

    write(fp,"WRITES",strlen("WRITES"));
    write(fp,"\n",strlen("\n"));

    write(fp,"PUSHS \"\\n\"",strlen("PUSHS \"\\n\""));
    write(fp,"\n",strlen("\n"));

    write(fp,"WRITES",strlen("WRITES"));
    write(fp,"\n",strlen("\n"));

    write(fp,"RETURN",strlen("RETURN"));
    write(fp,"\n",strlen("\n"));
    write(fp,"\n",strlen("\n"));

/*-----------------------------------------------*/
    write(fp,"String_print: NOP",strlen("String_print: NOP"));
    write(fp,"\n",strlen("\n"));

    write(fp,"LOAD 0",strlen("LOAD 0"));
    write(fp,"\n",strlen("\n"));

    write(fp,"WRITES",strlen("WRITES"));
    write(fp,"\n",strlen("\n"));

    write(fp,"RETURN",strlen("RETURN"));
    write(fp,"\n",strlen("\n"));
    write(fp,"\n",strlen("\n"));
/*-----------------------------------------------*/



    generation_lesFonction(fp, classListe);
  generation_classList(fp, classListe);
}

void generation_lesFonction(int fp, ClassP p_listClass)
{

    ClassP tempClass=p_listClass;
    while(tempClass != NULL)
    {
        MethodeP methodel=tempClass->methodeL;
        generation_fonctionListe(fp, tempClass->name, methodel);
    tempClass=tempClass->next;
    }
}

void generation_classList(int fp, ClassP p_listClass)
{
    write(fp,"init: NOP",strlen("init: NOP"));
  write(fp,"\n",strlen("\n"));

    ClassP tempClass=p_listClass;
    while(tempClass != NULL)
    {
        generation_class(fp, tempClass);
        tempClass=tempClass->next;
    }

    write(fp,"\n",strlen("\n"));
    write(fp,"JUMP main\n",strlen("JUMP main\n"));
  write(fp,"\n",strlen("\n"));
}

void generation_fonctionListe(int fp, char *className, MethodeP p_methode)
{

    MethodeP tempMethode=p_methode;
    while(tempMethode != NULL)
    {
        if(strcmp(className,"String")!=0 && strcmp(className,"Integer")!=0)
            generation_fonction(fp, className, tempMethode);
        tempMethode=tempMethode->next;
    }
}

void generation_fonction(int fp, char *className, MethodeP p_methode)
{

    if(p_methode==NULL)
    {
        return;
    }

    char etiquette[64];
    sprintf(etiquette,"%s_%s: NOP",className, p_methode->name);
    write(fp,etiquette,strlen(etiquette));
  write(fp,"\n",strlen("\n"));

  /*generation_bloc(fp, p_methode->corps,  p_methode->name, TRUE,NULL);*/
    write(fp,"--- methode crops",strlen("--- methode crops"));
    write(fp,"\n",strlen("\n"));


  write(fp,"RETURN",strlen("RETURN"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));
}

void generation_bloc(int fp, TreeP tree, char *fonctionName, bool flag,EnvClassP listeVarEnv)
{
    
    if(tree == NULL)
        return;

    if(tree->op != BLOCANO && tree->op != BLOCLAB)
    {
        printf("error in generation_bloc\n");
        exit(0);
    }


    int nbVariableCourant=0;

    /*char *blocID=NULL;
    if(tree->op == BLOCANO)
    {
        generation_Inst(fp,tree->u.children[2],listEnvClass,listVar,&nbVariableCourant);
        blocTete=pushEtiquetteBlocAnonym(blocTete);
        blocID=(char*)malloc(64);
        sprintf(blocID,"bloc_%d",nbEtiquette);
        nbEtiquette++;
    }
    else
    {
        generation_Inst(fp,tree->u.children[2],listEnvClass,listVar,&nbVariableCourant);
        char *blocID=tree->u.children[0]->u.str;
        blocTete=pushEtiquetteBlocLabel(blocTete,blocID);
    }

    char ch1[64];
    if(flag == TRUE)
        sprintf(ch1,"%s_%s:NOP    --fin",fonctionName,blocID);
    else
    
        sprintf(ch1,"main:NOP    --fin");
    write(fp,ch1,strlen(ch1));
    */
    listeVarEnv=generation_Inst(fp, tree->u.children[2], &nbVariableCourant,listeVarEnv);
    write(fp,"--this is crops",strlen("--this is crops"));
  write(fp,"\n",strlen("\n"));

    char ch2[64];
    sprintf(ch2,"POPN %d",nbVariableCourant);
    write(fp,ch2,strlen(ch2));
    write(fp,"\n",strlen("\n"));
}


EnvClassP generation_Inst(int fp, TreeP tree, int *nbVar,EnvClassP listeVarEnv)
{
    if(tree== NULL)
        return listeVarEnv;

    printf("%d\n",tree->op);

    if(tree->op==LIST)
    {
        listeVarEnv=generation_Inst(fp,tree->u.children[0],nbVar,listeVarEnv);
        listeVarEnv=generation_Inst(fp,tree->u.children[1],nbVar,listeVarEnv);
    }

    else if(tree->op == LOCVAR)
    {
        char *idName=tree->u.children[0]->u.lvar->name;
        char *CIDName=tree->u.children[0]->u.lvar->type->name;
        listeVarEnv=pushVar(fp,listeVarEnv,listeClassEnv,idName,CIDName);
        *nbVar=(*nbVar)+1;

        if(tree->u.children[1] != NULL)
        {
            int indice=getClassIndiceGP(idName,listeVarEnv);

            char ch[64];
            sprintf(ch,"PUSHG %d",indice);
            write(fp,ch,strlen(ch));
            write(fp,"\n",strlen("\n"));

            generation_expr(fp,tree->u.children[1]->u.children[1],listeVarEnv );

            if(strcmp(CIDName,"Integer")==0 || strcmp(CIDName,"String")==0)
            {
                write(fp,"STORE 0",strlen("STORE 0"));
                write(fp,"\n",strlen("\n"));
            }
            write(fp,"\n",strlen("\n"));
        }

        /*EnvClassP temp=listeVarEnv;
        while(temp!=NULL)
        {
            printf("Name :%s\n",temp->name);    
            printf("Position :%d\n",temp->positionGP);
            temp=temp->next;
        }*/
    }
    else    /*---exprs---*/
    {
        generation_expr(fp, tree,listeVarEnv);
    }
    return listeVarEnv;
}

void generation_expr(int fp, TreeP tree,EnvClassP listeVarEnv)
{   
    /*printf("%d\n",tree->op);*/

    switch(tree->op)
        {
            case ADD:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"ADD",strlen("ADD"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"Resultat:\"",strlen("PUSHS \"Resultat:\""));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITEI",strlen("WRITEI"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                break;

            }
            case MINUS:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"SUB",strlen("SUB"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"Resultat:\"",strlen("PUSHS \"Resultat:\""));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITEI",strlen("WRITEI"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                break;
            }
            case MUL:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"MUL",strlen("MUL"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"Resultat:\"",strlen("PUSHS \"Resultat:\""));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITEI",strlen("WRITEI"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                break;
            }
            case DIV:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"DIV",strlen("DIV"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"Resultat:\"",strlen("PUSHS \"Resultat:\""));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITEI",strlen("WRITEI"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                break;
            }
            case UPLUS:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                break;
            }
            case UMINUS:
            {
                write(fp,"PUSHN 1",strlen("PUSHN 1"));
                write(fp,"\n",strlen("\n"));

                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"SUB",strlen("SUB"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"Resultat:\"",strlen("PUSHS \"Resultat:\""));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITEI",strlen("WRITEI"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case AND:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                
                write(fp,"LOAD 0",strlen("LOAD 0"));
                write(fp,"\n",strlen("\n"));

                generation_expr(fp,tree->u.children[1],listeVarEnv);
                
                write(fp,"LOAD 0",strlen("LOAD 0"));
                write(fp,"\n",strlen("\n"));

                write(fp,"CONCAT",strlen("CONCAT"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"Resultat:\"",strlen("PUSHS \"Resultat:\""));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));

                write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                write(fp,"\n",strlen("\n"));

                write(fp,"WRITES",strlen("WRITES"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case NE:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"NOT",strlen("NOT"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case EQ:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"EQUAL",strlen("EQUAL"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case LT:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"INF",strlen("INF"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case LE:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"INFEQ",strlen("INFEQ"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case GT:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"SUP",strlen("SUP"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case GE:
            {
                generation_expr(fp,tree->u.children[0],listeVarEnv);
                if(tree->u.children[0]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                generation_expr(fp,tree->u.children[1],listeVarEnv);
                if(tree->u.children[1]->op != Cste)
                {
                    write(fp,"LOAD 0",strlen("LOAD 0"));
                    write(fp,"\n",strlen("\n"));
                    write(fp,"\n",strlen("\n"));
                }
                write(fp,"SUPEQ",strlen("SUPEQ"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case ITE:   
            {
                char label_else[64];
                sprintf(label_else,"else_%d",nbITELabelIndice);
                char end_ITE[64];
                sprintf(end_ITE,"end_ITE_%d",nbITELabelIndice);
                nbITELabelIndice++;

                generation_expr(fp,tree->u.children[0],listeVarEnv);

                char inst_JZ[64];
                sprintf(inst_JZ,"JZ %s",label_else);
                write(fp,inst_JZ,strlen(inst_JZ));
                write(fp,"\n",strlen("\n"));

                generation_expr(fp,tree->u.children[1],listeVarEnv);

                char inst_JUMP[64];
                sprintf(inst_JUMP,"JUMP %s",end_ITE);
                write(fp,inst_JUMP,strlen(inst_JUMP));
                write(fp,"\n",strlen("\n"));

                char else_NOP[64];
                sprintf(else_NOP,"%s:NOP",label_else);
                write(fp,else_NOP,strlen(else_NOP));
                write(fp,"\n",strlen("\n"));
                if(tree->u.children[2] != NULL)
                {
                    generation_expr(fp,tree->u.children[2],listeVarEnv);
                }

                char end_NOP[64];
                sprintf(end_NOP,"%s:NOP",end_ITE);
                write(fp,end_NOP,strlen(end_NOP));
                write(fp,"\n",strlen("\n"));

                break;
            }
            case WHILEDO:
            {
                char whileLabel[64];
                sprintf(whileLabel,"while_%d:NOP",nbWhileLabelIndice);
                char inst_JUMP[64];
                sprintf(inst_JUMP,"JUMP while_%d",nbWhileLabelIndice);
                char end_while_Label[64];
                sprintf(end_while_Label,"end_while_%d",nbWhileLabelIndice);
                nbWhileLabelIndice++;

                write(fp,whileLabel,strlen(whileLabel));
                write(fp,"\n",strlen("\n"));

                generation_expr(fp,tree->u.children[0],listeVarEnv);

                char inst_JZ[64];
                sprintf(inst_JZ,"JZ %s",end_while_Label);
                write(fp,inst_JZ,strlen(inst_JZ));
                write(fp,"\n",strlen("\n"));

                generation_expr(fp,tree->u.children[1],listeVarEnv);

                write(fp,inst_JUMP,strlen(inst_JUMP));
                write(fp,"\n",strlen("\n"));

                char fini[128];
                sprintf(fini,"%s:NOP",end_while_Label);
                write(fp,fini,strlen(fini));
                write(fp,"\n",strlen("\n"));

                break;
            }
            case AFF:
            {

                if(tree->u.children[0]->op == ID)
                {
                    char *idName=tree->u.children[0]->u.str;
                    printf("IDname: %s\n",idName);
                    char *idType=getEnvClass(idName, listeVarEnv)->CIDName;
                    printf("idType: %s\n",idType);
                    generation_expr(fp,tree->u.children[0],listeVarEnv);
                    generation_expr(fp,tree->u.children[1],listeVarEnv);

                    if(strcmp(idType,"Integer")==0 || strcmp(idType,"String")==0 )
                    {
                        write(fp,"STORE 0",strlen("STORE 0"));
                        write(fp,"\n",strlen("\n"));
                    }
                    else
                    {
                        write(fp,"STOREL -1",strlen("STOREL -1"));
                        write(fp,"\n",strlen("\n"));
                    }
                }
                else/*selection*/
                {
                    generation_expr(fp,tree->u.children[0],listeVarEnv);

                }
                break;
            }
            case YIELDLAB:
            {
                break;
            }
            case YIELDANO:
            {
                break;
            }
            case STR:
            {
                char *str=tree->u.str;
                printf("%s\n",str);
                char ch[64];
                sprintf(ch,"PUSHS %s",str);
                write(fp,ch,strlen(ch));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case Cste:
            {
                char val_str[64];
                int val=tree->u.val;
                sprintf(val_str,"PUSHI %d",val);
                write(fp,val_str,strlen(val_str));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case ID:
            {
                if(strcmp(tree->u.str,"void")==0)
                {
                    break;
                }

                int indiceGP=getClassIndiceGP(tree->u.str,listeVarEnv);
                char ch[64];
                sprintf(ch,"PUSHG %d",indiceGP);
                write(fp,ch,strlen(ch));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case ENVOI:
            {
                if(tree->u.children[0]->op == ID)
                {
                    char *idName=tree->u.children[0]->u.str;
                    int indice=getClassIndiceGP(idName,listeVarEnv);
                    EnvClassP obj=getEnvClass(idName,listeVarEnv);
                    char *CIDName=obj->CIDName;

                    char ch[64];
                    sprintf(ch,"PUSHG %d",indice);
                    write(fp,ch,strlen(ch));
                    write(fp,"\n",strlen("\n"));
                    write(fp,ch,strlen(ch));
                    write(fp,"\n",strlen("\n"));

                    EnvClassP classModele=getEnvClass(CIDName,listeClassEnv);
                    char *foncID=tree->u.children[1]->u.str;
                    char etiquetteFonction[128];
                    sprintf(etiquetteFonction,"%s_%s",CIDName,foncID);
                    int positionFonc=getChampIndice(etiquetteFonction,classModele);

                    char ch2[64];
                    sprintf(ch2,"LOAD %d",positionFonc);
                    write(fp,ch2,strlen(ch2));
                    write(fp,"\n",strlen("\n"));

                    write(fp,"CALL",strlen("CALL"));
                    write(fp,"\n",strlen("\n"));

                }
                if(tree->u.children[0]->op == SELECT)
                {

                }
                if(tree->u.children[0]->op == Cste)
                {

                }
                if(tree->u.children[0]->op == STR)
                {
                    char *string=tree->u.children[0]->u.str;
                    char *foncID=tree->u.children[1]->u.str;
                    
                    if(strcmp(foncID,"print")==0)
                    {
                        char ch[128];
                        sprintf(ch,"PUSHS %s",string);
                        write(fp,ch,strlen(ch));
                        write(fp,"\n",strlen("\n"));

                        write(fp,"WRITES",strlen("WRITES"));
                        write(fp,"\n",strlen("\n"));
                    }
                    if(strcmp(foncID,"println")==0)
                    {
                        char ch[128];
                        sprintf(ch,"PUSHS %s",string);
                        write(fp,ch,strlen(ch));
                        write(fp,"\n",strlen("\n"));

                        write(fp,"WRITES",strlen("WRITES"));
                        write(fp,"\n",strlen("\n"));

                        write(fp,"PUSHS \"\\n\" ",strlen("PUSHS \"\n\" "));
                        write(fp,"\n",strlen("\n"));

                        write(fp,"WRITES",strlen("WRITES"));
                        write(fp,"\n",strlen("\n"));
                    }
                    
                }
                break;
            }
            case CENVOI:
            {
                write(fp,"--this is Cenvoi",strlen("--this is Cenvoi"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case SELECT:
            {
                write(fp,"--this is select",strlen("--this is select"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            case CSELECT:
            {
                write(fp,"--this is Cselect",strlen("--this is Cselect"));
                write(fp,"\n",strlen("\n"));
                break;
            }
            default:
            {
                break;
            }




        }
}


int getNbFonction(ClassP p_cls)
{
    if(p_cls==NULL)
        return 0;

    int res=0;
    MethodeP tempMethode=p_cls->methodeL;
    while(tempMethode != NULL)
    {
        res++;
    tempMethode=tempMethode->next;
    }

    if(p_cls ->isExtend ==TRUE)
    {
        res+=getNbFonction(p_cls ->classMere);
    }

    return res;
}

void generation_class(int fp,ClassP p_class)
{

    char *className=p_class->name;
    int nbMethode=getNbFonction(p_class);

    char tete[64];
    sprintf(tete,"--------%s",className);
    write(fp,tete,strlen(tete));
  write(fp,"\n",strlen("\n"));

    char ALLOC_nb[32];
    sprintf(ALLOC_nb,"ALLOC %d",nbMethode);
    write(fp,ALLOC_nb,strlen(ALLOC_nb));
  write(fp,"\n",strlen("\n"));

  int tempIndice=0;
  ClassP tempClass=p_class;
  char *tempClassName=p_class->name;
  MethodeP tempMethode=p_class->methodeL;
  while(tempIndice<nbMethode)
  {
        if(tempMethode == NULL)
        {
            tempClass=tempClass->classMere;
            tempClassName=tempClass->name;
            tempMethode=tempClass->methodeL;
        }

        write(fp,"DUPN 1",strlen("DUPN 1"));
        write(fp,"\n",strlen("\n"));

        char PUSHA_nameFonc[48];
        sprintf(PUSHA_nameFonc,"PUSHA %s_%s",tempClassName,tempMethode->name);
        write(fp,PUSHA_nameFonc,strlen(PUSHA_nameFonc));
        write(fp,"\n",strlen("\n"));

        char STORE_Nb[16];
        sprintf(STORE_Nb,"STORE %d",tempIndice);
        write(fp,STORE_Nb,strlen(STORE_Nb));
        write(fp,"\n",strlen("\n"));

        tempIndice++;
    tempMethode=tempMethode->next;
  }
  write(fp,"\n",strlen("\n"));
}



void generation_addint(int fp)
{
  write(fp,"addint: NOP",strlen("addint: NOP"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -2",strlen("PUSHL -2"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -1",strlen("PUSHL -1"));
  write(fp,"\n",strlen("\n"));

  write(fp,"ADD",strlen("SUB"));
  write(fp,"\n",strlen("\n"));

  write(fp,"STOREL -3",strlen("STOREL -3"));
  write(fp,"\n",strlen("\n"));

  write(fp,"RETURN",strlen("RETURN"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));

}

void generation_subint(int fp)
{
  write(fp,"subint: NOP",strlen("subint: NOP"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -2",strlen("PUSHL -2"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -1",strlen("PUSHL -1"));
  write(fp,"\n",strlen("\n"));

  write(fp,"SUB",strlen("SUB"));
  write(fp,"\n",strlen("\n"));

  write(fp,"STOREL -3",strlen("STOREL -3"));
  write(fp,"\n",strlen("\n"));

  write(fp,"RETURN",strlen("RETURN"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));
}

void generation_mulint(int fp)
{
  write(fp,"mulint: NOP",strlen("mulint: NOP"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -2",strlen("PUSHL -2"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -1",strlen("PUSHL -1"));
  write(fp,"\n",strlen("\n"));

  write(fp,"MUL",strlen("SUB"));
  write(fp,"\n",strlen("\n"));

  write(fp,"STOREL -3",strlen("STOREL -3"));
  write(fp,"\n",strlen("\n"));

  write(fp,"RETURN",strlen("RETURN"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));
}

void generation_divint(int fp)
{
  write(fp,"divint: NOP",strlen("divint: NOP"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -2",strlen("PUSHL -2"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -1",strlen("PUSHL -1"));
  write(fp,"\n",strlen("\n"));

  write(fp,"DIV",strlen("SUB"));
  write(fp,"\n",strlen("\n"));

  write(fp,"STOREL -3",strlen("STOREL -3"));
  write(fp,"\n",strlen("\n"));

  write(fp,"RETURN",strlen("RETURN"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));
}

void generation_concat(int fp)
{
  write(fp,"concat: NOP",strlen("concat: NOP"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -2",strlen("PUSHL -2"));
  write(fp,"\n",strlen("\n"));

  write(fp,"PUSHL -1",strlen("PUSHL -1"));
  write(fp,"\n",strlen("\n"));

  write(fp,"CONCAT",strlen("CONCAT"));
  write(fp,"\n",strlen("\n"));

  write(fp,"STOREL -3",strlen("STOREL -3"));
  write(fp,"\n",strlen("\n"));

  write(fp,"RETURN",strlen("RETURN"));
  write(fp,"\n",strlen("\n"));
  write(fp,"\n",strlen("\n"));
}
/*----------------------fin init.c------------*/








/*-------------------class_envir.c--------------------*/

EnvClassP creerEnvClass(ClassP listeClass)
{

    int indiceGP=0;

    ClassP tempClass=listeClass;
    EnvClassP tempEnvClass=NULL;
    EnvClassP tete=NULL;

    while(tempClass !=NULL)
    {
        if(indiceGP == 0)
        {
            tete=NEW(1,EnvClass);
            tempEnvClass=tete;
            tempEnvClass->next=NULL;
            tempEnvClass->p_etiquette=NULL;
      tempEnvClass->nbChamp=0;
      tempEnvClass->positionGP=indiceGP;
        }
        else
        {
            tempEnvClass->next=NEW(1,EnvClass);
            tempEnvClass=tempEnvClass->next;
            tempEnvClass->next=NULL;
            tempEnvClass->p_etiquette=NULL;
      tempEnvClass->nbChamp=0;
      tempEnvClass->positionGP=indiceGP;
        }

        tempEnvClass->name=tempClass->name;
        tempEnvClass->CIDName=tempClass->name;
        tempEnvClass->flag=ENV_CLASS;
        tempEnvClass->positionGP=indiceGP;

        creerEtiquetteL(tempClass,tempEnvClass);

    indiceGP++;
        tempClass=tempClass->next;
    }
    nbFpVariable=indiceGP;

    return tete;
}

void creerEtiquetteL(ClassP p_class,EnvClassP p_envClass)
{

  creerEtiquetteVarL(p_class, p_envClass, &(p_envClass->nbChamp));
    creerEtiquetteMethodeL(p_class, p_envClass, &(p_envClass->nbChamp));


}

EtiquetteP creerEtiquetteVarL(ClassP p_class, EnvClassP p_envClass,int *nbChamp)
{

    VarDeclP tempLvar=p_class->lvar;

    EtiquetteP tempEtiquette=p_envClass->p_etiquette;
  while(tempEtiquette != NULL)
  { 
    if(tempEtiquette->next == NULL)
    {
      break;
    }
    else
    {
      tempEtiquette=tempEtiquette->next;
    }
  }


    while(tempLvar != NULL)
    {

        if(*nbChamp == 0)
        {
            p_envClass->p_etiquette=NEW(1,Etiquette);
            tempEtiquette=p_envClass->p_etiquette;
            tempEtiquette->next=NULL;
        }
        else
        {
            tempEtiquette->next=NEW(1,Etiquette);
            tempEtiquette=tempEtiquette->next;
            tempEtiquette->next=NULL;
        }

        if(tempLvar->type == NULL)
        {
            if(tempLvar->intStrObjet == 2)
                tempEtiquette->typeCID="Integer";
            if(tempLvar->intStrObjet == 1)
                tempEtiquette->typeCID="String";
        }
        else
            tempEtiquette->typeCID=tempLvar->type->name;

        tempEtiquette->position=*nbChamp;
        tempEtiquette->name=tempLvar->name;
        if(tempLvar->intStrObjet == 2)        /* int */
            tempEtiquette->flag=FLAG_INT;
        else if(tempLvar->intStrObjet == 1)   /* str */
            tempEtiquette->flag=FLAG_STR;
        else if(tempLvar->intStrObjet == 3)   /* obj */
            tempEtiquette->flag=FLAG_OBJ;
        else
        {
            printf("Error in creerEtiquetteVarL()\n");
            exit(0);
        }
        *nbChamp=(*nbChamp)+1;
    tempLvar=tempLvar->next;
    }

    if(p_class->isExtend == TRUE)
    {
        EtiquetteP finEtiquette=creerEtiquetteVarL(p_class->classMere, p_envClass,  nbChamp);    
        return finEtiquette;
    }
    else
        return tempEtiquette;
}


EtiquetteP creerEtiquetteMethodeL(ClassP p_class, EnvClassP p_envClass, int *nbChamp)
{

  printf("%s \n",p_class->name);
    MethodeP p_methode=p_class->methodeL;

  EtiquetteP tempEtiquette= p_envClass->p_etiquette;
  while(tempEtiquette != NULL)
  { 
    if(tempEtiquette->next == NULL)
    {
      break;
    }
    else
    {
      tempEtiquette=tempEtiquette->next;
    }
  }
  
    while(p_methode != NULL)
    {
        if(*nbChamp == 0)
        {
            p_envClass->p_etiquette=NEW(1,Etiquette);
            tempEtiquette=p_envClass->p_etiquette;
            tempEtiquette->next=NULL;
        }
        else
        {     
            tempEtiquette->next=NEW(1,Etiquette);
            tempEtiquette=tempEtiquette->next;
            tempEtiquette->next=NULL;
        }


        char *etiquetteName=(char*)malloc(128);
        sprintf(etiquetteName,"%s_%s",p_class->name,p_methode->name);
        tempEtiquette->typeCID=p_methode->typeRetour->name;
        tempEtiquette->position=*nbChamp;
        tempEtiquette->name=etiquetteName;
        tempEtiquette->flag=FLAG_FONC;
    
        *nbChamp=(*nbChamp)+1;
    p_methode=p_methode->next;
    }

    if(p_class->isExtend == TRUE)
    {
        EtiquetteP finEtiquette=creerEtiquetteVarL(p_class->classMere, p_envClass, nbChamp);
        return finEtiquette;
    }
    else
        return tempEtiquette;
}

EnvClassP getEnvClass(char *nom, EnvClassP tete)
{

    if(tete == NULL)
        return NULL;

    EnvClassP tempEnv=tete;
    while(tempEnv != NULL)
    {
        if(strcmp(nom, tempEnv->name) == 0)
            return tempEnv;

    tempEnv=tempEnv->next;
    }
    return NULL;
}

int getClassIndiceGP(char *nom, EnvClassP tete)
{

    EnvClassP resClass=getEnvClass(nom, tete);
    if(resClass == NULL)
        return -1;

    else
        return resClass->positionGP;
}

int getChampIndice(char *name, EnvClassP p_envClass)
{
  if(p_envClass ==NULL)
  {
    printf("error in getChampIndice. EnvClassP vide");
    exit(0);
  }

  int res=0;
  EtiquetteP temp=p_envClass->p_etiquette;
  while(temp !=NULL)
  {
    if(strcmp(name,temp->name)==0)
    {
      return res;
    }

    res++;
    temp=temp->next;
  }
  return -1;
}




/*--------------------------- fin-----------------------------*/



BlocP pushEtiquetteBlocLabel(BlocP tete, char *nom)
{

    if(tete ==NULL)
    {
        BlocP temp=NULL;
        temp=NEW(1,Bloc);
        temp->nom=nom;
        temp->indice=nbEtiquette;
        nbEtiquette++;
        temp->next=NULL;
        return temp;
    }

    BlocP temp=tete;


    temp=NEW(1,Bloc);
    temp->nom=nom;
    temp->indice=nbEtiquette;
    nbEtiquette++;
    temp->next=tete;

    return tete;
}

BlocP pushEtiquetteBlocAnonym(BlocP tete)
{
    char ch[64];
    sprintf(ch,"bloc_%d",nbEtiquette);

    if(tete ==NULL)
    {
        BlocP temp=NULL;
        temp=NEW(1,Bloc);
        temp->nom=ch;
        temp->indice=nbEtiquette;
        nbEtiquette++;
        temp->next=NULL;
        return temp;
    }

    BlocP temp=tete;

    temp=NEW(1,Bloc);
    temp->nom=ch;
    temp->indice=nbEtiquette;
    nbEtiquette++;
    temp->next=tete;

    return tete;
}


int getBlocIndice(BlocP tete, char *nom)
{
    if(tete ==NULL)
        return -1;

    BlocP temp=tete;
    while(temp!=NULL)
    {
        if(strcmp(temp->nom,nom)==0)
        {
            return temp->indice;
        }
        temp=temp->next;
    }

    return -1;
}

BlocP pushBlocIndice(BlocP tete)
{
    if(tete ==NULL)
        return NULL;

    BlocP temp=tete->next;
    free(tete);
    

    return temp;
}


/* initialiser un objet */
EnvClassP pushVar(int fp,EnvClassP envir, EnvClassP tete, char *nom, char *typeCID)
{
    EnvClassP classGP=getEnvClass(typeCID, tete);
    if(classGP == NULL)
    {
        printf("class not found\n");
        exit(0);
    }

    EnvClassP temp=NULL;

    temp=NEW(1,EnvClass);
    temp->name=nom;
    temp->flag=ENV_OBJ;
    temp->positionGP=nbFpVariable;
    temp->next=envir;
    temp->CIDName=classGP->name;
    nbFpVariable++;

    int nbChamp=classGP->nbChamp;
    char ch[128];
    sprintf(ch,"ALLOC %d ------%s",nbChamp,nom);
    write(fp,ch,strlen(ch));
    write(fp,"\n",strlen("\n"));


    EtiquetteP p_etiquette=classGP->p_etiquette;
    if(p_etiquette->flag==FLAG_INT)
    {

        write(fp,"DUPN 1",strlen("DUPN 1"));
        write(fp,"\n",strlen("\n"));

        write(fp,"PUSHI 0",strlen("PUSHI 0"));
        write(fp,"\n",strlen("\n"));

        write(fp,"STORE 0",strlen("STORE 0"));
        write(fp,"\n",strlen("\n"));

        write(fp,"DUPN 1",strlen("DUPN 1"));
        write(fp,"\n",strlen("\n"));

        write(fp,"PUSHA Integer_printInt",strlen("PUSHA Integer_printInt"));
        write(fp,"\n",strlen("\n"));

        write(fp,"STORE 1",strlen("STORE 1"));
        write(fp,"\n",strlen("\n"));

    }
    else if(p_etiquette->flag==FLAG_STR)
    {
        write(fp,"DUPN 1",strlen("DUPN 1"));
        write(fp,"\n",strlen("\n"));

        write(fp,"PUSHS \"\"",strlen("PUSHS \"\""));
        write(fp,"\n",strlen("\n"));

        write(fp,"STORE 0",strlen("STORE 0"));
        write(fp,"\n",strlen("\n"));

        write(fp,"DUPN 1",strlen("DUPN 1"));
        write(fp,"\n",strlen("\n"));

        write(fp,"PUSHA String_println",strlen("PUSHA String_println"));
        write(fp,"\n",strlen("\n"));

        write(fp,"STORE 1",strlen("STORE 1"));
        write(fp,"\n",strlen("\n"));

        write(fp,"DUPN 1",strlen("DUPN 1"));
        write(fp,"\n",strlen("\n"));

        write(fp,"PUSHA String_print",strlen("PUSHA String_print"));
        write(fp,"\n",strlen("\n"));

        write(fp,"STORE 2",strlen("STORE 2"));
        write(fp,"\n",strlen("\n"));
    }
    else{
        int i=0;
        while(p_etiquette!=NULL)
        {
            
            if(p_etiquette->flag==FLAG_FONC)
            {
                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                char *fonc_name=p_etiquette->name;
                char push_fonc[128];
                sprintf(push_fonc,"PUSHA %s",fonc_name);
                write(fp,push_fonc,strlen(push_fonc));
                write(fp,"\n",strlen("\n"));

                char ch[32];
                sprintf(ch,"STORE %d",i);
                write(fp,ch,strlen(ch));
                write(fp,"\n",strlen("\n"));
                i++;
            }
            if(p_etiquette->flag==FLAG_OBJ)
            {
                write(fp,"DUPN 1",strlen("DUPN 1"));
                write(fp,"\n",strlen("\n"));

                char ch[128];
                sprintf(ch,"%s_%s",nom,p_etiquette->name);
                temp=pushVar(fp, envir, tete, ch, p_etiquette->typeCID);
                nbFpVariable++;
            }
            char ch2[32];
            sprintf(ch,"STORE %d",i);
            write(fp,ch2,strlen(ch2));
            write(fp,"\n",strlen("\n"));
            i++;
            p_etiquette=p_etiquette->next;
        }
    }
    write(fp,"\n",strlen("\n"));
    return temp;
}



EnvClassP popVar(int fp,EnvClassP tete, int popNb)
{
    if(tete==NULL)
    {
        return NULL;
    }

    EnvClassP temp;
    EnvClassP res=tete;
    int i=popNb;
    while(i>0 && res!=NULL)
    {
        temp=res;
        res=res->next;
        free(temp);
    }

    char ch[64];
    sprintf(ch,"POPN %d",popNb);
    write(fp,ch,strlen(ch));
    write(fp,"\n",strlen("\n"));

    return res;
}