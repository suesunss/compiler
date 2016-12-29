#include <unistd.h>
#include <stdio.h>
#include "tp.h"
#include "tp_y.h"

extern TreeP racine;
extern ClassP classAnalysee;
extern void setError();
extern TreeP getChild(TreeP tree, int rank);
extern bool verbose;
extern bool noVC;

void pprint(TreeP tree);

int margin = 0; /* niveau d'indentation courant */

/* Impression:la partie declarative du programme */
void pprintVar(VarDeclP decl, TreeP tree) {
  if (! verbose) return;
  printf("%s := ", decl->name);
  pprint(tree);
  /* utile au cas ou l'evaluation se passerait mal ! */
  fflush(NULL);
}

/*void pprintValueVar(VarDeclP decl) {
  if (! verbose) return;
  if (! noVC) {
    printf(" [Valeur: %d]\n", decl->val);
  } else printf("\n");
}*/


void println(char *str) {
  int i;
  fprintf(stderr, "%s\n", str);
  for(i = 0; i < margin; i++) fprintf(stderr, "  ");
}


char * decompileOp(short op) {
  switch (op) {
  case '+':   return " + ";
  case '-':
  case UPLUS: return " + ";
  case UMINUS: return " - ";
  case '*':   return " * ";
  case '/':   return " / ";
  case EQ:    return " = ";
  case LT:    return " < ";
  case GT:    return " > ";
  case LE:    return " <= ";
  case GE:    return " >= ";
  case NE:    return " <> ";
  case '&':   return " & ";
  default:
    fprintf(stderr, "Internal error: undefined binary operator: %c", op);
    return "UNKNOWN";
  }
}

/* Affichage de la structure d'une expression */

/* Affichage d'une expression binaire */
void pprintTree2(TreeP tree, char *op) {
  fprintf(stderr, "(");
  pprint(getChild(tree, 0));
  fprintf(stderr, "%s", op);
  pprint(getChild(tree, 1));
  fprintf(stderr, ")");
}

/* Affichage d'une expression unaire */
void pprintTree1(TreeP tree, char *op) {
  fprintf(stderr, "(%s", op);
  pprint(getChild(tree, 0));
  fprintf(stderr, ")");
}

void pprintIf(TreeP tree) {
  fprintf(stderr, "if ");
  pprint(getChild(tree, 0));
  margin++;
  println(" then");
  pprint(getChild(tree, 1));
  margin--;
  println("");
  margin++;
  println("else");
  pprint(getChild(tree, 2));
  margin--;
}

/* Affichage recursif d'un arbre */
void pprint(TreeP tree) {
  char *s;
  if (tree == NIL(Tree)) return;
  switch (tree->op) {
  case ID: case STR:
    fprintf(stderr, "%s", tree->u.str); break;
  case Cste:
    fprintf(stderr, "%d", tree->u.val); break;
  case EQ: case NE: case GT: case GE: case LT: case LE:
  case '+': case '-': case '*': case '/': case '&':
    s = decompileOp(tree->op);
    pprintTree2(tree, s);
    break;
  case IF:
    pprintIf(tree); break;
  default:
    /* On signale le probleme mais on ne quitte pas le programme pour autant */
    fprintf(stderr, "Internal error: pprint unknown label: %d\n", tree->op);
  }
}

void pprintMain(TreeP tree) {
  if (! verbose) return;
  printf("Expression principale : ");
  pprint(tree);
  fflush(NULL);
}


/*====================================================================================*/
/** permet d'afficher un arbre à n fils **/
void pprintTreeMain(TreeP tree) {
    if(tree == NIL(Tree)){
        printf("ARBRE = NIL\n");
    }

    int nbChild = tree->nbChildren;
    int i;
    printf("(TreeP(nbChildren=%d et ", nbChild);
    switch (tree->op) {
        case NE:    printf("op=NE"); break;
        case EQ:    printf("op=EQ"); break;
        case LT:    printf("op=LT"); break;
        case LE:    printf("op=LE"); break;
        case GT:    printf("op=GT"); break;
        case GE:    printf("op=GE"); break;
        case UMINUS:    printf("op=UMINUS"); break;
        case UPLUS:    printf("op=UPLUS"); break;
        case STR:    printf("op=STR"); break;
        case LIST:    printf("op=LIST"); break;
        case SELECT:       printf("op=SELECT"); break;
        case ENVOI:     printf("op=ENVOI"); break;
        case CSELECT:   printf("op=CSELECT"); break;
        case CENVOI:      printf("op=CENVOI"); break;
        case LOCVAR:      printf("op=LOCVAR"); break;
        case BLOCANO:    printf("op=BLOCANO"); break;
        case BLOCLAB:     printf("op=BLOCLAB"); break;
        case YIELDANO:     printf("op=YIELDANO"); break;
        case YIELDLAB:     printf("op=YIELDLAB"); break;
        case WHILEDO:     printf("op=WHILEDO"); break;
        case ITE:    printf("op=ITE");  break;
        case ADD:     printf("op=ADD"); break;
        case MINUS:      printf("op=MINUS"); break;
        case MUL:    printf("op=MUL"); break;
        case DIV: printf("op=DIV"); break;
        case AND:     printf("op=AND"); break;
        case PARAM:     printf("op=PARAM"); break;
        case RACINE:   printf("op=RACINE"); break;
        case RACINE_CLASS:     printf("op=RACINE_CLASS"); break;
        default: break;
    }
    printf(")\n");
    if(tree->op==RELOP){
        printf("=============================================\n");
        /* printf("OPERATEUR = %d \n", tree->u.val);*/
        switch(tree->u.val){
                case EQ : printf("OPERATEUR : <>\n");break;
                case NE : printf("OPERATEUR : <>\n");break;
                case LT : printf("OPERATEUR : <\n");break;
                case LE : printf("OPERATEUR : <=\n");break;
                case GT : printf("OPERATEUR : >\n");break;
                case GE : printf("OPERATEUR : >=\n");break;
                }
        printf("=============================================\n");
    }
    else if(tree->op==ID || tree->op==CID || tree->op==STR){
        printf("=============================================\n");
        printf("---tree->u.str = %s\n", tree->u.str);
        printf("=============================================\n");
    }
    else if(tree->op==Cste){
        printf("=============================================\n");
        printf("---tree->u.val = %d\n", tree->u.val);
        printf("=============================================\n");
    }
    else if(tree->op==LOCVAR){ 
        printf("===================================================\n");
        printVar(tree->u.lvar);
        printf("===================================================\n");
    }
    /*else if(tree->op==RACINE_CLASS){ 
        printf("===================================================\n");
        printClasse(tree->u.classe);
        printf("===================================================\n");
    }
    else if(tree->op==LISTEMETHODE){
        printf("===================================================\n");
        printMethode(tree->u.methode);
        printf("===================================================\n");
    }*/
    else if(nbChild == 0){
        printf("------------------- Probleme?!\n");
    }
    else if(nbChild>0){
        for(i=0; i<nbChild; i++){
            printf("---child[%d]\n", i);
            if(tree->u.children[i] == NIL(Tree)){
                printf("--------> NIL\n");
            }
            else{
                pprintTreeMain(tree->u.children[i]);
            }
        }
    }
    else{
        printf("-----------------Probleme 2\n");
    }
}

void printClasse(ClassP classe){
    ClassP tmp=classe;
    if(tmp != NULL){
        printf("[debut de print class(type)]:\n");
        printf("classe:%s\n", tmp->name);
        if(tmp->params != NULL){
            printf("constructeur :\n");
            printVar(tmp->params);
        }
        /*
        if(tmp->corps_constructeur != NULL){
            printf("corps_constructeur : \n");
            pprintTreeMain(tmp->corps_constructeur);
        }
        */
        if(tmp->methodeL != NULL){
            printf("liste_methodes :\n");   
            printMethode(tmp->methodeL);
        }
        if(tmp->lvar != NULL){
            printf("liste_champs :\n");
            printVar(tmp->lvar);
        }
        if(tmp->classMere != NULL){
            printf("Classe mere = %s\n", tmp->classMere->name);
        }
        printf("isExtend=%d\n", tmp->isExtend);
        printf("isFinal=%d\n", tmp->isFinal);
        printf("[fin de print class]\n");
        printClasse(tmp->next);
    }
    else{
        printf("\n");
    }
}

void printMethode(MethodeP methode){
    MethodeP tmp=methode;
    if(tmp != NULL){
        printf("---------------\n");
        printf("--methode:%s\n", tmp->name);
        printf("----isStatic = %d\n----isFinal = %d\n----isRedef = %d\n", tmp->isStatic, tmp->isFinal, tmp->isRedef);
        
        printf("========  corpMethode ========= \n");
        printf("name = %s\n",tmp->name);
        if(tmp->corps != NULL){
            pprintTreeMain(tmp->corps);
        }
        printf("======== FIN corpMethode ========= \n");
        if(tmp->typeRetour != NULL){
            printf("typeRetour = %s\n", tmp->typeRetour->name);
            /* FONCTIONNE AUSSI : printClasse(tmp->typeRetour); */
        }
        if(tmp->lvar != NULL){
            printf("Liste de param :\n");
            printVar(tmp->lvar);
        }
        if(tmp->classApp != NULL){
            printf("Class d'appartenance = %s\n", tmp->classApp->name);
        }
        printf("---------------\n");
        printMethode(tmp->next);
    }
    else{
        printf("\n");
    }
}

void printVar(VarDeclP var){
    VarDeclP tmp=var;
    if(tmp != NULL){
        printf("-----------------------------------------------\n");
        printf("[var: %s]\n", tmp->name);
        if(tmp->type != NULL){
          printf("type = %s\n", tmp->type->name);
          printf("[debut de l'arbre type]:\n");
          printClasse(tmp->type);
          printf("[Fin de print type]\n");
        }
        printf("categorie(static ou non) = %d\n", tmp->categorie);

        printf("init = \n");

        if(!(tmp->init==NIL(Tree))){
        pprintTreeMain(tmp->init);
        }
        else{
            printf("NULL");
        }
        /*if(tmp->init != NULL){
            pprintTreeMain(tmp->init);
        }*/

        printf("_______________________\n");
        printVar(tmp->next);
    }
    else{
        printf("\n");
    }
}

void pprintBlock(TreeP tree) {
}


void pprintAff(TreeP tree) {
}

/* Affichage d'un new C(arg1, ... argN) */
void pprintNew(TreeP tree) {
}


/* Affichage d'une selection d'attribut */
void pprintACall(TreeP tree) {
}


/* Affichage d'un appel de methode */
void pprintMCall(TreeP tree) {
}

/* Imprime les informations sur une variable ou un champ */
void varPrint(VarDeclP var) {
}

/* Imprime les informations sur les classes et l'expression finale */
void prettyAll(TreeP mainExp) {
  if (! verbose) return;
}

