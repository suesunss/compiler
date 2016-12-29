#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "tp.h"
#include "tp_y.h"

#define PAS_FAIT 	1

int runVC(TreeP mainExp) {
  bool checkProg = checkProgramme(racine);
  return checkProg;
}


int genCode(TreeP mainExp) {
  return PAS_FAIT;
}

void prologue() {
	/* Ajout des classes predefinies : Integer, String et Void 
   * Ajout des methodes predefinies printInt (-> integer) et println & print (-> string)*/
  /* Creation des classes predefinies */
  ClassP Integer = makeClassePredefinie("Integer", NULL, NULL, NULL, NULL, NULL, 0, 0);
  ClassP String = makeClassePredefinie("String", NULL, NULL, NULL, NULL, NULL, 0, 0);
  ClassP Void = makeClassePredefinie("Void", NULL, NULL, NULL, NULL, NULL, 0, 0);

  /* Creation des methodes predefinies */
  /*MethodeP toString = makeMethode("toString", 0, 0, 0, NIL(Tree), String, NIL(VarDecl), Integer);*/
  MethodeP printInt = makeMethode("printInt", 0, 0, 0, NIL(Tree), String, NIL(VarDecl), Integer);
  MethodeP println = makeMethode("println", 0, 0, 0, NIL(Tree), String, NIL(VarDecl), String);
  MethodeP print = makeMethode("print", 0, 0, 0, NIL(Tree), String, NIL(VarDecl), String);
  
  VarDeclP intVal=NEW(1,VarDecl);
  intVal->name="val";
  intVal->type=NULL;
  intVal->next=NULL;
  intVal->intStrObjet=2;
  intVal->init=NULL;
  Integer->lvar=intVal;

  VarDeclP strVal=NEW(1,VarDecl);
  strVal->name="str";
  strVal->type=NULL;
  strVal->next=NULL;
  strVal->intStrObjet=1;
  strVal->init=NULL;
  String->lvar=strVal;

  printInt->next = NULL;
  print->next = NULL;
  println->next = print;

  /* Ajout des methodes dans leurs classes respectives */
  Integer->methodeL = printInt;
  String->methodeL = println;

  /* Ajout de ces classes predefinies dans la liste de classe */
  Void->next = NULL;
  String->next = Void;
  Integer->next = String;
  listClass = Integer;
}
