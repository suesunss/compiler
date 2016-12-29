Chiffre [0-9]
Entier {Chiffre}+
Lower	[a-z]
Upper	[A-Z]
Lettre	[a-zA-Z_]
LC 	({Lettre}|{Chiffre})
Delim   [ \t\n\r]
Symbole [&+\-*/();:,.{}|]
BS      \\.
PasBSG [^\\"]
IntString ({BS}|{PasBSG})*
Guill		"\""
Star  		"*"
NotStar		[^*]
NotStarPar      [^*/]
InComment       ({NotStar}|({Star}+{NotStarPar}+))*{Star}*
Comment 	"/*"{InComment}"*/"

%{
#include <string.h>
#include <strings.h>
#include "tp.h"
#include "tp_y.h"

extern char *strdup(char *);
extern YYSTYPE yylval;
extern int yylineno;
extern int yylex();

int TesteMotClef(const char *s) {
    
      if (! strcmp(s, "class")) return(CLASS);
      if (! strcmp(s, "extends")) return(EXTENDS);
      if (! strcmp(s, "new")) return(KNEW);
      if (! strcmp(s, "if")) return(IF);
      if (! strcmp(s, "then")) return(THEN);
      if (! strcmp(s, "else")) return(ELSE);
      if (! strcmp(s, "var")) return(VAR);
      if (! strcmp(s, "static")) return(STATIC);
      if (! strcmp(s, "override")) return(OVERRIDE);
      if (! strcmp(s, "def")) return(DEF);
      if (! strcmp(s, "yield")) return(YIELD);
      if (! strcmp(s, "is")) return(IS);
      if (! strcmp(s, "returns")) return(RETURNS);
      if (! strcmp(s, "final")) return(FINAL);
      if (! strcmp(s, "while")) return(WHILE);
      if (! strcmp(s, "do")) return(DO);
      yylval.S = strdup(yytext);
      return(ID);
}

%}

%%
{Entier} 	          { yylval.I = atoi(yytext); return(Cste); }
{Lower}{LC}*	      { return TesteMotClef(yytext); }
{Upper}{LC}*	      { yylval.S = strdup(yytext); return CID; }
\"{IntString}\"       { yylval.S = strdup(yytext); return String; }
{Symbole}	          { return(yytext[0]); }
":="		          { return(AFF); }
"="		              { yylval.C = EQ; return(RELOP); }
"<>"		          { yylval.C = NE; return(RELOP); }
"<="		          { yylval.C = LE; return(RELOP); }
">="		          { yylval.C = GE; return(RELOP); }
">"		              { yylval.C = GT; return(RELOP); }
"<"		              { yylval.C = LT; return(RELOP); }
{Delim}+	          ;
{Comment}	          ;
.		              { printf("Caractere errone: %c a la ligne: %d\n", yytext[0], yylineno); }
%%
