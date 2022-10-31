(*
                         CS 51 Final Project
                           MiniML -- Parser
*)
                  
%{
  open Expr ;;
%}

%token EOF
%token OPEN CLOSE
%token LET DOT IN REC
%token NEG 
%token F_NEG
%token PLUS MINUS 
%token F_PLUS F_MINUS
%token TIMES DIVIDEDBY 
%token F_TIMES F_DIVIDEDBY
%token LESSTHAN GREATERTHAN EQUALS
%token CONCAT
%token IF THEN ELSE 
%token FUNCTION
%token RAISE
%token <int> INT 
%token <float> FLOAT
%token <string> STRING
%token <string> ID
%token TRUE FALSE

%nonassoc IF
%left LESSTHAN GREATERTHAN EQUALS
%left PLUS MINUS 
%left F_PLUS F_MINUS
%left TIMES DIVIDEDBY 
%left F_TIMES F_DIVIDEDBY
%left CONCAT
%nonassoc NEG 
%nonassoc F_NEG

%start input
%type <Expr.expr> input

(* Grammar follows *)
%%
input:  exp EOF                 { $1 }

exp:    exp expnoapp            { App($1, $2) }
        | expnoapp              { $1 }

expnoapp: INT                   { Num $1 }
        | FLOAT                 { Float $1 }
        | STRING                { Str $1 }
        | TRUE                  { Bool true }
        | FALSE                 { Bool false }
        | ID                    { Var $1 }
        | exp CONCAT exp        { Binop(Concat, $1, $3) }
        | exp PLUS exp          { Binop(Plus, $1, $3) }
        | exp MINUS exp         { Binop(Minus, $1, $3) }
        | exp TIMES exp         { Binop(Times, $1, $3) }
        | exp DIVIDEDBY exp     { Binop(DividedBy, $1, $3) }
        | exp F_PLUS exp        { Binop(F_Plus, $1, $3) }
        | exp F_MINUS exp       { Binop(F_Minus, $1, $3) }
        | exp F_TIMES exp       { Binop(F_Times, $1, $3) }
        | exp F_DIVIDEDBY exp   { Binop(F_DividedBy, $1, $3) }
        | exp EQUALS exp        { Binop(Equals, $1, $3) }
        | exp LESSTHAN exp      { Binop(LessThan, $1, $3) }
        | exp GREATERTHAN exp   { Binop(GreaterThan, $1, $3) }
        | NEG exp               { Unop(Negate, $2) }
        | F_NEG exp             { Unop(F_Negate, $2) }
        | IF exp THEN exp ELSE exp      { Conditional($2, $4, $6) }
        | LET ID EQUALS exp IN exp      { Let($2, $4, $6) }
        | LET REC ID EQUALS exp IN exp  { Letrec($3, $5, $7) }
        | FUNCTION ID DOT exp   { Fun($2, $4) } 
        | RAISE                 { Raise }
        | OPEN exp CLOSE        { $2 }
;

%%
