:- use_module(library(charsio)).
:- use_module(library(dif)).
:- use_module(library(ordsets)).
:- use_module(library(reif)).
:- use_module(library(lists)).

%%%
% notmember(Value, List):
%   `Value` est différent de tous les éléments de la liste `List`.

notmember(_, []).
notmember(Elem, [Head|Rest]) :-
    dif(Elem, Head),
    notmember(Elem, Rest).

%%%
% assoc_key_value(Assoc, Key, Value):
%   La paire `Key-Value` est l'un des éléments du dictionnaire `Assoc`,
%   représenté comme une liste de paires.

assoc_key_value([], _, _) :- fail.
assoc_key_value([First-Second|Rest], Key, Value) :-
    if_(Key = First,
        Value = Second,
        assoc_key_value(Rest, Key, Value)).

%%%
% name_fresh_vars(Name, Fresh, Vars):
%   `Fresh` est un nom de variable qui n'est pas présent dans la liste de noms `Vars`
%   et qui est obtenu à partir du nom original `Name`.

name_fresh_vars(Name, Fresh, Vars) :-
    name_prefix(Name, Fresh),
    notmember(Fresh, Vars),
    !.

name_prefix(Name, Name).
name_prefix(Name, ['_'|Mid]) :- name_prefix(Name, Mid).

%%%%%%%%%%
% TYPAGE %
%%%%%%%%%%

%%%
% type_freevars(Type, Vars):
%   `Vars` contient la liste des noms de variables libres
%   dans l'expression de type `Type`.

type_freevars(var(Name), [Name]).
type_freevars(arrow(Left, Right), Vars) :-
    type_freevars(Left, LV),
    type_freevars(Right, RV),
    ord_union(LV, RV, Vars).
type_freevars(forall(TypeVar, Type), Vars) :-
    type_freevars(Type, BodyVars),
    ord_subtract(BodyVars, [TypeVar], Vars).

%%%
% env_type(TypeVarEnv, Type):
%   `Type` est une expression de type bien formée dans l'environnement
%   `TypeVarEnv` (une liste de noms de variables de types)

env_type(TypeVarEnv, var(Name)) :-
    member(Name, TypeVarEnv).
env_type(TypeVarEnv, arrow(Left, Right)) :-
    env_type(TypeVarEnv, Left),
    env_type(TypeVarEnv, Right).
env_type(TypeVarEnv, forall(TypeVar, Type)) :-
    env_type([TypeVar|TypeVarEnv], Type).

%%%
% type_subst(Type, Search, Replace, Subst):
%   `Subst` est l'expression de type obtenue à partir de `Type` en remplaçant chaque
%   occurrence de `var(Search)` par `Replace`, en faisant de l'α-renommage pour éviter
%   la capture des variables libres de `Replace`.

type_subst(var(Name), Search, Replace, Subst) :-
    ( Name = Search -> Subst = Replace ; Subst = var(Name) ).
type_subst(arrow(Left, Right), Search, Replace, arrow(LR, RR)) :-
    type_subst(Left, Search, Replace, LR),
    type_subst(Right, Search, Replace, RR).
type_subst(forall(TypeVar, Type), Search, Replace, forall(NewVar, NewBody)) :-
    ( TypeVar = Search ->
        NewVar = TypeVar,
        NewBody = Type
    ;   type_freevars(Replace, FVRep),
        ( member(TypeVar, FVRep) ->
            type_freevars(Type, FVType),
            ord_union(FVRep, FVType, Vars),
            name_fresh_vars(TypeVar, Fresh, Vars),
            type_subst(Type, TypeVar, var(Fresh), RenamedBody),
            type_subst(RenamedBody, Search, Replace, NewBody),
            NewVar = Fresh
        ;   type_subst(Type, Search, Replace, NewBody),
            NewVar = TypeVar
        )
    ).

%%%
% type_equiv(Type1, Type2):
%   Les types `Type1` et `Type2` sont égaux à un ou plusieurs α-renommage près.

type_equiv(var(X), var(Y)) :- X = Y.
type_equiv(arrow(A1, B1), arrow(A2, B2)) :-
    type_equiv(A1, A2),
    type_equiv(B1, B2).
type_equiv(forall(TV1, T1), forall(TV2, T2)) :-
    type_freevars(forall(TV1, T1), FV1),
    type_freevars(forall(TV2, T2), FV2),
    ord_union(FV1, FV2, Vars),
    name_fresh_vars(TV1, Fresh, Vars),
    type_subst(T1, TV1, var(Fresh), RT1),
    type_subst(T2, TV2, var(Fresh), RT2),
    type_equiv(RT1, RT2).

%%%
% env_expr_type(TypeVarEnv, TypeEnv, Expr, Type):
%   `Expr` est une expression bien formée du type `Type` dans l'environnement
%   `TypeVarEnv` (une liste de noms de variables de types) et dans l'environnement
%   `TypeEnv` (un dictionnaire associant chaque variable d'expression à son type).

% EVar
env_expr_type(TypeVarEnv, TypeEnv, var(Var), Type) :-
    assoc_key_value(TypeEnv, Var, Type),
    env_type(TypeVarEnv, Type).

% Abs
env_expr_type(TypeVarEnv, TypeEnv, lambda(Var, ArgType, Body),
              arrow(ArgType, BodyType)) :-
    env_type(TypeVarEnv, ArgType),
    env_expr_type(TypeVarEnv, [Var-ArgType|TypeEnv], Body, BodyType).

% App
env_expr_type(TypeVarEnv, TypeEnv, apply(E1, E2), ResType) :-
    env_expr_type(TypeVarEnv, TypeEnv, E1, arrow(ArgType, ResType)),
    env_expr_type(TypeVarEnv, TypeEnv, E2, ArgType2),
    type_equiv(ArgType, ArgType2).

% Poly
env_expr_type(TypeVarEnv, TypeEnv, poly(TypeVar, Expr),
              forall(TypeVar, BodyType)) :-
    env_expr_type([TypeVar|TypeVarEnv], TypeEnv, Expr, BodyType).

% Spec
env_expr_type(TypeVarEnv, TypeEnv, spec(Expr, TypeArg), ResType) :-
    env_expr_type(TypeVarEnv, TypeEnv, Expr, forall(TypeVar, BodyType)),
    env_type(TypeVarEnv, TypeArg),
    type_subst(BodyType, TypeVar, TypeArg, ResType).

%%%%%%%%%%%%%%
% ÉVALUATION %
%%%%%%%%%%%%%%

%%%
% expr_freevars(Expr, Vars):
%   `Vars` contient la liste des noms de variables libres
%   dans l'expression de valeur `Expr`.

expr_freevars(var(Name), [Name]).
expr_freevars(lambda(Var, _Type, Body), Vars) :-
    expr_freevars(Body, BodyVars),
    ord_subtract(BodyVars, [Var], Vars).
expr_freevars(apply(Left, Right), Vars) :-
    expr_freevars(Left, LV),
    expr_freevars(Right, RV),
    ord_union(LV, RV, Vars).
expr_freevars(poly(_TypeVar, Expr), Vars) :-
    expr_freevars(Expr, Vars).
expr_freevars(spec(Expr, _Type), Vars) :-
    expr_freevars(Expr, Vars).

%%%
% expr_subst(Expr, Search, Replace, Subst):
%   `Subst` est l'expression de valeur obtenue à partir de `Expr` en remplaçant chaque
%   occurrence de `var(Search)` par `Replace`, en faisant de l'α-renommage pour éviter
%   la capture des variables libres de `Replace`.

expr_subst(var(Name), Search, Replace, Subst) :-
    ( Name = Search -> Subst = Replace ; Subst = var(Name) ).
expr_subst(apply(Left, Right), Search, Replace, apply(LR, RR)) :-
    expr_subst(Left, Search, Replace, LR),
    expr_subst(Right, Search, Replace, RR).
expr_subst(poly(TypeVar, Body), Search, Replace, poly(TypeVar, NewBody)) :-
    expr_subst(Body, Search, Replace, NewBody).
expr_subst(spec(Expr, Type), Search, Replace, spec(NewExpr, Type)) :-
    expr_subst(Expr, Search, Replace, NewExpr).
expr_subst(lambda(Var, Type, Body), Search, Replace, lambda(NewVar, Type, NewBody)) :-
    ( Var = Search ->
        NewVar = Var,
        NewBody = Body
    ;   expr_freevars(Replace, FVRep),
        ( member(Var, FVRep) ->
            expr_freevars(Body, FVBody),
            ord_union(FVRep, FVBody, Vars),
            name_fresh_vars(Var, Fresh, Vars),
            expr_subst(Body, Var, var(Fresh), RenamedBody),
            expr_subst(RenamedBody, Search, Replace, NewBody),
            NewVar = Fresh
        ;   expr_subst(Body, Search, Replace, NewBody),
            NewVar = Var
        )
    ).

%%%
% env_expr_reduce(ValueEnv, Expr, Value)
%   `Value` est la valeur obtenue en réduisant le plus possible l'expression `Expr`
%   dans l'environnement `ValueEnv` (un dictionnaire associant chaque variable
%   d'expression à sa valeur)

env_expr_reduce(ValueEnv, var(Var), Value) :-
    assoc_key_value(ValueEnv, Var, Value), !.

env_expr_reduce(_, var(Var), var(Var)).

env_expr_reduce(ValueEnv, apply(Left, Right), Res) :-
    env_expr_reduce(ValueEnv, Left, LeftRed),
    if_(LeftRed = lambda(Var, _, Body),
        (
            expr_subst(Body, Var, Right, Subst),
            env_expr_reduce(ValueEnv, Subst, Res)
        ),
        (
            env_expr_reduce(ValueEnv, Right, RightRed),
            Res = apply(LeftRed, RightRed)
        )
    ).

env_expr_reduce(ValueEnv, lambda(Var, Type, Body), lambda(Var, Type, BodyRed)) :-
    env_expr_reduce(ValueEnv, Body, BodyRed).

env_expr_reduce(ValueEnv, spec(Poly, _), Res) :- env_expr_reduce(ValueEnv, Poly, Res).

env_expr_reduce(ValueEnv, poly(_, Body), Res) :- env_expr_reduce(ValueEnv, Body, Res).

%%%%%%%%%%%
% SYNTAXE %
%%%%%%%%%%%

%%%
% var_ast(var(Name)):
%   `var(Name)` est une variable.

var_ast(var([Char])) --> [Char], {char_type(Char, alnum)}.
var_ast(var([Char|Rest])) --> [Char], {char_type(Char, alnum)}, var_ast(var(Rest)).

%%%
% spaces: Suite d'espaces potentiellement vide.

spaces --> [].
spaces --> " ", spaces.

%%%
% expr_ast(Ast, Expr, []):
%   `Expr` est une expression syntaxiquement correcte dont l'arbre
%   de syntaxe abstrait est `Ast`.

expr_ast(Ast) --> lambda_ast(Ast).
expr_ast(Ast) --> poly_ast(Ast).
expr_ast(Ast) --> apply_ast(Ast).
expr_ast(Ast) --> var_ast(Ast).

lambda_ast(lambda(Var, Type, Body)) -->
    "lambda ", spaces,
    var_ast(var(Var)),
    spaces, ":", spaces,
    type_ast(Type),
    spaces, ".", spaces,
    expr_ast(Body).

poly_ast(poly(TypeVar, Body)) -->
    "poly ", spaces,
    var_ast(var(TypeVar)),
    spaces, ".", spaces,
    expr_ast(Body).

elem_tree_left(Elem, apply(Left, Right), apply(LeftTr, Right)) :-
    elem_tree_left(Elem, Left, LeftTr).

elem_tree_left(Elem, spec(Left, Right), spec(LeftTr, Right)) :-
    elem_tree_left(Elem, Left, LeftTr).

elem_tree_left(Elem, expr(Var), apply(Elem, Var)).
elem_tree_left(Elem, type(Var), spec(Elem, Var)).

apply_ast(Ast) -->
    {(nonvar(Ast) -> elem_tree_left(Fun, Rest, Ast)); true},
    apply_item_ast(expr(Fun)), apply_tail_ast(Rest),
    {elem_tree_left(Fun, Rest, Ast)}.

apply_tail_ast(Ast) -->
    {(nonvar(Ast) -> elem_tree_left(Fun, Rest, Ast)); true},
    " ", spaces, apply_item_ast(Fun), apply_tail_ast(Rest),
    {elem_tree_left(Fun, Rest, Ast)}.

apply_tail_ast(Arg) -->
    " ", spaces, apply_item_ast(Arg).

apply_item_ast(expr(Ast)) --> "(", lambda_ast(Ast), ")".
apply_item_ast(expr(Ast)) --> "(", apply_ast(Ast), ")".
apply_item_ast(expr(Ast)) --> "(", poly_ast(Ast), ")".
apply_item_ast(type(Ast)) --> "[", type_ast(Ast), "]".
apply_item_ast(expr(Ast)) --> var_ast(Ast).

%%%
% type_ast(Ast, Expr, []):
%   `Expr` est une expression de type syntaxiquement correcte dont l'arbre
%   de syntaxe abstrait est `Ast`.

type_ast(Ast) --> forall_ast(Ast).
type_ast(Ast) --> arrow_ast(Ast).
type_ast(Ast) --> var_ast(Ast).

forall_ast(forall(TypeVar, Type)) -->
    "forall ", spaces,
    var_ast(var(TypeVar)),
    spaces, ".", spaces,
    type_ast(Type).

arrow_ast(arrow(Left, Right)) -->
    termtype_ast(Left),
    spaces, "->", spaces,
    type_ast(Right).

termtype_ast(Ast) --> "(", forall_ast(Ast), ")".
termtype_ast(Ast) --> "(", arrow_ast(Ast), ")".
termtype_ast(Ast) --> var_ast(Ast).

%%%%%%%%%%%%
% TOPLEVEL %
%%%%%%%%%%%%

%%%
% type_ast_print(Type):
%   Affiche sur la sortie standard une représentation de l'expression de type `Type`

type_ast_print(Type) :-
    type_ast(Type, Str, []), !,
    format("  Type: ~s\n", [Str]).

%%%
% expr_ast_print(Expr):
%   Affiche sur la sortie standard une représentation de la valeur `Expr`

expr_ast_print(Expr) :-
    expr_ast(Expr, Str, []), !,
    format("Valeur: ~s\n", [Str]).

%%%
% eval_expr(TypeEnv, ValueEnv, Expr, Type, Value):
%   Tente de typer et d'évaluer l'expression `Expr` pour obtenir son type `Type` et sa
%   valeur `Value` dans l'environnement de valeur `ValueEnv` et de type `TypeEnv`. Affiche
%   le résultat ou l'erreur sur la sortie standard.

eval_expr(TypeEnv, ValueEnv, Expr, Type, Value) :-
    env_expr_type([], TypeEnv, Expr, Type) ->
        type_ast_print(Type),
        (
            env_expr_reduce(ValueEnv, Expr, Value) -> expr_ast_print(Value)
          ; format("Valeur: [Erreur]\n", []), fail
        )
  ; format("  Type: [Erreur]\n", []), fail.

%%%
% assign_name_ast(Name, Expr, Line, []):
%   Lit une expression de la forme `Name = Expr` dans la chaîne de caractères `Line`.

assign_name_ast(Name, Expr) -->
    var_ast(var(Name)),
    spaces, "=", spaces,
    expr_ast(Expr).

%%%
% toplevel(TypeEnv, ValueEnv):
%   Boucle du toplevel avec l'environnement de type `TypeEnv` et de valeur `ValueEnv`.

trim(Line, Trimmed) :- append(Trimmed, "\n", Line), !.
trim(Line, Trimmed) :- append(Trimmed, "\r\n", Line), !.
trim(Line, Trimmed) :- append(Trimmed, "\r", Line), !.
trim(Line, Line).

toplevel(TypeEnv, ValueEnv) :-
    format("> ", []),
    flush_output,
    get_line_to_chars(user_input, FullLine, ""),
    trim(FullLine, Input),
    (
        Input = "" -> halt
      ; (expr_ast(Expr, Input, []),
            (eval_expr(TypeEnv, ValueEnv, Expr, _, _) ; true),
            NewTypeEnv = TypeEnv,
            NewValueEnv = ValueEnv)
      ; (assign_name_ast(Name, Expr, Input, []),
            (
                (eval_expr(TypeEnv, ValueEnv, Expr, Type, Value),
                    NewTypeEnv = [Name-Type|TypeEnv],
                    NewValueEnv = [Name-Value|ValueEnv])
              ; (NewTypeEnv = TypeEnv, NewValueEnv = ValueEnv)
            ))
      ; (format("[Syntaxe invalide]\n", []),
            NewTypeEnv = TypeEnv, NewValueEnv = ValueEnv)
    ),
    format("\n", []),
    toplevel(NewTypeEnv, NewValueEnv).

main :-
    format("Girard (donnez une entrée vide pour quitter)\n", []),
    catch(
        toplevel([], []),
        Exception,
        (loader:write_error(Exception), halt(42))
    ).
