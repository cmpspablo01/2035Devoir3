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
%   La paire `Key-Value` est l’un des éléments du dictionnaire `Assoc`,
%   représenté comme une liste de paires.

assoc_key_value([First-Second|Rest], Key, Value) :-
    if_(Key = First,
        Value = Second,
        assoc_key_value(Rest, Key, Value)).

%%%
% name_fresh_vars(Name, Fresh, Vars):
%   `Fresh` est un nom de variable qui n’est pas présent dans la liste de noms `Vars`
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
%   dans l’expression de type `Type`.

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
type_freevars(_, []).

%%%
% env_type(TypeVarEnv, Type):
%   `Type` est une expression de type bien formée dans l’environnement
%   `TypeVarEnv` (une liste de noms de variables de types)

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
env_type(_, var("X")).

%%%
% type_subst(Type, Search, Replace, Subst):
%   `Subst` est l’expression de type obtenue à partir de `Type` en remplaçant chaque
%   occurrence de `var(Search)` par `Replace`, en faisant de l’α-renommage pour éviter
%   la capture des variables libres de `Replace`.

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
type_subst(X, _, _, X).

%%%
% type_equiv(Type1, Type2):
%   Les types `Type1` et `Type2` sont égaux à un ou plusieurs α-renommage près.

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
type_equiv(X, X).

%%%
% env_expr_type(TypeVarEnv, TypeEnv, Expr, Type):
%   `Expr` est une expression bien formée du type `Type` dans l’environnement
%   `TypeVarEnv` (une liste de noms de variables de types) et dans l’environnement
%   `TypeEnv` (un dictionnaire associant chaque variable d’expression à son type).

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
env_expr_type(_, _, _, var("X")).

%%%%%%%%%%%%%%
% ÉVALUATION %
%%%%%%%%%%%%%%

%%%
% expr_freevars(Expr, Vars):
%   `Vars` contient la liste des noms de variables libres
%   dans l’expression de valeur `Expr`.

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
expr_freevars(_, []).

%%%
% expr_subst(Expr, Search, Replace, Subst):
%   `Subst` est l’expression de valeur obtenue à partir de `Expr` en remplaçant chaque
%   occurrence de `var(Search)` par `Replace`, en faisant de l’α-renommage pour éviter
%   la capture des variables libres de `Replace`.

% SUPPRIMER LA LIGNE SUIVANTE ET COMPLÉTER
expr_subst(X, _, _, X).

%%%
% env_expr_reduce(ValueEnv, Expr, Value)
%   `Value` est la valeur obtenue en réduisant le plus possible l’expression `Expr`
%   dans l’environnement `ValueEnv` (un dictionnaire associant chaque variable
%   d’expression à sa valeur)

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
% spaces: Suite d’espaces potentiellement vide.

spaces --> [].
spaces --> " ", spaces.

%%%
% expr_ast(Ast, Expr, []):
%   `Expr` est une expression syntaxiquement correcte dont l’arbre
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
%   `Expr` est une expression de type syntaxiquement correcte dont l’arbre
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
%   Affiche sur la sortie standard une représentation de l’expression de type `Type`

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
%   Tente de typer et d’évaluer l’expression `Expr` pour obtenir son type `Type` et sa
%   valeur `Value` dans l’environnement de valeur `ValueEnv` et de type `TypeEnv`. Affiche
%   le résultat ou l’erreur sur la sortie standard.

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
%   Boucle du toplevel avec l’environnement de type `TypeEnv` et de valeur `ValueEnv`.

toplevel(TypeEnv, ValueEnv) :-
    format("> ", []),
    flush_output,
    get_line_to_chars(user_input, FullLine, ""),
    append(Input, "\n", FullLine),
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
