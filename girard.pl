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

assoc_key_value([], _Key, _Value) :- fail.
assoc_key_value([First-Second|Rest], Key, Value) :-
    if_(Key = First,
        Value = Second,
        assoc_key_value(Rest, Key, Value)).

%%%
% name_fresh_vars(Name, Fresh, Vars):

name_fresh_vars(Name, Fresh, Vars) :-
    name_prefix(Name, Fresh),
    notmember(Fresh, Vars),
    !.

name_prefix(Name, Name).
name_prefix(Name, ['_'|Mid]) :- name_prefix(Name, Mid).

%%%%%%%%%%
% TYPAGE %
%%%%%%%%%%

type_freevars(var(Name), [Name]).
type_freevars(arrow(Left, Right), Vars) :-
    type_freevars(Left, LV),
    type_freevars(Right, RV),
    ord_union(LV, RV, Vars).
type_freevars(forall(TypeVar, Type), Vars) :-
    type_freevars(Type, BodyVars),
    ord_subtract(BodyVars, [TypeVar], Vars).

env_type(TypeVarEnv, var(Name)) :-
    member(Name, TypeVarEnv).
env_type(TypeVarEnv, arrow(Left, Right)) :-
    env_type(TypeVarEnv, Left),
    env_type(TypeVarEnv, Right).
env_type(TypeVarEnv, forall(TypeVar, Type)) :-
    env_type([TypeVar|TypeVarEnv], Type).

type_rename(var(Name), Old, New, var(NameRen)) :-
    ( Name = Old -> NameRen = New ; NameRen = Name ).
type_rename(arrow(Left, Right), Old, New, arrow(LR, RR)) :-
    type_rename(Left, Old, New, LR),
    type_rename(Right, Old, New, RR).
type_rename(forall(TypeVar, Type), Old, New, forall(NewVar, NewType)) :-
    ( TypeVar = Old ->
        NewVar = New,
        type_rename(Type, Old, New, NewType)
    ;   NewVar = TypeVar,
        type_rename(Type, Old, New, NewType)
    ).

type_subst(var(Name), Search, Replace, Subst) :-
    ( Name = Search -> Subst = Replace
    ; Subst = var(Name)
    ).
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
            type_rename(forall(TypeVar, Type), TypeVar, Fresh,
                        forall(RenamedVar, RenamedBody))
        ;   RenamedVar = TypeVar,
            RenamedBody = Type
        ),
        type_subst(RenamedBody, Search, Replace, NewBody),
        NewVar = RenamedVar
    ).

type_equiv(var(X), var(Y)) :- X = Y.
type_equiv(arrow(A1, B1), arrow(A2, B2)) :-
    type_equiv(A1, A2),
    type_equiv(B1, B2).
type_equiv(forall(TV1, T1), forall(TV2, T2)) :-
    type_freevars(forall(TV1, T1), FV1),
    type_freevars(forall(TV2, T2), FV2),
    ord_union(FV1, FV2, Vars),
    name_fresh_vars(TV1, Fresh, Vars),
    type_rename(T1, TV1, Fresh, RT1),
    type_rename(T2, TV2, Fresh, RT2),
    type_equiv(RT1, RT2).

% EVar: lookup d'abord, check ensuite
env_expr_type(TypeVarEnv, TypeEnv, var(Var), Type) :-
    assoc_key_value(TypeEnv, Var, Type),
    env_type(TypeVarEnv, Type).

env_expr_type(TypeVarEnv, TypeEnv, lambda(Var, ArgType, Body),
              arrow(ArgType, BodyType)) :-
    env_type(TypeVarEnv, ArgType),
    env_expr_type(TypeVarEnv, [Var-ArgType|TypeEnv], Body, BodyType).

env_expr_type(TypeVarEnv, TypeEnv, apply(E1, E2), ResType) :-
    env_expr_type(TypeVarEnv, TypeEnv, E1, arrow(ArgType, ResType)),
    env_expr_type(TypeVarEnv, TypeEnv, E2, ArgType2),
    type_equiv(ArgType, ArgType2).

env_expr_type(TypeVarEnv, TypeEnv, poly(TypeVar, Expr),
              forall(TypeVar, BodyType)) :-
    env_expr_type([TypeVar|TypeVarEnv], TypeEnv, Expr, BodyType).

env_expr_type(TypeVarEnv, TypeEnv, spec(Expr, TypeArg), ResType) :-
    env_expr_type(TypeVarEnv, TypeEnv, Expr, forall(TypeVar, BodyType)),
    env_type(TypeVarEnv, TypeArg),
    type_subst(BodyType, TypeVar, TypeArg, ResType).

%%%%%%%%%%%%%%
% ÉVALUATION %
%%%%%%%%%%%%%%

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

expr_rename(var(Name), Old, New, var(NameRen)) :-
    ( Name = Old -> NameRen = New ; NameRen = Name ).
expr_rename(lambda(Var, Type, Body), Old, New,
            lambda(NewVar, Type, NewBody)) :-
    ( Var = Old ->
        NewVar = New,
        expr_rename(Body, Old, New, NewBody)
    ;   NewVar = Var,
        expr_rename(Body, Old, New, NewBody)
    ).
expr_rename(apply(Left, Right), Old, New, apply(LR, RR)) :-
    expr_rename(Left, Old, New, LR),
    expr_rename(Right, Old, New, RR).
expr_rename(poly(TypeVar, Expr), Old, New, poly(TypeVar, NewExpr)) :-
    expr_rename(Expr, Old, New, NewExpr).
expr_rename(spec(Expr, Type), Old, New, spec(NewExpr, Type)) :-
    expr_rename(Expr, Old, New, NewExpr).

expr_subst(var(Name), Search, Replace, Subst) :-
    ( Name = Search -> Subst = Replace
    ; Subst = var(Name)
    ).
expr_subst(apply(Left, Right), Search, Replace, apply(LR, RR)) :-
    expr_subst(Left, Search, Replace, LR),
    expr_subst(Right, Search, Replace, RR).
expr_subst(poly(TypeVar, Expr), Search, Replace, poly(TypeVar, NewExpr)) :-
    expr_subst(Expr, Search, Replace, NewExpr).
expr_subst(spec(Expr, Type), Search, Replace, spec(NewExpr, Type)) :-
    expr_subst(Expr, Search, Replace, NewExpr).
expr_subst(lambda(Var, Type, Body0), Search, Replace,
           lambda(NewVar, Type, NewBody)) :-
    ( Var = Search ->
        NewVar = Var,
        NewBody = Body0
    ;   expr_freevars(Replace, FVRep),
        ( member(Var, FVRep) ->
            expr_freevars(Body0, FVBody),
            ord_union(FVRep, FVBody, Vars),
            name_fresh_vars(Var, Fresh, Vars),
            expr_rename(lambda(Var, Type, Body0), Var, Fresh,
                        lambda(RenVar, Type, RenBody))
        ;   RenVar = Var,
            RenBody = Body0
        ),
        expr_subst(RenBody, Search, Replace, NewBody),
        NewVar = RenVar
    ).

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

% Scryer: char_type(_, digit) n'existe pas. On accepte lettres unicode (alpha) et chiffres (alnum).
var_start_char(C) :- char_type(C, alpha) ; char_type(C, alnum) ; C = '_'.
var_cont_char(C)  :- char_type(C, alpha) ; char_type(C, alnum) ; C = '_'.

var_ast(var([C])) --> [C], { var_start_char(C) }.
var_ast(var([C|Rest])) --> [C], { var_start_char(C) }, var_ast_tail(Rest).

var_ast_tail([C|Rest]) --> [C], { var_cont_char(C) }, var_ast_tail(Rest).
var_ast_tail([]) --> [].

spaces --> [].
spaces --> " ", spaces.

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

type_ast_print(Type) :-
    type_ast(Type, Str, []), !,
    format("  Type: ~s\n", [Str]).

expr_ast_print(Expr) :-
    expr_ast(Expr, Str, []), !,
    format("Valeur: ~s\n", [Str]).

eval_expr(TypeEnv, ValueEnv, Expr, Type, Value) :-
    env_expr_type([], TypeEnv, Expr, Type) ->
        type_ast_print(Type),
        (
            env_expr_reduce(ValueEnv, Expr, Value) -> expr_ast_print(Value)
          ; format("Valeur: [Erreur]\n", []), fail
        )
  ; format("  Type: [Erreur]\n", []), fail.

assign_name_ast(Name, Expr) -->
    var_ast(var(Name)),
    spaces, "=", spaces,
    expr_ast(Expr).

%% --- FIX PRINCIPAL: enlever \n / \r en fin de ligne ---
strip_eol(Line0, Line) :-
    ( append(Line1, "\r\n", Line0) -> Line = Line1
    ; append(Line1, "\n", Line0)   -> Line = Line1
    ; append(Line1, "\r", Line0)   -> Line = Line1
    ; Line = Line0
    ).

input_parses(Input) :-
    once((
        expr_ast(_, Input, [])
      ; assign_name_ast(_, _, Input, [])
    )).

read_command(FirstPrompt, ContPrompt, Input) :-
    format("~s", [FirstPrompt]),
    flush_output,
    get_line_to_chars(user_input, L0, ""),
    strip_eol(L0, Line0),
    ( Line0 = "" ->
        Input = ""
    ; read_command_more(Line0, ContPrompt, Input)
    ).

read_command_more(Acc, _ContPrompt, Acc) :-
    input_parses(Acc), !.
read_command_more(Acc, ContPrompt, Input) :-
    format("~s", [ContPrompt]),
    flush_output,
    get_line_to_chars(user_input, L1, ""),
    strip_eol(L1, Line1),
    ( Line1 = "" ->
        Input = Acc
    ; append(Acc, " ", Acc1),
      append(Acc1, Line1, Acc2),
      read_command_more(Acc2, ContPrompt, Input)
    ).

toplevel(TypeEnv, ValueEnv) :-
    read_command("> ", "| ", Input),
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
