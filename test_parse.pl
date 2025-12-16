:- use_module(library(charsio)).
:- ['girard'].

test :-
    Input = "0 = poly a . lambda x : a . lambda f : a -> a . x",
    write('Testing assign_name_ast with: '), write(Input), nl,
    (assign_name_ast(Name, Expr, Input, Rest) ->
        write('Success! Name: '), write(Name), nl,
        write('Expr: '), write(Expr), nl,
        write('Rest: '), write(Rest), nl
    ;   write('Failed to parse!'), nl
    ).

:- initialization(test).
