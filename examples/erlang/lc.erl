-module(lc).
-export([main/0]).

%% List comprehensions compile to letrec + local funs in Core Erlang.
main() ->
    Squares = [X * X || X <- [1, 2, 3, 4, 5]],
    erlang:display(Squares),
    Evens = [X || X <- Squares, X rem 2 =:= 0],
    erlang:display(Evens).
