-module(demo).
-export([main/0]).

sum([], Acc) -> Acc;
sum([H|T], Acc) -> sum(T, Acc + H).


range(N, N) -> [N];
range(I, N) -> [I | range(I + 1, N)].

classify(X) when X > 100 -> {big, X};
classify(X) when X > 10  -> {medium, X};
classify(X) -> {small, X}.

main() ->
    L = range(1, 10),
    erlang:display(L),
    erlang:display(sum(L, 0)),
    erlang:display(classify(5)),
    erlang:display(classify(50)),
    erlang:display(classify(500)),
    erlang:display({done, [a, b | c]}).
