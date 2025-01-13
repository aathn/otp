-module(t).
-export([t/2]).

t(A, B) ->
    case A of
        0 -> A
      ; 1 -> B
    end.
