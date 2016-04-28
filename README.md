[A small implementation of type inference.](infer.hs)

You enter an expression. The program tells you its type.

    infer> parse
    (String -> Int)
    infer> parse "123"
    Int
    infer> (\p -> p (\a -> \b -> a)) ((\a -> \b -> \f -> f a b) 33 "33")
    Int
    infer> (\f -> \g -> \x -> f (g x))
    unresolved type variable

The language is really trivial. No `let` expressions, no generic types
(as you can see on the last line above).

I tried to make the code fairly easy to read, but it still needed a ton
of comments.


## Exercises

Want to try something cool?

1.  Add a `TList` type, so we can have lists as well as functions.
    This is surprisingly easy!
    If you search for `TString`, you'll find all the places you need to change.

2.  Add `map`, `mul`, and `numbers` bindings such that the program can correctly
    tell you the type of this expression:

        map (\x -> mul x x) numbers

    (The tricky one is `map`.)

Of course if you really wanted to get serious about it,
you'd want to support `let` expressions, full generic types, and so forth.
