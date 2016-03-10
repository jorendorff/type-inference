[A small implementation of type inference.](infer.hs)

The language is really trivial. No let-bound polymorphism (i.e. generic functions).

I used the `ST` monad because the algorithm I know involves mutably updating type variables.
I'd love to know a stateless algorithm for this.
