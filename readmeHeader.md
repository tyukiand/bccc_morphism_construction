# Hom-set morphism generator for bicartesian closed categories

![banner](banner.png)

This is a little Scala-EDSL that enables the user to write down
chains of equalities that describe (iso)morphisms between
hom-sets in BCCC (bicartesian closed categories), from which it
then can reconstruct the complete (iso)morphisms between those
hom-sets.

It can also automatically apply the Yoneda lemma to extract
morphisms between objects given morphisms between their Yoneda
embeddings. Therefore, it is essentially a semi-automated
implementation of the general strategy described for example
in Awodey's *"Category Theory"* section 8.4
*"Applications of the Yoneda Lemma"*.

The basic idea is that if we can construct an isomorphism
between `Hom(A, X)` and `Hom(B, X)` that is natural in `X`, then
the Yoneda lemma gives us a way to construct an explicit
isomorphism between `A` and `B`. For example, in Proposition 8.6,
Awodey wants to show that

    A x (B U C) ~ (A x B) U (A x C)

holds *(here, `A`, `B`, `C` are some objects of a BCCC, and `x`, `U`, `~` 
are ugly ascii-art representations that stand for product,
coproduct, isomorphism respectively)*. In order to show this, he
writes down the following chain of isomorphic hom-sets:

    Hom(A x (B U C), X) ~ 
    Hom(B U C, X^A) ~
    (Hom(B, X^A) x Hom(C, X^A)) ~
    (Hom(A x B, X) x Hom(A x C, X)) ~
    Hom((A x B) U (A x C), X)

(again, up to differences in type-setting), and then applies the
Yoneda lemma corollary to obtain the isomorphism between `A x (B U C)`
and `(A x B) U (A x C)`. 

The present EDSL allows us to interpret the above chain of Hom-sets
literally as executable Scala code. It then fills out the gaps, replacing the
somewhat vague `~`-signs by explicit isomorphisms. Finally, it uses
the Yoneda lemma to convert those isomorphisms to isomorphisms between
underlying objects.

A wall of examples follows.

-----

