# HK Proposition 10.2, Claim 3: the exact missing conclusion

Follow-up to the author's request to locate the failure in Claim 3.

The finite-root diagnostic satisfies the stated conclusions of Claim 3
(after correcting its swapped f/g names). It therefore does not refute
Claim 3 as a statement about definable factor bijections. The stronger
conclusion needed to identify Gamma classes in the induction is that the
Gamma factor has an RV lift over the original ground. Clause (3) gives a
lift after fixing the RES parameter. Those are different assertions.
This note identifies that distinction and shows that compactness shrinking
cannot remove it in the example. It does not claim a complete Lean proof
of Claim 3 in all its generality.

Source: [HK, arXiv math/0510133v3, Proposition 10.2, printed pages 91–92]
(https://arxiv.org/pdf/math/0510133v3). Lemma 3.17 is on pages 26–27;
Lemma 2.3 is on page 14; Example 12.8 is on page 109.

## Use unambiguous names

Write h for the RES map and k for the Gamma map. Thus the three desired
properties, over the fixed ground S, are:

1. F restricts to a bijection Qtilde x Ptilde^sharp onto
   Qtilde' x Ptilde'^sharp.
2. h:Qtilde -> Qtilde' and k:Ptilde -> Ptilde' are S-definable bijections.
3. For each q and gamma, F maps {q} x gamma^sharp bijectively onto
   {h(q)} x k(gamma)^sharp.

Property (2) says definable Gamma bijection, not Gamma-category morphism.
The latter additionally requires an RV lift over S. Property (3), after
fixing q, supplies an S(q)-definable lift. Keeping q as an input yields an
S-definable family of lifts, not an S-definable member of that family.

## Check of the proof's steps

* Product completeness: Lemma 3.17 addresses the full-Gamma-dimension input
  and its interaction with stable parameters. It is applicable to an
  algebraic RES type; it does not require that type to be a definable
  singleton. Hence it cannot replace q by an S-definable point.
* Selecting one target product and taking projected types are legitimate
  uses of completeness.
* The dimension sentence needs the chain
  m=dim_Gamma(P') <= dim(Y_i') <= m. The first equality needs the fact that
  stable RES parameters do not create new Gamma rank, together with the
  definable inverse of F. The reversed inequality in the displayed prose
  is a direction typo, not the finite-root obstruction.
* Once P' is full-dimensional, the second application of product
  completeness can yield the full target product of types.
* The RES-coordinate independence argument gives h(q) defined over S(q).
  Uniformity of that h over a definable neighbourhood is a compactness
  issue, with q retained as its argument.
* For the Gamma coordinate, stability alone gives a finite image, rather
  than constancy. Completeness of the relevant product fibre over
  S(gamma), obtainable from the same generic-type argument, supplies
  constancy. The output is k(gamma) in Gamma-definable closure of S(gamma).
  This still does not supply any RV representative of a translation term.
* Compactness can extend fibre coherence to definable neighbourhoods.
  Injectivity must first hold on the types; it is not created by
  compactness itself. Generic full-fibre rigidity can address that
  preliminary point. Neither this injectivity argument nor compactness
  removes the residual parameter from the RV lift.

These observations distinguish omitted justifications from the decisive
parameter descent issue. The finite-root example below satisfies the
factor conclusions globally, so neither the stability sentence nor the
neighbourhood extension is false in that example.

## Instantiate every clause in the diagnostic example

Take S=C((t)), v(t)=1, delta=1/5, and

    R={r in RV : r^5=rv(t)},
    I=(0,infinity), J=(delta,infinity),
    F(r,u)=(r,r*u).

The fifth roots of unity belong to C. The roots of t are permuted
transitively by valued-field automorphisms over the henselian field S.
Consequently R is a complete algebraic S-type Q, with five realizations
and no individually S-definable realization.

Choose P to be the complete Gamma type at positive infinity over S:

    P(gamma) = {gamma > c : c in Q}.

The induced Gamma structure is a divisible ordered Abelian group; this
is a complete one-dimensional type. It is a full-dimensional type of I.
Let Q'=Q, P'=P+delta. Then

    F(Q x P^sharp) = Q x (P+delta)^sharp.

Indeed every r has value delta, and u -> r*u maps each full value fibre
onto the shifted full fibre. We can use the definable neighbourhoods
Qtilde=Qtilde'=R, Ptilde=I and Ptilde'=J. The factor maps, forced by F, are

    h(r)=r,    k(gamma)=gamma+delta.

Both are S-definable bijections. For every r and gamma, multiplication by r
is a bijection gamma^sharp -> (gamma+delta)^sharp. Thus all three literal
conclusions of Claim 3 hold. The RV lift uses r, and its base is S(r).

For the type at positive infinity, P+delta=P as a set of realizations.
Nevertheless the pointwise map k(gamma)=gamma+delta is forced by F and
clause (3); it cannot be replaced by the identity merely because the two
types coincide. P itself is not a definable neighbourhood. The subsequent
shrinking argument concerns definable subsets of the given source I.

## No shrinking around P supplies a same-ground lift

This strengthens merely observing that the displayed lift uses r: it
rules out every possible S-definable lift on any S-definable neighbourhood
of this P.

Let U be an S-definable Gamma set containing P. By o-minimality/pure DOAG
quantifier elimination it contains a final interval (c,infinity), with a
rational endpoint c. Choose an integer N>max(c,0). The element

    u_N=rv(t)^N

is S-definable and has value N in U. Suppose L:U^sharp -> (U+delta)^sharp
were any S-definable function contracting to k. Its value L(u_N) would be
an S-definable RV element of value N+1/5.

But S is henselian, so its RV definable closure is RV(S), whose value group
is Z. The value N+1/5 is not an integer. This is a contradiction. Bijectivity
was not needed: no such S-definable function exists at all.

There is therefore no choice of a smaller S-definable neighbourhood of P
that turns k into a Gamma morphism over S. The residual neighbourhood
cannot select a root either: R itself is a complete algebraic type, so any
S-definable subset of R containing that type is all of R.

## Locate the invalid inference

The restriction in clause (3), for a fixed q, has the form

    L_q(u)=pr_2 F(q,u),  defined over S(q).

Uniformity gives a definable family (q,u)->L_q(u). The inference

    for every q, there is an S(q)-definable RV lift of k
        implies
    there is an S-definable RV lift of k

is false. Definability of the contracted Gamma map k over S is weaker than
definability of an RV lift over S. The finite-root example, even after
all permitted neighbourhood shrinking at P, demonstrates that difference.

The induction's equality of tensor terms after Claim 4 uses the Gamma
factor to identify its restricted-category classes. That needs either the
stronger conclusion that k has a lift over S or some additional argument
establishing the weighted tensor equality by the actual balancing
relations. The latter must not be assumed merely from the lack of a Gamma
morphism; the separate T001 detector supplies the global source-tensor
inequality in this example.

The precise diagnosis is therefore: Claim 3 as written is insufficient
for the induction; Claim 3 strengthened by the same-ground-lift conclusion
would be false here. The proof does not establish that strengthened
conclusion. No weaker statement or stronger hypothesis has been silently
substituted into the manuscript or Lean formalization.


There are two readings to keep distinct. On the literal reading of
“definable bijections,” the root example satisfies Claim 3. If the intended
reading in context is “morphisms of the Gamma category,” then the Gamma
part of that stronger Claim 3 is false by the tail argument. In either
reading, the offending inference is forgetting the residual parameter in
the RV lift, rather than the initial product-completeness calculation.
