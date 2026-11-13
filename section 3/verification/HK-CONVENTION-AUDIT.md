# HK convention audit for the tensor comparison

2026-11-12. Requested by the author after review item T001.

Outcome: no convention has been found that removes the fixed-ground
obstruction for the unlocalized graded tensor product. This is a source
and mathematical audit, not a complete Lean construction of the example.
The working manuscript and all Lean statements are unchanged.

## Sources and coverage

The main source is [HK, arXiv math/0510133v3](https://arxiv.org/pdf/math/0510133v3),
the latest version listed by arXiv (28 April 2006). The critical passages
were compared with [v2](https://arxiv.org/pdf/math/0510133v2) and readable
cached extracted text of the [Oxford accepted-manuscript copy,
intv-090310.pdf](https://ora.ox.ac.uk/objects/uuid%3A3f48e02b-c313-4ef3-a3f2-e983a5f0149a/files/mcd1cfc6c194380d69a2f7a03e084dec0).
The Oxford text was recovered after direct retrieval initially returned
403. Its critical definitions and tensor proof agree with v3. The file
name is not treated as proof of a revision date. The publisher's full
chapter was behind subscription access; no comparison with its full
145-page typeset text is claimed. v1 retrieval returned an error.

Read closely: the parameter, definability, algebraic-closure, category,
base-change, grading and localization passages throughout Sections 1–3,
6, 8–10 and 12; the complete tensor proof and its cited group-extension
and generic-type lemmas. Other sections were searched for global scope
changes. This is not a claim to have independently verified every proof
in the 116-page paper or to have proved the absence of all possible errata.

| Passage (v3 printed pages) | Convention checked |
| --- | --- |
| §§1.4–1.6, 5–6 | RES includes rational-value fibres; translations use the ground value group; definability fixes the field. |
| §§2.1–2.1.4, 11–16 | Parameter naming, definable/algebraic distinctions, explicit algebraic base change. |
| §2.2, 18–20 | Grothendieck relations and fibrewise parameter scopes. |
| Lemmas 3.17, 3.21, 3.26–3.28, 26–32 | Generic fibres, local base change, integral monomial structure. |
| §3.7 and §6.0.1, 39–42, 61 | Effective/resolved structures and base-change conditions. |
| Definition 3.66 and Remark 3.67, 45 | Finite labels, finite-value RES objects, arbitrary RV bijections. |
| §8.1, 73–75 | Effective VF isomorphism is distinguished explicitly. |
| Definition 9.1 and §9.1, 83–84 | Ground versus divisible hull; ambient grading; separate localization. |
| Lemma 9.8 and Question 9.9, 87–88 | Explicit annihilator quotient; no blanket cancellation. |
| §10.1, 90–93 | Ordinary tensor universal property; graded comparison. |
| §10.2, 94–95 | Measured comparison reuses injectivity argument. |
| §12.3 and Example 12.8, 108–109 | Henselian ground and RV definable closure. |

## Test 1: is the ground silently algebraically closed?

No blanket replacement by acl(S) is stated in the passages governing the
comparison. Section 2.1.4 explains an available change of theory; it does
not announce that every subsequent category is over the algebraic closure.
The base change used inside the proof of Lemma 3.21 has local scope.

This distinction is material in T001. Put S=C((t)), v(t)=1, and let R be
the five RV roots of rv(t). A valued-field automorphism fixing S sends a
chosen fifth root of t to a primitive fifth root of unity times that root.
Its RV value changes as an RV element, so no element of R is S-definable.
The value 1/5 is nevertheless Gamma-definable. Over acl(S), the elements
of R are individually named and the value translation has a named RV lift.
That changes the example's categories.

Algebraic base change cannot simply be used as an injective descent map:
R and five named points become isomorphic after naming the roots, whereas
before base change R has no S-definable point and the five-point constant
set does. Even on finite positive classes that distinction survives.
No comparison in this audit assumes this base change is harmless.

## Test 2: does A mean the divisible hull of the value group?

The introduction's fixed-field setup and Definition 9.1 distinguish A from
Q tensor A. In the example, A=Z and Q tensor A=Q. The endpoint 1/5 is an
allowed definable endpoint, since it is specified by 5x=1, while translation
by 1/5 is not an A-translation.

If one instead interprets the translation group as all Gamma-definable
points, the translation by 1/5 becomes allowed. That does not restore the
whole fixed-ground comparison: it would allow a Gamma arrow {0}->{1/5}.
The claimed RV lift would be an S-definable bijection from 0^sharp to
(1/5)^sharp. The former contains the S-definable point 1, and the latter
has no S-definable point, since dcl(S) in RV is RV(S), with value group Z.
Thus enlarging the translation group alone breaks the claimed lift functor.
The occasional terminology about definable Gamma constants does not supply
an RV representative, and cannot by itself resolve this conflict.

## Test 3: is the coefficient tensor already localized or ungraded?

The finite-Gamma singleton class tau=[{0}]_1 has degree one. It is distinct
from the degree-zero identity. Corollary 10.3 explicitly concerns a graded
tensor. The tensor universal property in §10.1 is the ordinary semiring
one, rather than a tensor of families with extra descent relations.

The localization and annihilator quotient discussed in §9 are separate
constructions; no application of them to Corollary 10.3 was found.
In particular, additive group completion does not invert tau.

There is a concrete reason the distinction matters. Let

    a = [R]_0 tensor [I]_1,    b = [R]_0 tensor [J]_1,
    I=(0,infinity),           J=(1/5,infinity),
    e_delta=[{1/5}]_1,        e_0=tau.

The original-ground residue bijection (r,x)->(r,r*x) gives

    [R]_0 * lift(e_delta) = [R]_0 * lift(e_0)

in RES[1]. The parameter-free integral unimodular shear

    (alpha,gamma) -> (alpha,gamma+alpha)

takes {1/5} x I onto {1/5} x J, so e_delta*[I]=e_delta*[J] in Gamma[2].
Balancing these two equalities proves

    tau*a = tau*b.

Thus the example disappears after inverting tau. This is a multiplication
by a positive-degree torus class, not an equality a=b in degree one. The
T001 dual-number detector sends tau to zero, and a,b to 0,5*epsilon.
It is consistent with all the displayed equalities. This calculation
explains exactly why cancelling tau would discard the obstruction.

No claim is made here that localizing is the correct replacement theorem
for the paper's intended applications, or that every tensor-injectivity
obligation after that localization has been proved.

## Test 4: is the finite root set excluded from RES[0]?

No. R is a finite original-ground definable RV set, has one Gamma value,
and its constant map to RV^0 is finite-to-one. Hence it fits the finite-map
RES[0] definition used both here and in HK. The map (r,x)->(r,r*x) is a
valid RV[1] bijection. It does not have to preserve the projection labels.

The distinction between dimension grading and ambient arity is retained:
R has degree zero despite its one RV coordinate; I and J have Gamma degree
one. Scissors in a fixed degree do not identify a finite set in degree zero
with the same carrier placed in degree one. The detector respects that.

## Test 5: can compactness or genericity descend the missing lift?

The residual factor can be the complete algebraic type consisting of R;
it need not contain an original-ground definable singleton. After fixing
r, the RV lift is multiplication by r over S(r), and its contracted map
is gamma -> gamma+1/5. Orthogonality makes that Gamma formula independent
of r. It does not make r itself S-definable.

Lemma 2.3 uniformizes witnesses relative to the fibre parameter retained
in the total space. For the R-indexed family it gives the map (r,x)->(r,r*x),
which was already available. It does not choose an S-definable r or produce
an unparameterized map I^sharp->J^sharp. Generic RV inputs also cannot
supply a definable choice from the independent algebraic root type.

The precise remaining step is the equality of tensor terms following
Claim 4 in Proposition 10.2, printed page 92. Claim 3 supplies definable
factor bijections (its f/g names are interchanged in parts of the statement
and proof). The final step uses the Gamma factor to identify classes in
the restricted Gamma category. A same-ground lift is required there.
The finite-root example is a direct test of that extra requirement.
The identities and scope checks in this note identify the apparent gap;
no HK theorem has been used as a premise to bypass it.

## Status for the formalization

The audit strengthens the reason to keep T001 open. No verified manuscript
repair is proposed, and no author approval is inferred from this research
request. Both tensor surjectivities and the generic-fibre monomial lemmas
remain checked. Tensor injectivity and complete Section 3 are not claimed.
The audit itself is mathematical analysis, not a full Lean counterexample.


## Subsequent Claim 3 check

See `HK-CLAIM3-AUDIT.md`. It sharpens the earlier diagnosis: the stated
factor and fibre conclusions of Claim 3 hold in the finite-root example.
The missing stronger conclusion is existence of an RV lift of the Gamma
factor over S, independent of the RES parameter. A cofinal-type argument
rules that out even after every allowed definable neighbourhood shrinking.
The tensor equality used after Claim 4 needs justification beyond Claim 3
as stated; this check does not assert that Claim 3's literal conclusions
have been disproved.
