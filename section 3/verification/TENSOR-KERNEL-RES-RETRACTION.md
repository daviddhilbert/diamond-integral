# T001: the unmeasured kernel is killed by the RES Euler evaluations

Current export status: both positive kernel congruences and both actual
ring-kernel ideals are now proved. See the dated export section at the
end; earlier pending-work notes below preserve their historical status.

The author's next question concerns the effect of the unmeasured kernel
on the retraction to RES. The answer is that both Euler evaluations kill
the entire tensor kernel. Their definitions therefore descend through
the surjection Psi; tensor injectivity is unnecessary for this descent.
There is no additional quotient of RES beyond the existing !I quotient.
This is a mathematical consequence of the kernel presentation, not a
claim that the complete Section 4 construction is already formalized.

## Use the actual target

Write

    T = K RES[*] tensor_(K Gamma^fin[*]) K Gamma[*],
    Rbar = K RES[*] / !I[*],
    q: K RES[*] -> Rbar,
    tau = q([G_m]_1).

Here !I[*] has the homogeneous degree-one generators
[delta^sharp]_1-[G_m]_1 for old-ground definable Gamma points delta.
The quotient and the grading are retained. The degree-one tau is not
the degree-zero unit.

For either chi=chi_g or chi=chi_b, define the Euler evaluation on
homogeneous pure tensors by

    Etilde_chi([X]_r tensor [U]_m)
      = q([X]_r) tau^m chi(U) in Rbar_(r+m).                 (1)

This is a well-defined graded ring homomorphism on T before using Psi.
One way to construct it is to start with the homogeneous tensor products
over Z and check the full graded balancing relations. If C is a finite
Gamma object of degree l with N points, then

    q([C^sharp]_l)=N tau^l,    chi(C)=N.

Indeed every tuple of values contributes the product of its value
fibres, all identified with G_m in Rbar. Thus evaluating a finite Gamma
coefficient on the RES side or on the Gamma side has the same effect.
Products and sums are respected by the Euler characteristics and the
degree factors tau^m. This explains where the existing !I quotient is
needed. A map with this formula into the raw RES ring generally would
not satisfy the balancing relations.

## The Gamma invariance used here is numerical

For every definable Gamma set U and every old-ground definable delta,

    chi_g(U+delta e_i)=chi_g(U),
    chi_b(U+delta e_i)=chi_b(U).                             (2)

The first is ordinary definable-bijection invariance of the geometric
Euler characteristic. For the second, translation and its inverse
preserve boundedness; the bounded Euler characteristic of semilinear
sets is invariant under such affine bijections. This can also be checked
directly from the polyhedral truncation construction: partition into
relatively open polyhedra P and use the face formula

    chi_b(P)=(-1)^(dim P) chi_g(closure P).

The formula follows by the alternating face calculation for a sufficiently
large closed-box truncation. For a bounded P it is the usual open-polytope
value. In general the recession cone is unchanged by translating P;
the truncated-face calculation has the same eventual value. Translation
also preserves dim P and commutes with closure, so the displayed formula
proves (2), and additivity gives it for U. This numerical Gamma fact does
not require the translation to have an RV lift over S. It therefore
applies to the very translations responsible for the failure of tensor
injectivity. No HK comparison or same-ground RV lift is used here.

The construction and invariance of the Gamma Euler characteristics remain
separate formalization work. Equation (2) is not a new assumption about
RV-definable representatives, or a claim that the original Gamma category
has been enlarged.

## Evaluate the generators

The mathematical unmeasured presentation gives generators

    g=[X]_r tensor ([U]_m-[U+delta e_i]_m),

whenever there is an S-definable function c:X -> delta^sharp. By (1)-(2),

    Etilde_chi(g)
      = q([X]_r) tau^m (chi(U)-chi(U+delta e_i))
      = 0.                                                  (3)

Since Etilde_chi is a ring homomorphism, it annihilates the ideal generated
by these elements, namely

    ker(Psi) <= ker(Etilde_chi).                              (4)

Vanishing is direct on each generator. The earlier relation
tau*ker(Psi)=0 is not being used to cancel a torus class in the target.
The conclusion holds already in Rbar, before any localization or forgetting
of the grading.

## Descent replaces the use of an inverse

Since Psi is surjective, (4) gives a unique homomorphism

    E_chi: K RV[*] -> Rbar,
    E_chi composed with Psi = Etilde_chi.                     (5)

To compute E_chi(v), choose any tensor t with Psi(t)=v and use (1).
Another choice t' differs by an element of ker(Psi), so (3)-(4) give the
same answer. On RES classes the map is the existing quotient q.

Thus the Section 4 sentence invoking Psi inverse can be replaced by:

    The balanced Euler evaluation annihilates ker(Psi), so it descends
    through the surjective map Psi to K RV[*].

This is the needed mathematical correction to that part of the
construction. It is a proposal recorded for review, not a change to the
approved working manuscript. There is no need to choose a tensor inverse
or impose any further relation on RES for this purpose.

## Subsequent bounded and geometric normalizations

Let s=[1]_1 in Rbar and let L_1=tau+s be the homogeneous affine-line
class. For a homogeneous RV class v of degree n, the subsequent formulas
are

    mathbb E_b(v)=s^(-n) E_b(v),
    mathbb E_g(v)=L_1^(-n) E_g(v),

in the corresponding graded localizations and their degree-zero pieces.
The vanishing (3) survives these normalizations, as well as the further
dimension-free maps used for the bounded target. Consequently the tensor
kernel found in T001 causes no additional ambiguity in either retraction.
In particular it does not obstruct the bounded Euler map used later in
the paper. This conclusion does not certify the other grading,
localization-comparison, or Section 4 claims independently.

For the fifth-root example, with R in RES[0], I=(0,infinity) and
J=(1/5,infinity), the two individual tensor representatives have images

    Etilde_b([R] tensor [I])=Etilde_b([R] tensor [J])=0,
    Etilde_g([R] tensor [I])=Etilde_g([R] tensor [J])=-q([R]) tau.

Thus both kill their nonzero difference. After the geometric
normalization, their common image is -q([R]) tau L_1^(-1).

## Status

The kernel presentation and the above global descent remain mathematical
proofs, not complete Lean exports. No source theorem has been weakened
or accepted from HK, and no Lean source, verification receipt, or approved
main text has been changed. This follow-up is part of the same T001 review
and does not open a new batch of Section 4 referee corrections.


## Actual ring-kernel exports — 2026-11-12

The positive presentations are primary. `TensorRingKernelPresentations`
now instantiates their groupification in both actual tensor products over
the original finite-Gamma coefficient rings. The ideal is the span of
`e(of a) - e(of b)` for exactly the explicit positive translation pairs
`(a,b)`, where `e` is the canonical completion/tensor equivalence. Its pure
tensor formula is checked. Thus the witness c remains existential and all
RES degrees, Gamma domains, finite tags and measured forms are retained.

`gammaGroundUnmeasuredGroupTensor_kernel` and
`gammaGroundMeasuredGroupTensor_kernel` identify these ideals with the
entire actual kernels. Both quotient ring equivalences evaluate on a
quotient class by the original groupified tensor map. The context exports
`proposition_3_18_unmeasured_ring` and `proposition_3_18_measured_ring`
retain the paper's actual VF/Gamma-generated ground.

`TensorRingDescent` proves that a ring evaluation descends if and only if
it agrees on the explicit positive pairs, and supplies the descended map,
its image formula and uniqueness. Its annular theorem identifies the full
pullback inclusion with the explicit unmeasured relation ideal, including
presentation ambiguity. The concrete bounded section 4 comparison maps
and numerical Gamma Euler constructions remain section 4 work; this is
not a claim to have constructed those maps.

These proofs follow from the already checked positive kernels and local
completion algebra. They introduce no HK, [19], R--Y or other additional
cited premise. They assume neither cancellation nor that a positive
semiring embeds in its group completion. The four new modules pass
the full integrated build and declaration audit: 1,002 supporting modules,
5,314 audited declarations and standard logical principles only.
The approved manuscript is unchanged.
