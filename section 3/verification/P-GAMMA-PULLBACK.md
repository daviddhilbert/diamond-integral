# T001: pullback of P_Gamma and the unmeasured tensor kernel

Current export status: both positive kernel congruences and both actual
ring-kernel ideals are now proved. See the dated export section at the
end; earlier pending-work notes below preserve their historical status.

The author's priority question is whether the P_Gamma ideal in the
next section is compatible with the new tensor kernel and the RES
retraction. The natural inclusion, after forgetting volume forms and
passing from bounded objects to the full unmeasured ring, does hold.
It can be proved directly, without the complete kernel presentation.

This note also distinguishes that inclusion from the stronger and
different claim that the bounded measured tensor kernel is generated
by the annular P_gamma lifts. The latter is false; the correct tensor
quotient retains both ideals. Neither distinction prevents the RES
retraction from descending.

## The precise diagram

Use the following graded rings and maps:

    T_mu_db = K muRES[*] tensor_(K muGamma^fin[*]) K muGamma^db[*],
    B = K muRV^db[*],
    q = mu-Psi^db : T_mu_db -> B,

    T = K RES[*] tensor_(K Gamma^fin[*]) K Gamma[*],
    A = K RV[*],
    Psi : T -> A.

Let f:T_mu_db -> T forget forms and include the bounded Gamma objects
into the full Gamma category. Let u:B -> A forget forms and include
the bounded RV objects into the full RV category. They are genuine
ring homomorphisms, compatible with the finite-Gamma coefficients.
On pure tensors the product-lift definitions give

    Psi composed with f = u composed with q.                 (1)

In particular no injectivity of a bounded-to-unbounded inclusion is
being assumed. Set J=(P_Gamma) in B and K=ker(Psi). The natural
pullback check is

    f(q^(-1)(J)) subset K.                                  (2)

This puts the two ideals in the same ring and makes the direction of
the inclusion explicit.

## Each stipulated P_gamma vanishes after unmeasured forgetting

Take a radius gamma>=0 for which the definition supplies an S-definable
t_gamma in gamma^sharp. This uses exactly the original-ground lift
stipulated in the manuscript, not a new root or parameter extension.
The RV annulus in P_gamma is

    RV^(circ circ) minus RV^(circ circ)_gamma
       = val^(-1)((0,gamma]).

The right endpoint is included. Put H_a=(a,infinity). In the full
unmeasured ring,

    u(P_gamma)
      = [(0,gamma]^sharp]+[{t_gamma}]_1-[{1}]_1
      = [H_0^sharp]-[H_gamma^sharp]
      = 0.                                                  (3)

The singleton classes are equal by their original-ground definable
bijection. Multiplication by t_gamma is an original-ground unmeasured
RV bijection H_0^sharp -> H_gamma^sharp, giving the last equality.
Equivalently the Gamma translation alpha |-> alpha+gamma is an
allowed original-ground Gamma morphism because t_gamma is its RV
multiplier.

At gamma=0 the annulus is empty and the two value-zero singleton
objects are already isomorphic; P_0=0. Formula (3) therefore includes
the zero-radius case. Splitting (0,gamma] into (0,gamma) and {gamma}
would require treating gamma=0 separately.

These equalities are in groupified rings. The tail argument uses
ordinary additive group cancellation, not cancellation or inversion of
a torus class. The tails are unbounded, so (3) must not be asserted as
an equality inside the bounded ring before passing to the full one.

Because u is a ring homomorphism, (3) proves u(J)=0 for the entire
ideal, including arbitrary coefficients. For every z in q^(-1)(J),
equation (1) now gives

    Psi(f(z))=u(q(z))=0,

which proves (2). This is the full pullback, not just a chosen list of
tensor representatives of the P_gamma generators. It automatically
includes all ambiguities in those representatives.

## The canonical tensor lifts actually map to zero in T

A convenient lift of P_gamma is

    ptilde_gamma =
      1 tensor [((0,gamma],0)]_1
      + [({t_gamma},id,0)]_1 tensor 1
      - [({1},id,0)]_1 tensor 1.                             (4)

It satisfies q(ptilde_gamma)=P_gamma. After applying f, the two RES
singletons cancel, while in the full Gamma ring

    [(0,gamma]]_1=[H_0]_1-[H_gamma]_1=0.

Thus f(ptilde_gamma)=0 already in T, a stronger statement for these
particular lifts. The same is not asserted for every element of the
full pullback (2): it need only map into K, which is nonzero.

## The RES retraction therefore descends

Let Etilde_b:T -> Rbar=K RES[*]/!I[*] be the balanced Euler evaluation
previously checked mathematically, with

    Etilde_b([X]_r tensor [U]_m)=q_RES([X]_r) tau^m chi_b(U).

The previous calculation proves Etilde_b(K)=0. Combining it with (2),

    (Etilde_b composed with f)(q^(-1)(J))=0.                  (5)

Thus the RES formula is independent of both the tensor preimage and
the representative modulo P_Gamma. No additional quotient of RES is
required beyond !I[*]. If the evaluation is made in the raw RES ring
before taking that quotient, the equivalent statement is that its
value lies in !I[*].

There is also a direct construction on actual RV classes: descend
Etilde_b to epsilon_b:A -> Rbar and define

    E_mu_db = epsilon_b composed with u : B -> Rbar.           (6)

It restricts to forgetting the RES form followed by q_RES. On a
bounded Gamma product factor it is chi_b(U) tau^m; chi_b=chi_g on
bounded sets, exactly the bounded retraction formula in Section 4.
Equation (3) proves E_mu_db(J)=0 without assuming that q is injective.
For the lift (4), the computation is simply

    chi((0,gamma]) tau + q_RES([{t_gamma}]_1-[{1}]_1)=0.

The subsequent forgetting of the grading gives E^diamond on B/J.
This settles the compatibility of P_Gamma with that RES retraction;
it does not certify every later comparison or application in the paper.

## Keep the correct pullback ideal in the bounded tensor presentation

Let K_mu_db=ker(q), and let I_ann be the ideal in T_mu_db generated by
the canonical lifts (4). Surjectivity of the bounded product normal
form gives the general algebraic identity

    q^(-1)(J)=K_mu_db+I_ann,
    B/J is isomorphic to T_mu_db/(K_mu_db+I_ann).              (7)

For completeness, lift the coefficients of any finite expression
sum b_i P_(gamma_i) using surjectivity. Subtracting the corresponding
sum of coefficient lifts times ptilde_(gamma_i) leaves an element of
K_mu_db. This proves (7) without cancellation assumptions on positive
semirings; the present statement is about rings.

One must not replace the sum in (7) by I_ann alone. A concrete
counterexample over S=C((t)) is already supplied by the finite root
set R={r:r^5=rv(t)}, delta=1/5. Put

    U=(0,delta], V=(delta,2delta],
    k_mu=[(R,0)]_0 tensor
              ([(U,-id)]_1-[(V,-id)]_1).                    (8)

Both Gamma factors are bounded and have identically zero combined
weight. The RV bijection (r,w) |-> (r,rw) is measured with these
forms, so k_mu belongs to K_mu_db.

But k_mu is not in I_ann. Apply f and then the original balanced
endpoint detector T -> Z[epsilon]/(epsilon^2): it sends a finite
degree-zero RES coefficient to cardinality, positive RES degrees to
zero, and a unary Gamma set to nu(U)*epsilon. The odd integer-periodic
endpoint function A is 1 at 1/5+Z, -1 at -1/5+Z, and 0 on the other
cosets. Its interval invariant gives

    nu(U)=A(0)-A(delta)=-1,
    nu(V)=A(delta)-A(2delta)=1.

Consequently the detector sends f(k_mu) to -10 epsilon, which is
nonzero. In contrast f(I_ann)=0 by (4), so this detector kills I_ann.
This proves K_mu_db is not contained in I_ann. It uses the same
previously specified tensor detector, not a new HK premise.

This non-absorption is different from (2) and (5), which hold. The
extra bounded tensor kernel must be retained in a tensor quotient
presentation; it is annihilated by the RES evaluation, so it causes
no failure of the retraction descent checked here.

## Formalization and review status

The choice to retain positive-dimensional coefficients is also necessary
for this very pullback test. Take the RES[1] curve X of
`TENSOR-KERNEL-FINITE-COEFFICIENTS.md`, with label x and form zero, so its
combined weight is zero. Replace R in (8) by this measured X, keeping
U=(0,delta], V=(delta,2delta] and the forms -id. Multiplication by
c(x,y)=y gives a bounded measured bijection, so the resulting k_X lies
in ker(q), hence in q^(-1)(J). Under f and the genus-component detector,

    Phi(f(k_X))=eta*(-1-1)*epsilon=-2 eta epsilon != 0.

That detector annihilates the unmeasured finite-coefficient ideal J_fin.
Thus f(q^(-1)(J)) is not contained in J_fin, whereas it is contained
in the full all-X kernel K by (2). Checking only the canonical lifts
of P_gamma would miss this ambiguity: those lifts map to zero under f,
but the full pullback includes the bounded measured tensor kernel.

The tail bijections, pullback argument, and explicit annular lift have
been checked at the mathematical level. The bounded tensor rings,
their normal forms and the complete Euler descent have not yet been
exported as the corresponding concrete Lean theorem. The full kernel
presentation is unnecessary for proving (2), which follows directly
from the commuting diagram and (3). No HK comparison is assumed,
no new ground parameter is named in the actual maps, and no working
manuscript or Lean source has been modified. This remains part of the
same T001 mathematical review.


## Checked annular portion — 2026-11-12

The 873-module integrated audit now includes the actual original-ground
multiplier and tail maps, the positive tail partition and absorption,
the full unbounded Gamma/RV annulus vanishing, the positive/ring measured
RV forgetful maps, and vanishing of the actual annular expressions with
definable singleton terms. `GammaGroundAnnularPullback` proves the full
ideal pullback inclusion into the actual unmeasured tensor kernel for
every commuting presentation. The presentation maps and commutation
proof remain explicit arguments: the concrete bounded section 4 categories
and their comparison maps have not yet been instantiated. No Euler
construction or nonzero endpoint detector is certified by these exports.


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
