**Current status:** the intended full-preimage convention is fixed; C001 is withdrawn. A mathematical positive-monicity proof using Reichstein--Youssin is now recorded in `COEFFICIENT-MONICITY-CHECK.md`. The general local Lean proof remains unfinished. The earlier discussion below is preserved as history.

# C001/C002: well-definedness precedes injectivity

2026-11-12. Follow-up to the author's question about the lower horizontal
arrow and Remark 2.28 / Lemma 2.29 of *Integration in algebraically closed
valued fields with sections*.

## What the checked Lean statements actually say

Both `GammaHom` and `GammaGroundGammaHom` require a bijection on the full
nonzero RV code families that contracts to the given Gamma bijection.
For that definition, the lower horizontal semiring homomorphism is already
checked: `gammaGroundGammaHom_lift_iso` transports the full code bijection
to an actual RV isomorphism; `gammaGroundGammaToRVKPlus` checks scissors;
`gammaGroundGammaToRVSemiring` additionally checks the unit and products.
No piecewise GL classification, tensor injectivity or HK premise enters
this forward construction.

This was a mathematical interpretation of Definition 3.13, not a proved
comparison with a definition allowing a bijection between arbitrary RV
subsets. The previous completion reports did not flag that distinction
adequately. The original manuscript says only that the Gamma bijection
is the vrv-contraction of a definable bijection; its general contraction
definition does not require full value preimages. The two readings must
not be silently identified.

## Failure under the arbitrary-subset reading

Work over S = C((t)), v(t)=1, in ACVF(0,0); this ground is nontrivially
valued as required. Write a=rv(t), alpha=1/5 and beta=2/5, additively.
The two S-definable finite RV sets

    R = {u : u^5=a},       R' = {v : v^5=a^2}

are bijective by u |-> u^2. Its inverse is v |-> v^3/a, as follows
immediately from the two fifth-power equations. The induced Gamma map
{alpha} -> {beta} is a bijection and the contraction of this actual
same-ground RV bijection. Thus it is a morphism under the arbitrary-subset
reading, even though its RV witnesses are finite, rather than the full
one-dimensional value fibres.

The full fibres alpha-sharp and beta-sharp are not S-definably bijective.
Here is a proof that distinguishes their RV classes, not merely absence
of definable points in both fibres.

Choose r with r^5=a only for the proof, and let zeta be a primitive fifth
root of unity in C. A hypothetical S-definable bijection F of the full
fibres induces

    g(z)=F(r z)/r^2 : k^* -> k^*.

The induced residue-field structure is ACF(0), so g and its inverse are
rational on cofinite open sets. Hence their generic rational maps are
inverse and g is a Mobius transformation. The ground automorphism
r |-> zeta r, fixing the residue field, forces

    g(zeta z)=zeta^2 g(z).

For a completely concrete model one may work in the Puiseux algebraic
closure of C((t)); its residue field is C and this ramification
automorphism fixes it pointwise. A putative defining formula for F in a
saturated extension transfers to that ACVF submodel.

The displayed functional equation says that the Mobius transformation
conjugates multiplication by zeta to multiplication by zeta^2. Both have
fixed-point set {0,infinity}; consequently g permutes that set and is
c z or c/z. Equivariance would then require zeta^2=zeta or zeta^2=zeta^-1,
both impossible for a primitive fifth root. This proves the claimed
nonexistence of F.

Positive RV class equality is exactly definable bijection (also checked
locally in `gammaGroundRVClass_eq_iff_iso`), so sending a Gamma object to
its full RV preimage does not descend even to positive classes under the
arbitrary-subset reading. The finite-Gamma-to-RES arrow has the same issue.
This is a mathematical counterexample, not a newly compiled Lean
construction of this particular valued-field model and its curve maps.

## What Lemma 2.29 does and does not provide

Source: https://arxiv.org/pdf/1204.5979v2, Convention 2.9 on printed p.4,
Definition 2.27 / Remark 2.28 / Lemma 2.29 on printed pp.7-8.

Lemma 2.29 is an abstract statement about a class O of functions on a
torsion-free module. It assumes piecewise integral-affine descriptions
and closure under inversion, composition, GL transformations and the
specified projections. These hypotheses must be established for the
particular contraction class; the lemma itself does not establish them.
The current ground also requires that translation constants have
same-ground definable RV representatives if they are to lift.

In particular, O cannot simply be all contractions of arbitrary RV
functions: RV squaring contracts to Gamma doubling. Doubling is a
bijection of Gamma, but its inverse halving has no definable full-input
RV lift in the pure L_RV theory. To see this, enlarge to a model base,
take an RV point with value gamma outside its divisible ground value
group, and use RV definable-closure values Gamma(base)+Z gamma; gamma/2
is not in that group. Thus the asserted closure under inversion is a
substantive condition. If one uses a cross-section to lift halving, the
lift is in the expanded language, where piecewise Z-affinity of all
contractions no longer holds. This observation does not refute the
abstract Lemma 2.29.

Even a valid piecewise GL theorem for Gamma morphisms proves the forward
map only: if h(gamma)=A gamma+delta with A in GL_n(Z) and rv-value(c)=delta,
then H(u)_i=c_i prod_j u_j^(A_ij) is a bijection of the full RV preimages.
Finite disjoint partitions glue these maps, preserving all tags.
This provides well-definedness when the hypotheses and the liftability
of constants hold. It does not imply that an arbitrary RV bijection
between two full preimages can be replaced by a contracting one.

## Injectivity after making the full-preimage condition explicit

For the full-preimage category, injectivity requires

    I-sharp isomorphic to J-sharp in RV[n]
       ==> I isomorphic to J in Gamma[n].

The forward construction above and Lemma 2.29 do not supply this
reflection statement. It remains open in the local formalization; no
counterexample to it is asserted here. Degree zero and singleton Gamma
domains in every arity are checked. The corrected Proposition 3.18 uses
homomorphisms of coefficient semirings, not monomorphisms, so its positive
quotient proof does not require horizontal injectivity. Its current Lean
proof remains a proof for the explicitly full-code Gamma category.

C001 proposes making that full-preimage condition explicit in Definition
3.13. C002 proposes omitting the unsupported horizontal monomorphism
assertion, retaining the checked two vertical monomorphisms. Both are
review proposals only; the approved working manuscript and Lean category
definitions are unchanged. The piecewise GL characterization at the
complete mixed ground has not been proved by this scope audit.


## Author clarification: intended Gamma morphisms — 2026-11-12

The author confirms the intended Gamma-morphism convention: the witnessing
bijection is on the full RV preimages. The arbitrary-RV-subset alternative
was introduced by the assistant and is not the category under discussion.
C001's proposed definition correction is withdrawn. Its mathematical
counterexample concerns that alternative only and provides no evidence
against monicity of the intended lower horizontal map. For the intended
category, well-definedness is checked; general horizontal injectivity
remains unresolved. C002's provisional omission of the assertion has not
been approved, and the main manuscript remains unchanged. The existing
C001/C002 PDF is retained as history and includes a withdrawn item.
