# Intended coefficient maps: monicity and later dependencies

2026-11-12. This note supersedes the open-ended mathematical status in
`COEFFICIENT-MAP-SCOPE-AUDIT.md`. The intended Gamma category requires full
RV-preimage witnesses. The withdrawn arbitrary-subset reading is irrelevant.
The author approved adding this proof and its citation on November 12; C002 is now incorporated in black in the annotated manuscript.

## Result and formalization boundary

There is a mathematical proof that the unmeasured **positive** coefficient
map K_+ Gamma[n] -> K_+ RV[n] is injective in ACVF(0,0), for the paper's
VF/RV/Gamma parameter convention. It uses residue-generic fibres and the
birational classification of diagonalizable group representations in
Reichstein--Youssin, *A birational invariant for algebraic group actions*,
Theorem 7.1 together with Corollary 2.5, published in *Pacific Journal of Mathematics* **204** (2002), no. 1, 223–246, DOI 10.2140/pjm.2002.204.223 (journal pp. 229, 238–239):
https://arxiv.org/pdf/math/0007181

The author explicitly approved this proof and its cited dependency.
`ReichsteinYoussinInput.lean` records exactly the faithful diagonal-action
classification as a replaceable input; it contains no ACVF extraction or
parameter-descent hypothesis. The pure-field rationality and equivariance
bridges are now checked locally. Original-ground RV graph invariance is now checked as well, using every
full Gamma-code preimage. Generic-fibre matching and its uniform finite
gluing are still in progress, so the general
monomorphism is **not yet a completed local Lean result**. The existing degree-zero and
singleton-domain reflection results retain their previous checked status.
No HK theorem is assumed. No claim about injectivity after groupification
is inferred from positive injectivity.

The relevant consequence of the external theorem is precise: faithful
diagonalizable actions on two n-dimensional tori which are equivariantly
birational admit an equivariant *monomial torus isomorphism*. It does not
say that the original birational map is monomial or extends everywhere.

## 1. Extract the Gamma bijection from residue generics

Let F:I-sharp -> J-sharp be an original-ground definable RV bijection,
with the finite disjoint-union tags retained. For each alpha in I, its
full fibre T_alpha is a torsor for (k^*)^n. After choosing coordinates
solely for the proof, its induced structure is that of a constructible
torus over the algebraically closed residue field. It has a unique
residue-generic type, of dimension n and degree one.

The map val o F on T_alpha has finite image, by residue/Gamma
orthogonality. Exactly one output value and tag beta receives the
generic part of this fibre; write h(alpha)=beta. The image of that part
is constructible of dimension n, since F is injective, and is therefore
generic in T_beta. Applying the same argument to F inverse shows that
the generic part of T_beta returns to T_alpha. This proves h is bijective.

The relation selecting the full-residue-dimension part is definable in
families, so h is definable over the original ground S. Finite union
tags are included in that relation. This construction does not claim
that F itself contracts: its exceptional subsets can change value.

In characteristic zero, the restriction between these generic parts is
a birational isomorphism of the two residue tori: definable maps in ACF
are rational on dense constructible opens, and F inverse gives the
rational inverse.

## 2. Keep all original-ground obstructions in the character group

Put Delta=val(RV intersect dcl(S)), an additive subgroup of Gamma.
For beta=h(alpha), form the finitely generated abelian group

    L=(Delta + sum_i Z alpha_i + sum_i Z beta_i)/Delta.

Let D be the diagonalizable algebraic group over k with character group
L. Its two n-dimensional diagonal representations have weights
the classes of alpha_i and beta_i, respectively.

These actions encode actual same-ground RV symmetries, rather than
discarding ramification by enlarging the ground. For a character
chi:L -> k^*, divisibility of k^* extends it to Gamma/Delta. The twist

    u |-> chi(val(u)) u

fixes k, all Gamma values, and every old-ground RV point. It preserves
RV multiplication, order-of-value relations and residue addition (all
terms of a residue sum have the same value). Relative RV quantifier
elimination therefore makes it elementary over the VF/RV/Gamma ground.
In particular it preserves the graph of F.

Choose representatives a_i in alpha_i-sharp and b_j in beta_j-sharp
only to normalize the two fibres to residue tori. The induced birational
map g satisfies

    g(chi(alpha_1)z_1,...,chi(alpha_n)z_n)
      = (chi(beta_1)g_1(z),...,chi(beta_n)g_n(z)).

This is D-equivariance. The two actions have the same kernel, by g and
its inverse. Their joint kernel is trivial because all the displayed
weights generate L. Thus both representations are faithful. This checks
the faithfulness hypothesis of Reichstein--Youssin; it must not be
silently assumed from dimension or nontriviality of the value group.

## 3. Replace the generic match by a full-fibre match

Theorem 7.1 and Corollary 2.5 give M in GL_n(Z) with

    beta_i - sum_j M_ij alpha_j in Delta.

For each of these differences choose c_i in RV intersect dcl(S).
Such points exist by the definition of Delta; no root or new parameter
is added to S. The monomial formula

    H(u)_i = c_i product_j u_j^(M_ij)

is an S-definable bijection of the **full** fibres T_alpha -> T_beta.
The inverse integer matrix gives its inverse. This is an alternative
to F, not an extension claim for its generic rational restriction.

The possible formulas M and old-ground definable c give a definable
cover of the graph of h. Compactness supplies finitely many formulas
covering its domain; refine them to a disjoint definable partition.
On each piece the associated monomial map carries the full RV
preimage onto the full preimage of its h-image. Since h is bijective,
these maps glue to an S-definable bijection H:I-sharp -> J-sharp
contracting to h. Hence h is a Gamma-category isomorphism. Positive
Grothendieck equality is actual isomorphism, so this proves the desired
positive injection. Degree zero is the elementary finite-tag case.

The upper horizontal finite-Gamma-to-RES injection then follows from
the commuting square and the already checked two vertical positive
injections. This argument concerns the unmeasured positive square only.

## 4. What the later manuscript actually needs

| Passage | Actual requirement | Horizontal monicity needed? |
| --- | --- | --- |
| The square and construction of Psi immediately before 3.18 | Four homomorphisms, their commuting square, and the balanced tensor universal property | No |
| Corrected positive Proposition 3.18, both forms | Surjectivity and the exact elementary kernel congruences; its zero-rank step uses the separately checked RES-to-RV vertical injection | No |
| VF-to-RV integral theorem at the end of section 3 | Its own VF lifting/kernel theorems | No |
| Section 4, without forms, formula (kill:gamma) and E_g,E_b | A balanced evaluation respecting the corrected tensor kernel | No |
| Section 4, measured lambda/psi and retractions | Preservation of complete combined weights on elementary translated pairs | No |
| Section 4, doubly bounded tensor comparison and P_Gamma | The bounded quotient presentation, descent of the evaluation, and its vanishing on actual annular generators | No |
| Section 5, comparison with cross-section retractions | Equality of descended evaluations on product generators; kernel descent handles presentation choices | No |
| Sections 6--7, covariant bijections, blowups and bounded VF integral | The VF/RV kernel and bounded retraction, not identification of Gamma as a subsemiring of RV | No |
| Section 8, motivic and piecewise retractions | The bounded presentation and separate descent/representative-independence checks for h_m | No |

For example, the unmeasured kernel pair evaluates on its two sides as

    q(X) chi(U) [G_m]^m,
    q(X) chi(U+delta e_i) [G_m]^m.

These agree because either Gamma Euler characteristic is translation
invariant, including for definable delta without an old-ground RV point.
Finite-coefficient balancing is exactly why the target includes !I.
For measured pairs the translated weight is adjusted so that the entire
combined weight is transported unchanged. Its Euler-fibre evaluation
therefore agrees too. Forgetting forms in the doubly bounded case leaves
the same underlying translation-invariant Euler computation.

The section 4 occurrences of Psi inverse and the asserted bounded
isomorphism still need the already-required quotient formulation after
the correction of 3.18. They do not follow from coefficient monicity.
Likewise the section 8 lattice-counting h_m formulas need their own
descent checks: the Euler check above does not automatically certify
them. These are dependencies of the tensor correction, not reasons to
assume horizontal injectivity.

The actual checked positive descent API requires agreement on elementary
pairs, and no injectivity premise:

* `PositiveTensorDescent.gammaGroundUnmeasuredTensor_descends_iff`;
* `PositiveTensorDescent.gammaGroundMeasuredTensor_descends_iff`;
* `BalancedTranslationDescent.gammaGroundBalancedEvaluationOnRV`.

`GammaGroundAnnularPullback.gammaGroundAnnularPullback_le_actual_tensor_kernel`
needs the commuting presentation square and vanishing of the annular
generators, not injectivity of either presentation or a section of it.
The concrete bounded section 4 maps are still outside the checked scope.

## Review consequence

The earlier C002 proposal was to omit an assertion whose local proof was
missing. It was never evidence that monicity was false. The present
mathematical proof is a reason not to describe the assertion as an error.
The author approved retaining it with the proof. C002 and the published
citation are incorporated in the manuscript, with a green resolution and
no corresponding referee item to gray. The resolved PDF is
`reference/proposed-revisions/C002-resolved-review.pdf`. Its PDF-only
right-panel display request returned queued; visibility was not confirmed.
The manuscript source SHA is
`080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97`.

The compiled transitive dependency check for seven existing roots passes;
see `coefficient-dependencies.json` and `coefficient-dependencies.log`.
It confirms that horizontal coefficient injectivity is not used, while
the existing vertical RES-to-RV injection is used.


## Forward-map dependency clarification

In response to the author's question about [19]: the lower horizontal
semiring map is checked locally from the intended full-preimage definition.
`gammaGroundGammaHom_lift_iso` takes the bijective RV witness already
required of a Gamma morphism; the scissors, unit and product checks then
construct `gammaGroundGammaToRVSemiring`. No `YinGammaAffineInput`,
piecewise-GL classification, [19] or HK premise occurs in these theorem
types. The separate [19] input concerns Remark 3.15's classification at
its stated VF-generated real-base scope, not well-definedness of this
forward map.


## Uniform generic selectors now under construction

The local checked modules now include `rvInfiniteLast_definableOverBase`
and arbitrary finite iteration of `rvGenericCoordinate`, over the complete
original Gamma ground. Uniform finite/cofinite bounds range over every
Gamma code before specializing the original finite support. Coordinate
selection respects its entire value class and preserves other established
coordinate invariances. Thus `rvFullFibreGeneric` is definable and invariant
on full nonzero RV fibres, including the empty tuple case.

`rvGenericCoordinate_at_residue_generic` identifies the selector with
membership of an actual algebraically independent residue tuple. A common
countable algebraically closed coefficient field for finitely many
intermediate selectors is constructed inside the residue field; genuine
saturation supplies a simultaneous test tuple. The generic matching and
its bijectivity still need to be connected to actual RV object isomorphisms,
then combined with diagonal weight classification and finite gluing.
These new modules postdate the 904-module integrated receipt and require
an updated full audit.


### Uniform generic selector and finite partitions

The local generic-selector bridge now proves uniform definability over the
complete original Gamma ground, full value-fibre invariance, and agreement
with membership at an actual independent residue tuple. Finite families of
all intermediate selectors have one countable algebraically closed residue
coefficient field; saturation supplies a simultaneous test tuple.
`rvFullFibreGeneric_partition` then proves exactly one generic part in any
finite definable partition of a full RV fibre. These are explicit actual
RV sets and full value-code relations, not additional geometric inputs.

The general horizontal monomorphism is still unfinished in Lean: the next
step matches an actual RV bijection and its inverse using these selectors,
then uses the proved character symmetries and the approved diagonal-action
classification to obtain old-ground full-fibre monomial maps and glue them.
The previous 904-module audit is superseded only when the new integrated
receipt completes. The mathematical C002 proof and PDF remain adopted.


### Integrated generic-selector audit

The complete 921-supporting-module checkpoint passes (11,406 Lake jobs):
2,725 theorem types, 2,207 printed definitions, 158 named instances and
eight reused declarations; 5,098 declarations audited in total. Only
`propext`, `Classical.choice` and `Quot.sound` occur. The integrated receipt
includes every generic-selector, common-coefficient, simultaneous-test-point
and finite-partition theorem described above. It still does not certify
all-degree horizontal monicity. The approved C002 manuscript SHA is unchanged.


The next local bridge is now connected to actual maps: the full value
graph of an RV map, retaining every output value representative, produces
an original-ground definable Gamma relation via the generic selector.
`rvNormalizedMapRelation_pure` extracts the pure-field graph from the
actual original-ground map. Its forward and inverse functionality are
proved, and characters of an injectively embedded weight group extend to
the original value quotient and preserve that actual normalized graph.
These additions postdate the 921-module receipt. Functionality and
bijectivity of the resulting Gamma relation for full RV-preimage
bijections, followed by finite gluing of the classified monomials, remain
unfinished; no general monicity theorem has been reported complete.


### Actual generic contraction and original-ground weights

`gammaGroundRVGeneric_contraction` now constructs the actual interpreted
Gamma map for a map from full RV preimages, retaining the complete original
real/Gamma ground and its actual target. Scalar generic values are unique,
and finite coordinate assembly includes the empty tuple case.
`gammaGroundRVGeneric_inverse_at` proves the inverse identity using one
locally constructed countable algebraically closed residue coefficient
field for the forward graph and all intermediate source/inverse selectors.
`gammaGroundRVBijection_generic_bijection` therefore supplies a genuine
interpreted Gamma bijection from a bijection of single full preimages.
These extraction and inverse results use no R--Y classification input.

`gammaGroundRVGeneric_original_coefficients` then applies the precise
approved R--Y input to the actual generic graph. Its conclusion has a
unimodular integer matrix and actual original-ground definable RV
coefficients at each Gamma point, with the weight group constructed from
the exact quotient by definable RV values. The interpreted generic
bijection has not yet been given a globally bijective full RV lift.
Finite formula selection/gluing, finite tagged families and general
positive horizontal monicity remain unfinished. All additions in this
entry postdate the 921-module integrated receipt.


### Integrated actual generic-bijection checkpoint

The 953-supporting-module checkpoint passes the complete project build
(11,438 Lake jobs) and audit: 2,777 public theorem types, 2,230 printed
definitions, 158 named instances and eight reused declarations, totaling
5,173 audited declarations. Only `propext`, `Classical.choice` and
`Quot.sound` occur. The receipt now includes the actual generic Gamma
bijection for single full RV preimages, original-ground pointwise
unimodular coefficients, finite map gluing, ordered cover refinement and
definable monomial agreement predicates. The original C002 manuscript
SHA is unchanged. General positive horizontal monicity remains unfinished;
finite formula extraction/gluing to a full RV bijection and finite
tagged families are the next obligations.


### Single-piece full lift and positive reflection

`gammaGroundAffine_partition_full_lift` now glues the finite old-ground
unimodular formulas into an actual bijection on the entire RV preimages.
It contracts pointwise to the interpreted Gamma bijection, including
arity zero and empty pieces. Injectivity uses the unimodular inverse;
surjectivity solves on each full value fibre.
`gammaGroundGammaSingle_reflects_RV_bijection` and
`gammaGroundGammaSemiringClass_single_eq_of_RV_bijection` therefore prove
actual Gamma-category isomorphism and equality already in the positive
semiring for single Gamma pieces. Their only new cited premise is the
approved R--Y classification. No cancellation or group completion is used.
Finite tagged family reflection remains unfinished, so this is not yet
general horizontal semiring injectivity. These additions postdate the
953-module integrated receipt.


### C002: general positive monicity proved locally

`gammaGroundUnitFamily_generic_bijection` constructs a genuine interpreted
Gamma-family bijection from an actual full RV family bijection, retaining
every finite tag. Its inverse compatibility is proved using one locally
constructed residue coefficient field for the actual partial branch graph
and both generic selectors. This extraction uses no R--Y input.
`gammaGroundUnitFamily_generic_original_coefficients` then applies only
the approved diagonal classification to obtain actual original-ground
RV coefficients and unimodular matrices at every Gamma point.

`gammaGroundUnitFamily_affine_full_lift` uses compactness and genuine
source/target branch partitions to construct a full bijective RV family
lift. Unit/code transport retains all representatives. Consequently
`gammaGroundGamma_reflects_RV_lift_bijection` proves actual Gamma-category
isomorphism reflection, and `gammaGroundGammaToRVKPlus_injective` proves
positive homogeneous injectivity. The checked direct-sum grading gives
`gammaGroundGammaToRVSemiring_injective`; the commuting square gives
`gammaGroundFiniteGammaToRESSemiring_injective`. Fixed-degree finite-Gamma
to RES injectivity is also proved. No cancellation or group completion
is used, and no groupified injectivity is inferred.

The only additional cited input is the precise approved R--Y consequence.
No HK result and no [19] classification input is used for well-definedness
or for this local ACVF proof. These additions postdate the 953-module
integrated receipt; the next complete audit is pending.


### Integrated C002 monicity checkpoint

The complete 977-supporting-module build passes (11,462 Lake jobs). The
full audit checks 2,815 public theorem types, 2,245 printed definitions,
158 named instances and eight reused declarations: 5,226 declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Both ordinary
horizontal positive coefficient monomorphisms are now included in the
integrated receipt, in each homogeneous degree and on the graded
semirings, with the actual GammaGroundContext wrappers. The approved
C002 manuscript SHA remains unchanged. This closes the local C002
monicity obligation, including finite tags and full original-ground
RV lifts, relative only to the expressly approved R--Y classification.
It does not certify the whole section or any groupified injectivity.
The next scope check concerns the broader-ground affine classification.


### Full-ground Gamma piecewise-GL classification

`gammaGroundGammaHom_iff_piecewiseGLZ` now proves both directions of
Remark 3.15's morphism criterion over the complete original mixed ground,
with finite source/target tags and actual definable RV translations. The
forward direction applies the proved generic coefficient construction to
the given morphism's own full code witness. The reverse direction glues
full RV bijections and uses no classification input.
`gammaGroundContext_GammaHom_iff_piecewiseGLZ` instantiates the actual
VF/Gamma-generated context; this is a local proof relative to the already
approved R--Y input, rather than a broader-base use of [19]. The separate
unary, potentially nonbijective contraction statement is still being
worked on; the accepted [19] record is retained at its stated real-base
scope. Well-definedness of the lower coefficient arrow remains the
independent direct proof from the full-preimage definition.

The full 982-supporting-module checkpoint passes (11,467 Lake jobs):
2,824 theorem types, 2,246 printed definitions, 158 named instances and
eight reused declarations, totaling 5,236 audited declarations. Only the
standard logical principles occur. No manuscript edit, commit or push
was made for this extension.


### Full-ground unary contraction classification

`gammaGroundUnary_code_contraction_piecewiseIntegralAffine` proves the
first sentence of Remark 3.15 for an actual map on full RV code preimages,
without assuming the RV map or its Gamma contraction is bijective. Its
finite partition has integer slopes and genuine original-ground definable
RV shifts. The proof stabilizes the RV map by `(u,v) -> (u,f(u)v)`,
classifies this genuine Gamma morphism in degree two and restricts its
finite affine formulas to the identity slice. All product, descent and
restriction graphs retain the original mixed base.

`gammaGroundContext_unary_contraction_piecewiseIntegralAffine` supplies
the actual VF/Gamma-generated context. Together with
`gammaGroundContext_GammaHom_iff_piecewiseGLZ`, both statements of Remark
3.15 have local full-ground proofs relative to the already approved
R--Y classification. No [19] statement is silently extended beyond its
stated base. The older precise [19] record is retained for reuse.
These changes postdate the 982-module audit and await the next full
integrated check. The manuscript remains unchanged.


## Final tuple classification and completion check — 2026-11-12

`gammaGround_code_contraction_piecewiseIntegralAffine` proves the first
sentence of Remark 3.15 for arbitrary actual full-code contractions from
Gamma^n to Gamma^m, including nonbijective maps and zero arities. Its finite
partition has rectangular integer matrices and genuine original-ground
definable RV shifts. The proof stabilizes to the full RV shear in degree
n+m, applies the checked full-ground morphism classification, and restricts
to the identity slice. The context wrapper retains the actual manuscript
VF/Gamma-generated ground. Only the already approved R--Y classification
is used as an additional cited input; [19] is not broadened.

The full project build and principle audit pass (11,483 Lake jobs), across
998 supporting modules plus Section: 2,843 theorem types, 2,254 definitions,
158 named instances and eight reused declarations, totaling 5,263. Only
`propext`, `Classical.choice` and `Quot.sound` occur. The verified semantic
coverage record links 21 manuscript targets to 115 actual declarations.
This completes the documented §3 paper contexts relative to the explicitly
accepted later [18] inputs and approved R--Y theorem, with no HK input.
Independent disc-name extensions and concrete §4 constructions are outside
this certificate. No groupified monicity is inferred from positive monicity.

Well-definedness of the lower coefficient map remains the separate direct
proof from full RV lift witnesses, with local scissors and product descent;
it needs neither [19] nor R--Y. The approved manuscript is unchanged
(SHA256 080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97).
No commit or push has been made.
