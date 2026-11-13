# Review of the checked types

The complete entry-point build and `verify.py` passed on Lean 4.35.0.
The receipt records exact source hashes and the approved dependency patch.
The audit prints all actual types and definitions with notation disabled.
The current complete audit covers 5,324 declarations: 2,866 supporting
theorem types, 2,280 definitions, 170 named instances and eight reused
declarations, across 1,003 supporting modules plus Section. It validates
119 actual declaration links for 21 manuscript targets.
Only `propext`, `Classical.choice` and `Quot.sound` occur. This is a local
verification, not a CI result.

The actual printed theorem types were reviewed with particular attention to:

- `IsDefinablePoint.map` uses a genuinely singleton-definable input and a
  complete definable function graph, at exactly the same parameter set.
  Its inverse direction uses the checked definable inverse. The R053
  obstruction theorem still has two explicit point-existence/nonexistence
  premises; it does not claim a particular model has been constructed.
- `RVObject` retains arbitrary finite domain arity and the unique RV zero
  there, while the finite-to-one target map has a separate nonzero field.
  The degree-zero theorem quantifies over an actual object and proves
  finiteness of its complete domain. No nonempty-domain premise is hidden.
- `VFObject` uses the actual §2 interior dimension and literal finite
  fibres. Its topology parameter is visible. `objectLiftVF` proves the
  ambient dimension bound and finite-fibre condition; it is only an
  object construction and does not contain a class-descent claim.
- `RVVolumeForm.graph_spec` identifies every graph fibre over the actual
  Gamma value with the full graph of its function on RV tuples. No
  representative of that Gamma value is added as a real parameter.
- `measuredRV_equation_iff` has the source/target ratio in the same order
  as §2's Jacobian definition: omega equals sigma times target weight
  divided by source weight. Both the statement and the preservation field
  quantify over **every** point. The measured groupoid's inverse and
  composition use this pointwise equality.
- The three printed groupoid instances use the actual definable-bijection
  and measured-bijection morphisms. Their laws are compiled, rather than
  assumed as mathematical input fields.
- The positive scissor relations keep the chosen finite-to-one target
  on each RV piece and the original mixed ambient coordinates on each VF
  piece. Nothing in their types supplies a graded multiplication or a
  tensor decomposition.
- `integralFromKernel_characterization` and its uniqueness theorem retain
  both surjectivity of L and **equality of the whole congruence** with
  `AddCon.ker L`. A relation that merely vanishes under L would not suffice.
  These types are the algebraic consequence of a future geometric kernel
  theorem, not a replacement for it.
- `abs_not_affine` assumes a positive element in an ordered abelian group;
  it rules out a translated additive homomorphism. It checks the algebraic
  part of R050 and does not assert that an absolute-value map is bijective.

The entries below preserve the historical type-review milestones. The
current completion review in `paper-targets.json` supersedes their open-item
notes, with the documented ground contexts and accepted cited inputs
explicit. Numerical audit coverage alone is not a semantic certificate.

Additional full-type review after the latest implementation:

- The RV fibre maximum is measured over S together with precisely the
  original VF tuple. Its invariance theorem discharges the exchange input;
  the full imaginary-base scope is not claimed.
- The full VF dimension comparison requires an actual compatible valuation,
  small real base and genuine saturation. Nonemptiness is required only
  for the equality to a natural number; upper-bound and exceptional-set
  comparisons handle empty sets and degree zero separately.
- The essential VF groupoid uses actual Jacobians on co-small definable
  representatives. Its agreement relation is compared to §2 dimension.
  The degree-zero homs preserve the Gamma form at every point.
- Gamma-family homs require a same-base definable bijection on the full RV
  code families. The finite tags and every imaginary representative remain.
- `rebaseSpace` changes only definability proofs along equality of language
  structures; the carrier, codes and decoder are literally the original
  data. `gammaRelation_definable` uses the full invariant graph. The
  measured lift is the genuine pullback along its original RV labels.
- `completedCongruenceEquiv` quantifies over an arbitrary relation on a
  commutative semiring and identifies its generated congruence completion
  with the ideal of all generator differences. The unmeasured pair uses
  b+1, whereas the measured pair uses b. No injectivity of completion is
  assumed. Neither result supplies an ACVF kernel theorem.
- `RVPositiveSemiring` is the universal semiring quotient on genuine
  products, same-degree definable bijections and scissors, with every
  degree's empty class killed. Comparison to the fixed-degree direct sum
  and the full geometric interpretation remain explicit obligations.

The RV universal positive semiring is now proved equivalent to the actual
direct sum of the fixed-degree positive quotients. RES has actual coproduct
representatives and an injective graded semiring map into RV. The Gamma
code lift retains all codes and explicit finite tags; its fixed-degree
scissor descent and finite-Gamma commutative square are proved. These
statements do not assert Gamma embedding or tensor isomorphism. The actual
unmeasured special generators are defined, and their completed congruence
is identified with the principal ideal generated by P−1. Neither geometric
HK kernel is inferred from this algebraic fact.

The expanded audit includes the concrete VF, Gamma, finite Gamma and
measured semiring presentations and the actual measured Gamma-to-RV arrow
lifts. It also includes the replaceable cited-input records and their
relative integral consequences. These input records are intentionally
uninhabited by local global declarations: every consequence takes its
specific record explicitly. Their source statements and stricter current
base specialization are documented in cited-inputs.json. A clean principle
audit of a function of a cited input does not independently verify that input.

The expanded multiplicative comparison has also been checked at its actual types:

- Measured RV positive equality is equivalent to an actual everywhere
  weight-preserving definable isomorphism. The auxiliary category of maps
  supplies coproducts; it does not replace the original groupoid.
- The measured RV and RES direct-sum equivalences use actual products,
  inherited cuts and genuine coproduct representatives. Measured RES
  injectivity is proved before group completion, without cancellation.
- Gamma product code maps retain every representative and the original
  finite tag. No model element is chosen to represent a Gamma value.
  The measured product map preserves combined weights at every point.
- Both coefficient squares commute as semiring maps. The canonical tensor
  maps use these exact coefficient maps and evaluate on actual objects as
  their cartesian product. Their types contain no bijectivity hypothesis
  or hidden HK input. Bijectivity remains an explicit open obligation.
- CompletionTensor proves the canonical ring-completion/tensor equivalence
  for arbitrary commutative semirings. It does not require or claim that
  the positive semirings embed into their completions.
- The 18 new modules in this batch disable autoImplicit, and the complete
  build and declaration audit pass.

The VF filtration comparison is now independently checked at the current
real-base scope. Its coproducts preserve the actual section 2 dimension
bound and finite RV fibres. Positive equality is exactly a definable
bijection; no cancellation or group-completion embedding is assumed. The
filtered semiring is equivalent to the companion all-finite-fibre positive
quotient. Its inclusions are injective, every class comes from an actual
bounded object, and vfPositiveIsColimit proves the categorical colimit in
AddCommMonCat with precisely the original bound-raising maps.

The measured VF direct-sum comparison explicitly requires both the accepted
global and degreewise lift records. Their compatibility is proved on actual
object lifts. The polynomial degree marker descends independently through
the actual measured special relation, proving that distinct degrees remain
independent. The resulting additive equivalence preserves the original
direct-sum addition. Multiplication is transported across it and is proved
to agree with every actual measured VF cartesian product and the unit.
The semiring structure remains visible through its explicit input-dependent
constructor in the semiring and ring equivalence types. This does not extend
the current VF-generated real-base specialization to the manuscript's full
parameter scope. The explicit local coefficient-semiring instance is printed
and audited too; it chooses the existing quotient commutative-semiring
structure for polynomial elaboration, with unchanged underlying operations.

The Gamma class comparison now uses actual definable disjoint unions, tag
permutations, full-code coproduct bijections and partition isomorphisms.
The code witnesses commute with decoding at every point. Empty pieces and
zero tags are handled explicitly rather than by a nonemptiness premise.
Positive equality is exactly a genuine Gamma isomorphism, and every positive
class has an actual representative. No HK decomposition, Gamma embedding or
cancellation input appears in these proofs. The general isomorphism-class
monoid data are instantiated by the checked Gamma coproduct maps.

The Gamma-ground extension keeps complete graphs over actual Gamma names.
Its real-code interpretation has a proved equality of the VF coefficient
field with the original field; it is not used to equate arbitrary RV
ranks. VF dimension and literal finite-RV-fibre invariance are proved.
The additive filtration colimits use actual bound-raising maps and genuine
Gamma-ground bijections. Their universal-semiring identification remains
separate. Essential Gamma-ground representatives retain actual partial
bijections and the intrinsic section 2 smallness condition. Their generic
equivalence relation has an exact same-ground agreement theorem. The
generic measured construction is compared with the manuscript's
pointwise-on-a-cofull-cut preservation condition over the Gamma ground in
`GammaGroundPointwiseVFMeasure` and `GammaGroundMeasuredVFGerms`: every
generic measure germ has an actual pointwise preserving representative on
a same-ground definable cofull subset with open VF fibres. The full
derivative determinant graph is kept distinct from the weaker pointwise
partial-Jacobian predicate. Zero determinants are included in its value
presentation. The positive-degree groupoid now uses the actual quotient
of pointwise preserving representatives; degree zero still uses genuine
form-preserving bijections.


The Gamma-ground measured grading now has the same checked polynomial
separation argument, retaining the actual fixed-degree scissors and both
accepted [18] records. Its surjectivity is proved independently by reducing
polynomial classes to finite additive sums of object generators. The
ordinary Gamma-ground universal-semiring comparison and its categorical
additive/group colimits use the accepted global and bounded lift records;
they are not unconditional geometric kernel proofs. The full finite-sorted
syntax bridge retains the proper-sort guards in every Gamma row and all
RV codes, rather than only the selected fibre.


The subsequent Gamma-ground RV class comparison uses auxiliary definable
map categories with actual coproduct universal properties. Both cut
inverses have same-ground graphs. The isomorphism-class additive monoids
therefore prove equality exactly when a genuine RV bijection exists; the
measured version retains the pointwise full combined weight. Actual object
representatives follow from the checked tagged coproduct formula. Products
of measured arrows preserve combined weights via the exact unpacked
coordinate formulas. RES finite support refers to all domain coordinates,
with the zero/one tag values explicitly included.


The subsequent ordinary and measured Gamma-ground RV grading comparisons
prove the cartesian associativity/unit/symmetry and distributivity on actual
objects and inherited cuts before constructing the graded commutative
semirings. Their universal-presentation equivalences and fixed-degree
injective inclusions have no lift or HK hypotheses. Both RES direct sums
have actual cartesian semiring products and injective positive graded
inclusions. Group gradings commute with completion; the canonical completed
coefficient maps are supplied without claiming completed injectivity.
The ordinary bounded RV inclusions are checked by extracting their finite
components from the proved direct-sum comparison. The graph normal form
retains the original full Gamma ground and actual projection coordinates.


The Gamma-ground family categories retain complete branch graphs and
explicit bijections on every full RV-code preimage. Their actual coproduct
coherence and partition maps commute with all decoders. Both ordinary and
measured positive class equality is exactly a genuine isomorphism, every
class has an actual tagged-family representative, and the finite full
subcategories have injective positive inclusions. None of these results
assumes the pending HK decomposition or coefficient monomorphisms. The
piecewise RV-code lift is an actual identity-target object with all nonzero
codes and the finite-support RES consequence; family realization and
cartesian grading remain separately tracked.


The 445-module receipt additionally checks complete Gamma-ground finite
family realization by zero/one RV tags, arbitrary-map descent, finite target
fibres, and finite whole-domain value support. Both ordinary and measured
Gamma lifts use every RV code and retain the original complete ground.
Scissors, product and unit maps are checked before taking universal
quotients. The four Gamma graded/presentation equivalences and group
completions use actual same-ground contraction witnesses. The finite
positive inclusions are injective; no completed coefficient injectivity is
inferred from this fact. Both canonical balanced tensor maps use the actual
multiplicative coefficient square, and their pure-tensor formulas are
printed. Neither tensor map is asserted bijective and no HK result is an
installed premise.

## Completed upstream checkpoint and native adapters

The 470-module receipt prints all 26 direct [18] proof exports and the
native 2.23, 2.27 and 2.28 wrappers. The Gamma-base syntax equivalence
requires proper sorted outputs for its reverse direction. Nonemptiness
and sortedness are retained when transporting local atomicity, since the
upstream atomicity predicate records the formula decision property without
these extra conjuncts. Nontrivial original Gamma ground is converted to a
positive definable value, without requiring nontriviality of the original
VF-generated real field. Open-disc images use image atomicity to exclude
whole VF; primitive-disc comparison includes the whole-field closed chart.
The [18] full consumer root and both section verification scripts pass
with the pinned five-file proof compatibility patch. Later integral/kernel
records remain accepted inputs and are not claimed supplied by this pin.

The native finite-disc equivalence is now proved in all mixed output arities.
Its reverse direction first proves invariance of the full raw Gamma-code
carrier, then constructs FiniteDiscTupleRelation. RealParameterPromotion
from the checked upstream library promotes an RV label uniformly over every
old imaginary name; 3.9 includes the zero label. For 3.4, each proposed cut
has finite real support. Applying the source theorem to that finite support
retains all old imaginaries and the ambient complete type, so the local
constructor is uniform in all enlarged real bases. Genuine saturation at an
infinite cardinal remains explicit. Native 2.25 closed/open and 2.30 real/DC
wrappers supply their original geometric arguments from these proofs.


The final 488-module receipt also prints the native mixed partition proof
and the 2.32 wrapper. The raw mixed codec is injective; its total-map default
is only used outside the declared source, and the graph equality is proved
on the complete source. Fixed input/output RV labels match exactly the
deleted-coordinate contexts of [18, Definition 3.20]. The source's
small-real-base partition theorem is applied to finite real support of the
graph and the positive definable value, keeping all imaginaries. Every
piece is then definable over the original full base.

The four zero cells form a finite disjoint cover; empty cells are permitted
by the native partition definition. The paper-open fibre iff is stable
under restriction and passes to the actual inverse by InvOn. Checked
open-ball infinitude excludes zero-only images, and nonzero images exclude
whole VF. Both native fibre-concentric conditions therefore use ordinary
finite-radius discs, even at the zero RV label. The constructor retains
actual saturation at an infinite cardinal; it does not impose a bound on
the old real base or silently replace Gamma nontriviality by VF nontriviality.


## Local proof foundations replacing the rejected HK-input proposal

The 502-module receipt checks the intrinsic mixed-fibre partition and its
unary ACVF application. The residue part includes RV zero and has finite
complete-domain value support. The other part is the complete nonzero RV
preimage of a Gamma-definable piece. No auxiliary angular representative
is made a ground parameter. Uniform finite-side selection uses first-order
counting predicates; finite union follows from the checked predecessor
GammaRVFamily.finite_projection theorem. Finite columns are partitioned by
original-base definable Gamma tests, decreasing the finite column count.
Only actual saturation and small real support are used in the compactness
steps. These local proofs introduce no HK premise and do not yet supply
higher-dimensional tensor or coefficient-injectivity theorems.


November 11, 524-module checkpoint: all 1708 public theorem types, 1680
definitions, 148 named instances and 8 selected reused declarations passed
the complete printed-type and dependency audit. The boundary relation is
defined using every nonzero RV code; its finite row is the actual intrinsic
order boundary, not a set of named representatives. Residue tuple projection
requires saturation, ACVF00 and smallness of both original real/Gamma bases.
The rectangle partition stays over the original base; finite thresholds
and temporary point witnesses do not enlarge that base. General Gamma tuple
orthogonality and the coefficient/tensor comparisons remain separate goals.


The 533-module receipt audits 1719 public theorem types, 1682 definitions,
148 named instances and 8 selected reused declarations (3557 heads). The
new tuple orthogonality proof has original-ground native Gamma/RV formulas
with full invariant code preimages. It explicitly uses saturation, ACVF00,
small real and Gamma supports, and nontrivial original-ground Gamma. Gamma
tuple point selection removes both temporary residue tuples coordinate by
coordinate. Compactness only chooses from predicates definable over the
original common real names. These rectangles do not certify the RV normal
form, Gamma-to-RV injectivity or invariance of tensor expressions.


544-module checkpoint: 1749 public theorem types, 1697 definitions,
148 named instances and 8 selected reused declarations (3602 heads).
The monomial equivalences contain two actual integral inverse matrices;
their maps are actual released-language terms on every RV input. Inverses
are asserted only on the nonzero torus. Smith normal form is the pinned
standard-library theorem, and the finite coordinate-value proof explicitly
uses torsion-free Gamma. The guarded equality split assumes its actual
flat-sum domains and retains the zero-residue cases on both branches.
This is not a certificate of the full RV normal form or Proposition 3.18.


559-module checkpoint: 1799 public theorem types, 1711 definitions,
149 named instances and 8 selected reused declarations (3667 heads).
The clause-coordinate invariance retains the actual flat-sum domains.
Finite DNF clause covers are labelled as covers; they are not silently
treated as disjoint positive-scissor decompositions. The subsequent global
value-pattern refinement is outside this receipt. The mixed quotient lemma
is an exact full-preimage equality under stated fibre invariance and does
not select representatives. No HK premise has entered the dependencies.


566-module checkpoint: 1827 public theorem types, 1725 definitions,
151 named instances and 8 selected reused declarations (3711 heads).
The global value-pattern cells are finite, cover the original DNF and are
pairwise disjoint. Their finite-character and angular-invariance proofs
operate on exact released total semantics, while pole/residue guards
remain formula literals. The common-name closure elimination repackages
the actual finite parameter witness and removes only same-value RV code
representatives; old real parameters remain in the original base. No
chosen representative is retained in its conclusion. The next adapters
and categorical product assembly are outside this receipt.


580-module checkpoint: 1869 public theorem types, 1741 definitions,
151 named instances and 8 selected reused declarations (3769 heads).
The definable angular-partition theorem uses exactly the input real base,
not common-name extensions. Its source DNF adapter preserves the original
finite parameter package, zero behavior and explicit domain certificate.
The finite pattern index has proved uniqueness, disjointness and coverage.
Each cell has a two-sided integral monomial basis and finite residue-value
support. Original-Gamma-ground product assembly, label/degree transport and
the coefficient/tensor conclusions remain separate obligations.


601-module checkpoint: 1937 public theorem types, 1769 definitions,
151 named instances and 8 selected reused declarations (3865 heads).
The finite geometric product charts contain actual same-base definable
bijections and full Gamma preimages. Characteristic zero, saturation,
real-base smallness and real-base Gamma nontriviality are explicit in the
product theorem. The original-Gamma angular partition only uses coefficient
values whose definability has been descended to that base. Product ambient
arities are explicitly distinguished from RV[k] degrees. No coefficient
monomorphism or tensor isomorphism is certified by this checkpoint.


613-module checkpoint: 1963 public theorem types, 1783 definitions,
151 named instances and 8 selected reused declarations (3905 heads).
The full original-Gamma-ground nonzero RV normal form has actual definable
product bijections, finite residue value support, and full Gamma fibres.
The finite code API equivalence is proved on every finite RV-sorted code
index. No Gamma representative enters the final base. Canonical structure,
ACVF00, actual saturation, small real/Gamma supports and original-ground
Gamma nontriviality remain explicit. Ambient arities are not RV[k] label
degrees. This receipt does not prove the coefficient or tensor claims.


623-module checkpoint: 1978 public theorem types, 1796 definitions,
151 named instances and 8 selected reused declarations (3933 heads).
The full RV tuple product charts preserve zero tags by an actual injective
nonzero coding, and pull back to their original source. The degree bound
uses actual independent RV points in each full Gamma fibre, never a
definable section. The RES representative has a genuine same-ground finite
nonzero label of the specified degree; ambient arities are not equated
with that degree. The rank helper's earlier exchange/Gamma algebraicity
records are explicitly visible and furnished by the checked [18] adapters
when assembling the chart-level tensor preimage. That later assembly and
all injectivity conclusions remain outside this receipt.


631-module checkpoint: 1992 public theorem types, 1802 definitions,
151 named instances and 8 selected reused declarations (3953 heads).
The concrete unmeasured positive tensor homomorphism and its actual
group-completed homomorphism are locally surjective under the original
small-base, saturation, ACVF00 and nontrivial-Gamma hypotheses. The final
entry points construct the earlier rank records from checked [18] proofs;
no abstract decomposition or HK comparison record is an input. The
finite-partition proof retains positive scissors without cancellation.
The legacy empty-bijection helper and all its dependents are included in
the successful corrected full build. No injectivity or measured tensor
isomorphism is certified by this receipt.


641-module checkpoint: 2014 public theorem types, 1811 definitions,
151 named instances and 8 selected reused declarations (3984 heads).
The finite Gamma-function cover is over the original mixed base; the
common real names are only used for compactness. Abstracted Gamma
predicates quantify universally over every proper code tuple, so they
remain invariant away from the original named parameter too. Unique-output
restriction and totalization by one have checked full-code graphs. The
actual volume-map graph and disjoint source partition are proved. These
lemmas do not assert a measured product factorization or either tensor
injectivity. Later value-reconstruction adapters are outside this receipt.


### Local measured product geometry — 655-module checkpoint

The full build and principle audit pass: 2034 public theorem types,
1819 printed definitions, 151 named instances and 8 selected reused
heads (4012 audited heads). Only the standard logical principles occur.
`GammaGroundRV_form_normal_form` now proves finite disjoint product
charts for every actual original-ground definable Gamma-valued weight
on a full RV tuple domain, including zeros. The charts retain an explicit
original-ground Gamma function giving the weight on the Gamma factor.
The proof reconstructs original values by the integral inverse monomial
matrix and splits the finite residue-value support into individually
original-ground definable Gamma tuples. It adds no RV representatives
to the ground and uses no HK input.

This is the measured geometric decomposition, not the measured tensor
comparison: the actual RES label degree, volume-form allocation and
positive scissors assembly still need to be joined to these charts.
The coefficient monomorphisms and tensor injectivity remain open.


### Concrete measured tensor surjectivity — 663-module checkpoint

The full build and audit pass: 2052 public theorem types,
1829 definitions, 151 named instances and
8 selected reused heads (4040 audited heads), using only the
standard logical principles. `MeasuredTensorSurjectivity` proves actual
object preimages and surjectivity of both `gammaGroundMeasuredTensorMap`
and `gammaGroundMeasuredGroupTensorMap`. It uses the locally proved
form-product charts, actual RES[k-m] degree transport, prescribed combined
weights converted to genuine same-ground volume forms, and finite positive
scissors assembly. Finite and degree-zero Gamma forms are retained.
No HK premise is used. Both unmeasured tensor surjectivity results remain
checked. Tensor injectivity and the Gamma-to-RV coefficient monomorphisms
remain open; Proposition 3.18 is not yet complete.


### Generic value fibres — 672-module checkpoint

The full build and audit pass: 2066 public theorem types,
1836 definitions, 151 named instances and 8 reused heads
(4061 audited heads), with standard principles only.
`GammaGenericValueFibres` proves original-ground generic value-fibre
invariance and constancy of actual Gamma-valued maps. `ResidueGenericValueFibres`
proves the version after naming a residue point and constancy of actual
maps into finite-value-support residue sets. `RVProductGenericMaps`
retains these statements after fixing a residue input in a product chart.
`RVFullGammaFibreDegree` proves that any finite-to-one map from a nonempty
full Gamma-preimage of arity m into RV[k] forces m ≤ k. The statements
about generic tuples are conditional geometric lemmas; they do not claim
existence or density of such tuples. Both tensor surjectivity proofs remain
checked. Injectivity and the coefficient monomorphisms are still open.


### Full-fibre monomial rigidity — 680-module checkpoint

The full build and audit pass: 2091 public theorem types,
1841 definitions, 151 named instances and 8 reused heads
(4091 audited heads), with standard logical principles only.
`RVMonomialFibreRigidity.rvMonomial_full_fibre_unimodular` and its affine
version prove that injectivity of an integral monomial map on one complete
RV value fibre forces a unit determinant. `FieldUnitPowerKernels` proves
the necessary characteristic-zero root-of-unity obstruction, and
`RVResiduePowerKernels` constructs the embedding of the actual algebraically
closed residue-field units into actual RV units, proves its value is one,
and derives the power-kernel obstruction without any HK premise.
`RVAngularInverseMonomials` retains the actual inverse chart formula, and
`RVAngularGraphRigidity` applies full-fibre rigidity to a square free input
block of an angular graph chart. The source projection remains injective
on the original graph. The matching-arity hypothesis is explicit; its
consequence at generic points and tensor invariance still need proof.
Both tensor surjectivity results remain checked. Neither tensor injectivity
nor the Gamma-to-RV monomorphisms are claimed complete.


### Generic graph arities and coefficients — 695-module checkpoint

The full build and audit pass: 2113 public theorem types,
1844 definitions, 151 named instances and 8 reused heads
(4116 audited heads), using only standard logical principles.
`RVAngularLabelDegree` proves that the free arity of an angular cell at a
Gamma-generic k-coordinate input equals its actual RV[k] label degree.
`RVGenericGraphBlocks` therefore supplies a square unimodular input block
without assuming matching arity. The lower bound uses the proved integral
left-kernel lemma for rectangular matrices and the old-ground Gamma values
of the residue coefficients. `RVAngularResidueUniqueness` proves that a
fixed residue-value fibre of an injective square product chart is a
singleton. `GammaGroundAngularResiduePoints` constructs actual original-
ground definable singleton pieces, and `GammaGroundAngularCoefficientPoints`
proves original-ground RV definability of the actual inverse-chart
coefficients and their definable images. Rectangular monomial maps retain
their parameter-free code graphs in `RVUnitRectangularMonomials`.

These are local graph results, not yet a complete classification of all
Gamma morphisms or tensor injectivity. Both tensor maps and their group
completions remain proved surjective. Finite-Gamma/residue-torus matching,
finite coefficient descent and lower-free-arity induction remain separate
obligations. The manuscript has not changed.


### Actual unit graphs and output formulas — 703-module checkpoint

The full build and audit pass: 2128 public theorem types,
1856 definitions, 151 named instances and 8 reused heads
(4143 audited heads), using standard principles only.
`GammaGroundRVUnitGraphs` presents actual definable-map graphs as unit
RV tuples, proves injectivity of their input projection (and output
projection for injective maps), and constructs an actual finite input
label. `RVProductResidueFinite` proves finiteness of a residue factor
when the full Gamma factor exhausts the label degree. Integral block
elimination is proved in `IntegerMonomialElimination`;
`GammaGroundAngularOutputMonomials` gives graph outputs as integral
monomials in the original input with actual old-ground RV coefficients.
`RVAngularOutputRigidity` proves unimodularity of the induced output
matrix when both projections are injective. Tensor injectivity and the
Gamma coefficient monomorphisms remain open; finite-Gamma/residue-torus
matching and descent must still be handled. Both surjectivity results
remain checked. No manuscript change or HK premise has been introduced.


## Generic-fibre monomials and critical review — 2026-11-12

The integrated build and complete audit pass for 712 supporting modules
plus their aggregate: 2142 public theorem types, 1860 definitions, 151
named instances and 8 reused declarations (4161 audited heads), with only
standard logical principles. `RVGenericFibreMonomials` proves an actual
old-ground definable RV map is an integral affine monomial on the entire
value fibre of a Gamma-independent input, with individually old-ground
RV-definable coefficients. For an injective square map its matrix is
unimodular. `UnimodularMonomialFibres` and `RVAngularInputFibres` supply the
whole-fibre solution argument. `GammaGroundUnitFibreDescent` and
`GammaGroundMonomialFibreDescent` construct actual Gamma morphisms,
including full code lifts, from value-kernel-preserving RV bijections.

A critical obstruction to the remaining tensor injectivity was found while
checking finite coefficient descent. Over S=C((t)), the five RV roots R of
rv(t) supply a coefficient-dependent translation between the full lifts
of (0,infinity) and (1/5,infinity). Thus the two corresponding R-weighted
RV products are isomorphic. A periodic odd endpoint-weight invariant,
extended through the tensor universal property to Z[epsilon]/(epsilon^2),
distinguishes their source tensors. The full mathematical argument and its
scope checks are in `verification/TENSOR-COEFFICIENT-OBSTRUCTION.md`; the
concrete model and complete detector are not yet Lean constructions.
This is not a claim that the measured map has the same counterexample.

Review item T001 presents this argument in blue beside Proposition 3.18
in a manuscript copy, at
`reference/proposed-revisions/T001-finite-coefficient-review.pdf`, printed
pages 34–35. The PDF-only right-panel request returned queued. The working
manuscript is unchanged. The author must review the mathematical obstruction
before a replacement theorem or change of ground/coefficient conventions
is chosen. No new HK acceptance request is pending; no HK premise was used.
Both positive tensor surjectivities and their group completions remain
proved. Neither tensor injectivity nor the coefficient monomorphisms are
claimed complete, and section 3 remains unfinished.


## Thorough HK convention audit — 2026-11-12

At the author's request, the parameter, algebraic base-change, RES,
Gamma-morphism, effective/resolved, grading and localization conventions
were traced through HK and the full tensor argument. Critical passages
were compared in arXiv v2/v3 and cached text of Oxford's accepted manuscript.
The publisher's full typeset chapter was not accessible. The source map,
rejected possible resolutions, and independent balancing calculation are
recorded in `verification/HK-CONVENTION-AUDIT.md`.

No convention was found that resolves T001 for the fixed-ground,
unlocalized graded tensor. The example satisfies tau*a=tau*b, where tau
is the degree-one finite-Gamma singleton whose RV lift is the residue
torus. It therefore vanishes after tau-localization, but the stated
Corollary 10.3 tensor is not localized. This is a concrete explanation
of why the separate localized constructions do not establish its original
injectivity. Merely replacing the translation subgroup by its divisible
hull would instead invalidate the fixed-ground RV lift of a singleton.
No main-text correction or replacement theorem is adopted. The Lean
sources and verification receipt are unchanged; T001 remains open for
mathematical review, and no complete Lean counterexample is claimed.


## Claim 3: the exact strength needed for induction

The finite-root example satisfies Claim 3's stated product and fibre
conclusions, with RES map h(r)=r and Gamma map k(gamma)=gamma+1/5.
Thus the diagnosis is that the stated claim is too weak for the tensor
identification; it is not refuted by that example as a statement about
definable factor bijections. Fixing r gives a lift over S(r), not S.

The stronger same-ground-lift conclusion is false even after shrinking
around the Gamma type at positive infinity. Every definable neighbourhood
of that type contains a tail and hence an integer N. A lift over S=C((t))
evaluated at rv(t)^N would give an S-definable RV element of value N+1/5,
contradicting RV definable closure over this henselian ground. This rules
out every possible same-ground lift on those neighbourhoods, not just the
particular multiplication-by-r formula. The complete line-by-line audit
and corrected weak/strong distinction are in `verification/HK-CLAIM3-AUDIT.md`.
The supporting Lean sources and approved manuscript are unchanged.

## Kernel presentation: mathematical status only

The unmeasured kernel calculation in `TENSOR-KERNEL-PRESENTATION.md` uses
actual RES-dependent multipliers, not a same-ground Gamma lift. It
identifies both the positive generating pairs and the groupified ideal,
and proves at the mathematical level that one degree-one torus factor
annihilates each generator. The local uniformization, finite-cover and
global induction are not yet audited Lean exports. No new declaration
was added and the 712-module receipt is unchanged. No measured kernel
formula or equality with the entire torus annihilator is claimed.

## Measured follow-up: mathematical calculation, unchanged Lean receipt

The new measured calculation is in
`MEASURED-TENSOR-KERNEL-PRESENTATION.md`. The old Jacobian convention gives
the compensating target form sigma(eta-delta e_i)-delta. The reverse
inclusion explicitly moves a constant RES weight difference through the
shared degree-zero coefficient p_a before using the local monomial
rectangles. The finite-coordinate normalization uses the measured point
({delta},-delta), whose combined weight is zero. The root example now
has an actual choice of distinct volume forms, and forgetting forms
proves its nonvanishing. The canonical zero-combined-weight construction
also embeds the ordinary kernel. These global calculations, the concrete
model/detector, and the full measured kernel equality remain mathematical
proofs rather than completed Lean exports. No public declaration or
source snapshot changed, and no entire-annihilator equality is asserted.


## Audited positive kernels and context instances — 2026-11-12

The complete integrated project build and declaration audit pass for
**842 supporting modules plus Section: 2566 theorem types, 2116 definitions, 151 named instances and 8 reused heads (4841 audited heads)**. Only propext, Classical.choice and Quot.sound occur.
The approved manuscript hash and all dependency pins are unchanged.

`MeasuredTensorPositiveKernel.lean` now proves the reverse measured kernel
inclusion, the exact equality of the elementary coefficient congruence
with the actual kernel, bijectivity of the quotient map and its semiring
isomorphism. `MeasuredTensorQuotientGrading.lean` gives the multiplicative
fixed-degree direct-sum grading, degree inclusions and original r+n
object-degree formula. These match the completed unmeasured exports.

The measured proof keeps all forms: finite RES-weight normalization,
weighted two-sided monomial matches and cuts, actual disjoint image
partitions, genuine glued volume forms on the rank-layer object, and the
actual inherited measured residual bijection. `MeasuredHyperplaneTensorReduction`
and `MeasuredNativeTensorHyperplaneReduction` transfer one fixed Gamma
coordinate into RES by finite measured balancing and retain the full
residual weight. `MeasuredTensorRankZero` and `MeasuredTensorRankInduction`
close the positive rank argument. `MeasuredTensorDegreeReassembly` projects
the actual RV direct sum and reassembles the finitely many original degrees.

`TensorPresentationContext.lean` supplies both corrected Proposition 3.18
presentations, their kernel statements and their graded versions in the
actual VF/Gamma-generated `GammaGroundContext`. Its nontriviality bridge
uses only Gamma names; it requires no nontrivial value in the real VF part.
Canonical structure, ACVF00, actual saturation, both base-smallness bounds
and nontrivial original-ground Gamma remain explicit. No HK statement,
additive cancellation or groupification enters either proof.

General transport from arbitrary presentations of imaginary ground names
and other section-wide context interfaces remain separate. The complete
section is not certified finished. The final corrected T001 statement and
both proofs are blue in the same manuscript-context PDF, printed pages
34–36, awaiting the author's review under AGENTS.md. The PDF-only right-panel
request returned queued; visibility is unconfirmed. No final T001 adoption,
commit or push has been made.


## Adopted manuscript, finite-name diagrams and positive descent — 2026-11-12

The integrated build and full declaration audit pass for **849 supporting modules plus Section: 2587 theorem types, 2134 definitions, 154 named instances and 8 reused heads (4883 audited heads)**,
with the adopted manuscript hash
24c58ba674814c3f12f6097b9fd61dc5675af627b6b9d4a43cae46052e6f68cb.
Only standard logical principles occur and all dependency pins are unchanged.

GammaGroundFiniteNameSupport gives common original-name support for finite
heterogeneous sets and full graphs. GammaGroundNamedFunctors preserves
actual VF, RV and measured RV maps faithfully. GammaGroundNameClosure proves
that already definable interpreted names add no definable sets or graphs,
while retaining every old Gamma name. GammaGroundMeasuredDiagramSupport
and GammaGroundVFDiagramSupport reconstruct finite diagrams literally,
including all measured RV labels and forms. No real RV representatives
are added to the ground.

PositiveTensorDescent proves the necessary-and-sufficient elementary-pair
criterion and uniqueness for descent to RV for both positive tensor maps.
BalancedTranslationDescent constructs the unique positive RV evaluation
from balanced coefficient maps and a numerically translation-invariant
Gamma evaluation; its restriction to RES is exactly the prescribed map.
This is an interface for the later Euler construction, not a claim that
the numerical Euler characteristics or section 4 balancing have been built.

The separate Gamma-to-RV and finite-Gamma-to-RES positive monomorphisms
in the prose coefficient square remain proof obligations. The actual
degree-zero VF/RV category equivalence is also not yet exported over the
complete Gamma ground; invariant finite VF coding is the next local step.
The updated verifier scope metadata records these concrete boundaries.
No new manuscript review is pending, and no commit or push has been made.


## Actual degree-zero comparisons — 2026-11-12

The integrated build and complete declaration audit pass for **860 supporting
modules plus Section: 2605 theorem types, 2150 definitions, 158 named
instances and 8 reused heads (4921 audited heads)**. Only standard logical
principles occur. The adopted manuscript and dependency pins are unchanged.

`BoundedVFFibreCoding`, `GammaVFCoordinateRows`, `GammaFiniteVFCodeGraphs`
and `GammaFiniteVFCoding` give uniform finite VF codes whose entire graphs
are invariant under every representative of the original Gamma names.
`GammaGroundFiniteVFCodeMaps` turns those graphs into actual definable
injections; `GammaGroundFiniteMixedCoding` retains existing RV coordinates
and codes finite mixed domains over that same ground.

`GammaGroundVFZeroFiniteness` proves intrinsic finiteness of every ordinary
VF[0] domain. `GammaGroundZeroRVLift` and
`GammaGroundZeroCategoryEquivalence` prove the actual ordinary category
equivalence using the manuscript's object lift, full faithfulness and
essential surjectivity. Canonical structure, ACVF00, saturation, small real
base and the valuation-topology compatibility remain explicit. Temporary
Gamma-code realization is used only to prove intrinsic finiteness, never
to descend a map defined over an expanded real base.

`GammaGroundZeroMeasuredLift` and `GammaGroundZeroMeasuredEquivalence`
prove the measured degree-zero category equivalence with every original
Gamma form retained pointwise. The measured domains already have no VF
coordinates, so this equivalence needs no extra coding or saturation
hypotheses. No HK premise, cancellation or groupification is involved.

The separate Gamma-to-RV and finite-Gamma-to-RES positive monomorphisms
remain unfinished. Both positive tensor quotient presentations are already
proved and adopted; the coefficient embeddings are being checked directly.
No manuscript review is pending, and no commit or push has been made.


## Annular compatibility and the coefficient proof question — 2026-11-12

The integrated build and complete declaration audit pass for **873 supporting
modules plus Section: 2620 theorem types, 2172 definitions, 158 named
instances and 8 reused heads (4958 audited heads)**. Only standard logical
principles occur. The adopted manuscript hash remains
24c58ba674814c3f12f6097b9fd61dc5675af627b6b9d4a43cae46052e6f68cb;
the dependency pins are unchanged.

`GammaGroundRVFamilyReflection` reflects arbitrary bijections of actual RV
family realizations to complete definable family graphs.
`GammaGroundGammaLiftReflection` transports those bijections to full code
families and proves descent when the decoding equivalence is preserved and
reflected. It proves the Gamma-to-RV positive injection in degree zero and
reflection for singleton Gamma domains in every arity, including values
without definable RV representatives. It does not prove reflection for all
finite Gamma unions or all Gamma objects.

`GammaGroundConstants`, `FullGammaFunctionOrder` and
`GammaGroundPointTranslations` construct actual old-ground multiplier maps.
`GammaGroundTails` and `GammaGroundAnnulusAbsorption` prove the positive tail
decomposition and absorption of the half-open annulus (0,delta], including
the zero-radius case. `GammaGroundAnnulusRingVanishing` derives zero only
after additive completion in the full unbounded Gamma and RV rings.
`GammaGroundDefinablePoints` supplies the actual singleton bijections.
`GammaGroundMeasuredRVForgetting` constructs the positive and ring
forgetful homomorphisms on actual objects and full forms.
`GammaGroundAnnularForgetting` proves the corresponding stipulated annular
expressions vanish after forgetting forms.

`IdealPullbackKernel` and `GammaGroundAnnularPullback` prove annihilation of
their entire generated ideal and its full pullback into the actual
unmeasured tensor kernel for every commuting presentation. The latter
retains the presentation maps and their commutation equation as explicit
arguments. The concrete bounded categories and comparison maps from
section 4 have not been constructed; this is not a certification of the
whole bounded diagram or of numerical Euler characteristics.

C001 is the critical remaining coefficient-embedding proof question:
from a same-ground RV bijection I-sharp ≃ J-sharp, construct a same-ground
Gamma bijection and some fibre-respecting replacement RV bijection, with
all finite tags retained. An arbitrary supplied RV bijection need not
itself contract. Neither the corrected tensor quotient theorem nor the
checked descent criterion constructs this replacement. The finite Gamma
case without definable RV representatives is part of the open obligation.
No counterexample or mathematical error in the coefficient embedding is
asserted, and no HK input is being requested or assumed.

The proof question is blue inside the unchanged manuscript context on
printed pages 33–34 of `reference/proposed-revisions/C001-coefficient-embedding-question.pdf`.
The PDF-only right-panel request returned queued; visibility is unconfirmed.
The working manuscript is unchanged, and no commit or push has been made.


## Coefficient-map scope correction — 2026-11-12

The lower horizontal map is checked for the explicit full-preimage
category encoded by `GammaHom` and `GammaGroundGammaHom`. Its comparison
with an interpretation of Definition 3.13 allowing contractions of
bijections between arbitrary RV subsets was not established. Under that
weaker interpretation, the fifth-root example over C((t)) separates equal
Gamma singleton classes whose full RV fibres are not definably bijective;
well-definedness itself fails. The model and curve argument are a
mathematical audit, not a newly compiled Lean model construction. See
`verification/COEFFICIENT-MAP-SCOPE-AUDIT.md` for the proof and the exact
scope of the reference to Lemma 2.29.

For the full-preimage definition, horizontal injectivity remains an open
local proof obligation: no counterexample to it has been established.
The new review batch C001/C002 proposes making that definition explicit
and provisionally omitting horizontal monicity; the latter is withdrawal
of an unsupported assertion, not a claim that it is false. The previous
C001 proof-question PDF is preserved. Both new proposals require author
review, and the approved manuscript is unchanged. The updated integrated
audit passes with the existing 873 supporting modules and 2620 theorem
types; this scope correction does not add Lean results.


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


## Positive monicity: mathematical proof and dependency check — 2026-11-12

A mathematical proof of the intended positive Gamma-to-RV monomorphism
was found. It extracts the unique residue-generic fibre match of an
arbitrary RV bijection, uses the original-ground RV twisting character
group, and applies Reichstein--Youssin Theorem 7.1 / Corollary 2.5 to
replace the equivariant birational match by a full monomial torus
isomorphism. Compactness glues finitely many such replacements. The upper
positive coefficient injection follows from the square and the checked
vertical injections. See `verification/COEFFICIENT-MONICITY-CHECK.md` for
the hypotheses, descent argument and source.

This is a mathematical proof using an external birational theorem, not
a completed local Lean proof. That external theorem is outside the
author-accepted input list and has not been added as a premise. No
groupified injectivity is inferred. There are no new supporting Lean
result modules or completed numbered formalizations in this update.

Horizontal monicity is unnecessary for the later constructions. The
manuscript dependency audit covers sections 3--8; all uses need the
horizontal homomorphisms, corrected quotient presentation and appropriate
descent checks. In particular Psi inverse and its bounded counterpart
need the quotient formulation already required by corrected 3.18. The
piecewise h_m maps retain separate lattice/descent obligations.
`verification/CoefficientDependencies.lean` also traverses the actual
compiled declaration closures of seven existing tensor, descent and
annular-pullback roots. It passes without horizontal injectivity; the
checked vertical RES-to-RV injection is used. The log and a separate
dependency receipt are retained in `verification/`.

C001 is withdrawn. C002 now presents the proof and its later role, with
no proposed definition change or assertion that monicity is false. The
blue manuscript-context review is
`reference/proposed-revisions/C002-monicity-and-use-review.pdf`, printed
pages 34--35. No manuscript edit or new external Lean input is adopted.


## November 12: C002 approved and local birational proof bridges

The author approved adding the proof and the published Reichstein–Youssin
citation. C002 is incorporated in black, with a green author resolution;
there is no matching referee item. The manuscript source SHA is
`080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97`.
The resolved manuscript PDF is
`reference/proposed-revisions/C002-resolved-review.pdf`, pp. 34–35.
Its PDF-only right-panel request returned queued; visibility is unconfirmed.
C001 remains withdrawn. Earlier entries saying C002 or the cited input is
unapproved are historical and superseded by this entry.

The exact characteristic-zero diagonal-action classification is now the
explicit replaceable `ReichsteinYoussinInput`; no HK premise is accepted.
Local Lean proofs construct polynomial/rational diagonal actions, prove
faithfulness from joint weight generation and birational equivariance,
extend characters into algebraically closed field units, and recover
actual old-ground definable RV coefficients from equality modulo their
value subgroup. The resulting unimodular maps are full-fibre maps.

The pure-field bridge is checked locally: definable closure in ACF0 is
the parameter field; partial definable graph outputs lie in the field
generated by the inputs; a two-sided functional relation identifies those
fields and preserves independence of equal-length tuples. Their rational
function field isomorphism intertwines any diagonal action preserving the
graph. Formula transport uses the checked ACF QE proof and an intermediate
field embedding, without requiring an ambient automorphism. The cited
classification is applied only after these local constructions.

Countably many algebraically closed coefficients can be chosen inside the
same residue field. Genuine saturation supplies independent residue tuples
over such a countable field. Actual original-Gamma-ground RV relations
normalize to pure residue-field relations without adding the normalizing
representatives to the final ground. The character twist fixes residue
points and original-ground RV points, preserves values and the named total
residue operations, and respects all well-sorted terms and formulas via
the released ACVF QE theorem.

This is supporting formalization, not completion of all-degree horizontal
monicity or the whole section. Finite generic-fibre matching, its uniform
original-ground definability and finite gluing still need local proofs.
No groupified injectivity is inferred. The later constructions do not use
horizontal monicity; the earlier dependency receipt remains applicable.
The complete audit must be rerun after the current additions before its
receipt covers this update.

The complete original-ground character-symmetry bridge now checks:
`GammaGroundCharacterSymmetry.rvCharacterTwist_definableOverBase` removes
all moved Gamma representatives by their invariant full code preimages;
`GammaGroundRVMapCharacterSymmetry.gammaGroundRVMap_character_equivariant`
applies it to actual map graphs. This introduces no extra names, no HK
input, no ambient VF automorphism and no saturation hypothesis. The
remaining monicity obligations are generic-fibre matching, its uniform
original-ground definability and finite gluing.


### Integrated C002 bridge audit

The 904-supporting-module checkpoint passed the complete project build
(11,389 Lake jobs) and declaration audit: 2,692 theorem types, 2,199
printed definitions, 158 named instances and eight reused declarations,
5,057 declarations in total. Only `propext`, `Classical.choice` and
`Quot.sound` occur. The receipt pins the approved C002 manuscript SHA
`080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97`.
Further generic-fibre modules added after this checkpoint require the
next integrated receipt. No complete all-degree monicity claim is made.


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


## Checked ring continuation — 2026-11-12

The full integrated project build and declaration audit pass (11,487 Lake
jobs), with 1,002 supporting modules plus Section. The receipt covers
2,866 theorem types, 2,270 definitions, 170 named instances and eight reused
declarations, totaling 5,314. Only `propext`, `Classical.choice` and
`Quot.sound` occur. It validates 119 declaration links for the 21 manuscript
targets. Counts report supporting infrastructure, not additional numbered
paper theorems.

Both actual ring tensor kernels now equal the ideals generated by the
explicit positive coefficient-pair differences. Both quotient ring
comparisons are instantiated in GammaGroundContext. Ring evaluation descent
is characterized by the same displayed pairs, with construction, image
formula and uniqueness proved. The full annular pullback lands in the
explicit unmeasured relation ideal for every commuting presentation.
These are local consequences of the already proved positive presentations;
no new cited premise, cancellation or embedding into group completion is
used. They complete the concrete groupification consequences of the §3
presentation. Actual Gamma Euler characteristics and concrete bounded §4
categories are separate §4 work. The supplementary signed unary-cone
refinement and diagnostic detector examples are not claimed as Lean exports
by this section certificate.

The §3 manuscript targets are covered in the documented paper contexts,
relative to the accepted later [18] lift/kernel records and approved R--Y
classification. No HK result is a given input. The manuscript hash remains
080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97.
No commit or push was made. The approved PDF-only right-panel display
request returned queued; visibility was not asserted.


## [18] refresh and push authorization — 2026-11-12

The author explicitly skips the supplementary unary-ray refinement and
requests an upstream check, complete audit and push. The dependency is now
pinned at 7d4acc730496b3bd05a22c268ffd89540ca694f9. The previously reused
section 2–3 files are unchanged. Section 4 is checked and section 6 now
supplies finite RV integration, kernel and principal-ideal proofs relative
to its explicit unfinished section 5.8 input. Section 7 measured integration
is not available.

IntegrationLaterExports links ten exact section 6 declarations; their full
types retain Section5TwoOrderInputAll, native finite RV/VF categories and
VFGammaGeneratedBase. The last condition explicitly requires definable
closure of the generating base. GammaGroundContext records a generated
real substructure and a Gamma subgroup, without that closure equation.
The existing lift-input records therefore remain explicit until both the
closure transport and native/consumer category comparisons are compiled.
No legacy input is silently claimed discharged by an export alias.

The already approved proper-open-radius compatibility patch covers nine
dependency files. Numbered statements are unchanged; two auxiliary obstacle
premises now use proper OpenRadius, matching their corrected predecessor
producers. Other edits are confined to proof bodies. The patch, auxiliary
API changes, file hashes and base revision are recorded explicitly. CI now
prepares both dependency patches and runs both section audits.

The main branch's independent section 2 citation update was fast-forwarded
and reconciled with this work. The approved manuscript remains unchanged.
Both combined section audits passed before the authorized push to origin/main.


## Verified upstream refresh prepared for publication — 2026-11-12

Both section audits pass at the pinned Lean 4.35.0 toolchain. Section 2
retains 850 theorem exports and 378 selected reuse declarations. Section 3
checks 2,866 theorem types, 2,280 definitions, 170 named instances and eight
reused declarations: 5,324 heads across 1,003 supporting modules plus Section.
The receipt validates 36 native [18] export links and the 21 manuscript
targets with 119 declaration links. Only the permitted standard logical
principles occur. Both compatibility patches also apply to their clean
dependency indexes.

The native section 6 theorem types retain the unfinished Section5TwoOrderInputAll
and exact generated-closure/category conditions. Legacy lift/kernel records
remain explicit pending the checked comparisons; section 7 measured inputs
are not claimed discharged. No HK input or manuscript change is introduced.
The author explicitly skips the unary-ray refinement. CI now prepares both
patches and audits both sections, with the same 180-minute build allowance
as the upstream project. This record reports local verification; CI is
reported separately after publication.
