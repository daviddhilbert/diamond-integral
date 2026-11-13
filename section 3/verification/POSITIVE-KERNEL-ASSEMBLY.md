# Remaining positive kernel assembly

The explicit elementary congruences, both surjective quotient maps, the
unmeasured generic local monomial rectangles and their local congruence,
the generic arity inequality, the unmeasured positive hyperplane rank
reduction, the finite monomial covers with actual patch images, and finite
positive common product refinements are checked. The global reverse kernel inclusion is still a
target. This file records the intended concrete assembly, not an extra
input or a completed numbered theorem.

## Positive algebraic normal forms

`TensorObjectNormalForm.lean` gives an actual finite list of
RES/Gamma object terms for every positive tensor. Each term retains its
RES degree and Gamma degree; its actual RV product has their sum as its
degree. The proof uses `DirectSum.induction_on`, the already proved
positive-presentation additive normal form, and tensor induction. Its
measured counterpart retains the measured object data and all forms.
There are no differences of classes.

Finite Gamma-family tags can be separated into a positive sum of native
single pieces using the actual tag-reindexing Gamma morphisms and
coproducts. `GammaPieceSums.lean` proves that step and `TensorPieceNormalForm.lean`
produces lists with a single native Gamma piece in each term.
`RESUnitCoordinates.lean` constructs one native RV-unit chart for every
actual RES coefficient using the fixed nonzero tuple encoding. Its value
support is finite, its original degree and label are retained, and no
Gamma factor or extra parameter is introduced. Native restrictions retain
those labels through their actual preimages. The same file transports the
local monomial congruence through the stored chart bijections.

Regroup the finite object lists by total degree. The existing positive RV
semiring/direct-sum comparison supplies equality in each degree. At one
fixed total degree, the existing positive RV class/isomorphism comparison
turns equality of product-union classes into an actual original-ground
RV bijection between the corresponding finite coproducts. It does not
use cancellation or stabilization. `TensorDegreeBijections.lean` checks
this degreewise actual-bijection extraction.

## Maximal free Gamma rank

Take the maximum free Gamma arity on either side. At a generic point in
one maximal-rank source chart, restrict to the target chart containing
its image. The source restriction is an original-ground definable subset
of the unit-free tuple times the retained residue tuple. Generic full-fibre
invariance over the residue input keeps the whole generic value fibre in
this target branch.

Apply `gammaGroundRVProduct_generic_fibre_arity_le` to the target free
and RES projections. The maximal-rank bound on the target gives equality
of the two free arities. The total degree then gives equality of the RES
label degrees. The checked monomial-neighbourhood theorem supplies
RES-dependent coefficients, constant old-ground values, and a unimodular
integer matrix. The residue-output injection theorem identifies the
RES output with its actual definable image. Its finite value support
follows from containment in the original target RES domain.

The image of a rectangle is the product of that RES image with the full
Gamma preimage of delta times the integral monomial Gamma image. This
uses `affineMonomial_full_value_fibre_solve`; its coefficient values are
constant across the retained RES input. Transport the native coefficient
map and the RES bijection through the stored label-chart bijections.
`TensorLocalMonomialCongruence.lean` gives the local
positive congruence from these actual data. The tuple translation is
proved from one-coordinate pairs by
`TensorTupleCoefficientCongruence.lean`, for arbitrary Gamma domains U.

## Finite matching on both sides

`RVProductFiniteMonomialCover.lean` now checks the finite monomial
cover on any actual square product-map branch, including the actual
product bijection onto each patch image and its agreement with the
original map. Patch Gamma factors remain inside their original source
and target Gamma domains. `RVProductLowerArityCover.lean` puts any
branch with a smaller target free arity entirely over finitely many
proper original-ground character hyperplanes. Apply these results to
the maximal-rank source charts. Its exceptional sets are preimages of proper old-ground
character hyperplanes. Do the same for the inverse RV bijection on
maximal-rank target charts. This second direction is necessary: covering
only generic source points does not by itself prove that the residual
target Gamma factors have smaller rank. Inverting the local product
bijections gives the corresponding source rectangles and the symmetric
local congruences. Combine the two finite families.

`TensorProductCuts.lean` checks the positive three-term rectangular
scissor identity, its actual complement, and its native RES-label
transport. `TensorRectangleRefinement.lean` iterates those cuts: it
retains the entire positive value, gives pairwise disjoint product leaves
covering the original product, and makes each leaf either contained in
or disjoint from every prescribed patch. Choosing the first containing
patch therefore gives a finite source matching.
Restrictions of a local formula retain its coefficient value, matrix,
RES injection and congruence. The product images of these disjoint
source rectangles are disjoint because the original RV map is injective.
`TensorBooleanCells.lean` now supplies the necessary positive tensor
identity for every finite disjoint full-preimage product partition. It
uses a common finite grid from separate RES and Gamma Boolean atoms,
including all empty atoms, rather than RV cancellation.
`NativeTensorProductPartitions.lean` and `RVMonomialPatchRestrictions.lean`
transport this identity and the local congruence through the original RES
unit charts (individually checked; added after the latest full audit).
The global selection and matching of these finite partitions still needs
assembly.

Decompose any remaining mixed source and target complements with the
existing mixed finite-product theorem. Actual RV scissors give the two positive sum
identities. Restrict the original RV bijection to these complements;
this supplies the residual comparison without cancelling the matched
summands in any semiring.

The finite covers show that every remaining maximal-rank Gamma factor,
for a nonempty RES coefficient, is covered by finitely many character
hyperplanes. Partition it by the first applicable hyperplane and apply
`gammaGroundUnmeasuredTensor_character_hyperplane_reduction` to each
nonempty part. This decreases Gamma arity and transfers the removed
degree into RES. Empty pieces have zero positive class. Normalize the
resulting RES factors back into unit charts if necessary. The actual RV
images remain equal by the residual RV bijection and the checked product
and balancing comparisons. `FiniteHyperplaneTensorReduction.lean` now proves the finite-cover
reduction, with exactly one degree transferred to RES and empty atoms
represented by actual zero-class objects. Induction on maximal Gamma
arity applies once the finite residual matching is assembled.

`TensorRankZero.lean` proves the base case: at arity zero all Gamma
factors are finite and are absorbed into RES by positive balancing. The
existing positive RES embedding into RV gives equality in the positive
tensor itself. Add the matched local congruences and the inductive
residual congruence, and reassemble the finitely many total degrees.
This proves the desired reverse congruence inclusion once all the
assembly just described has been encoded.

The finite RV coproduct geometry is checked separately in
`RVFiniteCoproductAtlas.lean`: its component maps are injective, their
images are disjoint and cover the actual coproduct. This is the next
bridge from the normal-form bijection to the branchwise local covers.
`GammaGroundChartTransitions.lean` checks the partial coordinate maps
through an actual RV bijection, their injectivity, agreement and target
cover pullback. `NativeTensorCharts.lean` retains each product term’s
original degrees and labels with its actual native product bijection.
`TensorDegreeReassembly.lean` checks positive regrouping by total degree
and equality of the actual RV images in every homogeneous block.

## Measured follow-up

Apply the same underlying geometric argument to measured RV bijections.
Normalize Gamma combined weights under integral coordinate changes and
fixed-prefix absorption, retaining the actual forms. On a matched
nonempty rectangle, the source RES weight divided by the transported
target RES weight equals the target Gamma weight divided by the source
Gamma weight. Independence of the two product variables makes this a
single original-ground definable Gamma constant. Its definability can be
proved from the actual singleton Gamma image of the RES ratio map.

The shared finite measured Gamma object in degree zero with this constant
combined weight moves the shift across the tensor by the checked positive
finite-factor balancing identity. Its inverse is the actual object with
the inverse Gamma weight. Then the transported Gamma combined weights
match, and the measured coordinate pairs apply. Full combined-weight
transport gives the paper's sigma_delta(eta)=sigma(eta-delta e_i)-delta.
No additive inverse of a semiring class is needed.


## Checked assembly checkpoint, November 12

The 788-module integrated receipt includes the actual rank-layer atlas,
forward/inverse finite product covers combined into one matrix, disjoint
source selection and the congruence between the matched positive sums.
All original target patches remain covered after source selection.
Target child boxes can be pulled back within their original disjoint
parents, and matched boxes plus uncovered cells give a positive tensor
partition without cancelling any summand.

Three modules checked individually after that receipt are now registered:
`RankLayerResidualCovers.lean` restricts the actual global RV bijection
to the complements and keeps both generic covers;
`NativeBoxResidualPartitions.lean` gives the positive parent decomposition,
regroups matched children by parent and covers each residual Gamma factor
by the original finite exceptional hyperplanes;
`NativeTensorHyperplaneReduction.lean` turns such a factor into a finite
native homogeneous normal form with strictly smaller free Gamma arity.

Next identify the complete residual tensor sum with the inherited RV
complement, including the old lower-rank charts, then apply the rank
induction and degree reassembly. This is unfinished proof work, not a
replaceable input or a claim that Proposition 3.18 is complete.


## Unmeasured assembly completed at explicit Gamma-ground scope

The 794-module integrated audit checks the complete unmeasured route:
`RankLayerResidualAtlas.lean` gives the residual positive identity, its
actual inherited RV presentation, and the strictly smaller-rank native
normal form. `UnmeasuredTensorRankInduction.lean` proves the induction
step using both generic covers and the actual residual RV bijection.
`UnmeasuredTensorPositiveKernel.lean` then proves the reverse inclusion
for arbitrary positive tensors, by normal forms and total-degree
reassembly. It proves equality of the least elementary congruence with
the actual kernel, bijectivity of the quotient map, its semiring
isomorphism, and its object-class formula.

All geometric context hypotheses remain explicit, including both ground
smallness conditions. No HK theorem, stabilization, additive cancellation
or groupification is used. Earlier descriptions above record the proof
route and prior checkpoints. The separate formal graded quotient interface
and the measured reverse inclusion remain unfinished.


## Measured route after positive weight normalization

The 799-module receipt includes the explicit graded unmeasured quotient
and the measured RES finite-weight partition and shared degree-zero weight
shift. Current later checked modules normalize every positive measured
tensor into a finite list retaining both original degrees, with RES
combined weight one and a full definable Gamma weight on each native
piece. Partial Gamma forms are totalized by one over exactly the old
ground. Actual measured Gamma tags split positively. Weighted full-fibre
RV bijections descend to measured Gamma morphisms with their real code
contractions; weighted unimodular monomials and coefficient tuple
translations use the displayed coordinate congruence.

Remaining concrete route:

1. Package a measured native chart as an existing unmeasured native chart
   together with a full Gamma combined-weight function. Its RES coefficient
   is the original labelled underlying object with prescribed combined
   weight one. A normalized measured RES object has that same positive
   class by the identity measured bijection. The actual measured product
   object has the old native product bijection, with weight f(val(u)).
2. Give the measured native RES and Gamma restrictions their positive
   finite Boolean partition identities. This repeats the positive grid
   algebra with the retained weight function on each Gamma atom; it
   requires no equality of RV classes and no cancellation.
3. Decorate actual monomial patches and their two-sided cuts with the
   measured local congruence. The global measured RV bijection and the
   native weight formulas give f(gamma)=h(delta*M gamma) on a nonempty
   rectangle, by choosing a RES point only inside the proof. No RES weight
   shift remains locally after the preceding normalization.
4. Reuse the underlying actual square/lower-arity cover geometry, but
   select source cells using the weighted cut data so the chosen match
   retains its measured congruence. Forgetting weighted cut proofs and
   subsequently recovering them from arbitrary unweighted choices would
   be circular. Underlying source/target image disjointness and the actual
   residual bijection use the already checked generic geometry.
5. Extend hyperplane reduction to the weights: a unimodular Gamma change
   transports the full weight function; its fixed old-ground prefix is
   absorbed with combined weight one, while substituting that prefix in
   the Gamma weight gives the residual full weight function. The RES
   combined weight remains one. The free Gamma arity drops and its degree
   transfers to RES. At arity zero absorb the full finite measured Gamma
   object, including its form, into measured RES and use its positive RV
   embedding.
6. Assemble the measured rank-layer residual tensor/RV presentation and
   rank induction as in the completed unmeasured proof, retaining the
   weights on original lower-rank charts. Reassemble total degrees via
   the actual measured RV direct-sum comparison, then prove the exact
   measured congruence kernel and graded quotient isomorphism.

The proved unmeasured kernel may certify underlying positive congruences
when forgetting measured matches; it must never be used as a substitute
for a measured congruence or a form-preserving residual comparison.


## Measured local checkpoint: 810-module full audit

The normalized measured piece normal form, weighted fibre descent,
weighted unimodular Gamma morphisms, generation of tuple translations
by the elementary coordinate pairs, and the weighted local monomial
congruence are all in the integrated receipt. Measured native charts
carry the old actual RV product coordinates and the full retained Gamma
weight; finite native RES/Gamma partitions preserve every label and weight.

After this receipt, `MeasuredTensorBooleanCells.lean` checks the positive
measured finite disjoint full-preimage product partition identity. Its
RES factor may carry an arbitrary original measured form. The common
Boolean grid uses the same Gamma function on each Gamma atom, so this
step needs neither a kernel equality nor cancellation. Next transport
that partition identity into native unit charts and weighted box values.
The weighted monomial patch matching, measured residual presentation,
hyperplane reduction and final induction remain.


## Concrete measured rank-layer design

Avoid transporting a recursive measured RV coproduct through all degree
casts. Reuse the existing unmeasured rank-layer RV object and its exact
top/lower native atlas, and prescribe its combined weight by gluing the
native Gamma weight forms over that finite disjoint atlas.

The weighted rank-layer record should store the same fields as the old
rank layer (within_degree, topCount, native residue/gamma arrays, lower
list of **unmeasured** native charts, lower_rank), plus top full Gamma
weights and proofs, and lower_weight/lower_weight_definable indexed by
Fin lower.length. The lower weight at j has the exact Gamma arity of
lower.get j. Its unmeasured projection is therefore literal, retaining
the old topMap and lowerMap with no list-map or arity casts. A lower
measured chart is simply the record containing lower.get j and its
stored full weight. Normalizing a measured native-chart list into this
record uses the old induction: top entries use the common RES degree
k-m, and lower cons entries store Z.underlying::lower with dependent
Fin.cases for their weight and its proof. Keep the lower value as a Fin
sum, which simplifies the cons identity.

`GammaGroundWeightGluing.lean` is being checked as a generic finite
injective-atlas gluing theorem for genuine Gamma-ground volume forms.
Its graph is the finite union of the images of a_i.pair w_i; source
image disjointness and a_i injectivity prove functionality. Use it on
the sum index Fin topCount plus Fin lower.length, with the original
unmeasured atlas maps and each measured native chart's nativeForm.
Define the weighted layer object as the old unmeasured RV object
withCombinedWeight the glued form. Its underlying object is then
definitionally the old one. The gluing equation and nativeForm_value
give the exact topMap/lowerMap weight formulas.

`MeasuredNativeImagePartitions.lean` is being checked: an injective
native chart with the exact ambient weight formula has the measured
RV class of its actual image, and finite disjoint image partitions
identify the full tensor sum. This gives the weighted layer value-image
comparison and the actual measured RV isomorphism from equal images.
Apply the already checked weighted square match cover, the old lower-
arity cover and the old atlas cover to obtain finite weighted rank-layer
covers, and combine forward/inverse matrices as in the unmeasured proof.
`MeasuredSourceGridMatching.lean` selects using the **weighted** cuts and
only then forgets to the existing geometric source matching; its positive
measured congruence is retained.

For residuals reuse GammaGroundTensorRankLayerMatchedFamily on the literal
unmeasured projection. Define the measured residual chart at c by taking
the existing E.residualChart c as its underlying chart, then define its
full Gamma weight by cases: the parent top weight on top residual cells,
and lower_weight j on the old lower charts. This gives exact, rather
than propositionally cast, sources for the already checked residualMap,
its injectivity, disjointness and cover. Restrict the weighted layer RV
object to E's actual complement. Its underlying domain is literally the
old E.residualObject domain. The parent weight formulas give the exact
ambient weight on each residual map, so the measured native-image
partition theorem supplies the residual tensor image. The old actual
residual bijection, with its agreement with the original global map,
then preserves inherited weights. No matched sum is cancelled.

The remaining weighted algebraic part is parentwise positive residual
reassembly with each parent's full Gamma weight, and weighted hyperplane
reduction. For the latter, transport the full weight by the unimodular
Gamma coordinate change, absorb the fixed old-ground prefix using a
finite measured Gamma object of combined weight one, and substitute
that prefix into the residual full weight function. The new RES factor
still has combined weight one and has its degree increased by one.
At Gamma arity zero absorb the actual finite measured Gamma factor with
its full form into measured RES and use its positive RV embedding.
Then the rank induction and total-degree reassembly follow the completed
unmeasured proof. This remains unfinished proof work, not an input.


## Checked measured rank-layer implementation (830-module receipt)

The design above is now implemented and audited in
MeasuredTensorRankLayerNormalForm, MeasuredTensorRankLayerAtlas,
MeasuredTensorRankLayerMatchCovers, MeasuredTensorRankLayerTwoSidedCovers,
MeasuredRankLayerSourceMatching, MeasuredRankLayerResidualCovers,
MeasuredNativeBoxResidualPartitions and MeasuredRankLayerResidualAtlas.
GammaGroundWeightGluing and MeasuredNativeImagePartitions are included.
The weighted residual value split is a literal positive tensor equality;
the complement presents the inherited measured RV object. The remaining
weighted hyperplane/rank-induction/degree steps are unfinished, not inputs.


## Completed measured assembly and quotient — 2026-11-12

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
