# Local RV normal-form proof route

This is a proof-development note, not an additional accepted input or a
claim that Proposition 3.18 is complete. No manuscript edit is proposed.

A true guarded rational-normal-form clause carries the actual domains of
all flat residue-polynomial summands. On nonzero RV tuples, write each
monomial as its constant coefficient times an integral character. Summands
with zero coefficient vanish identically. For the others, the residue
domain forces one fixed Gamma value of that character.

Partition by whether the two nonzero outer monomials of each equality have
the same value. On an equal-value cell, retain the outer-ratio character.
On an unequal-value cell, the equality forces both residue factors to
vanish. Orders only use coordinate Gamma values. Collect the finitely many
active characters. Smith normal form turns their integer span into
coordinates with finite value support; torsion-free Gamma ensures that
finite support of a nonzero power gives finite support of the coordinate.
The basis change is an actual original-ground monomial RV bijection.

Angular invariance, the finite disjoint value-pattern refinement and the
same-real-ground mixed residue/Gamma quotient are proved. The checked
arbitrary-tuple rectangle theorem supplies the product factors. Gamma coordinates of active residues
are determined by the residues themselves. The remaining full Gamma fibres
then supply the product factors. Zero-coordinate strata and the original
RV[k] finite-to-one labels must be retained in the categorical assembly.

A Gamma-parameter specialization may be used inside the existence proof,
but its chosen RV representatives must not occur in the final ground.
Integer exponent vectors and basis matrices are parameter-free. Recover
Gamma value-cell thresholds over the original ground using the checked
residue-tuple Gamma closure elimination for the code representatives, each
in its old-ground definable single-value fibre. Define the final quotient
relation from the original RV set and the parameter-free coordinate maps.
It is not defined using an angular representative.

After object decomposition, tensor injectivity still needs invariance
under actual RV isomorphisms and decreasing Gamma dimension. A bijection
of whole generic tori must force integral unimodularity, including the
residue roots-of-unity obstruction in characteristic zero. This is a local
proof obligation, not an assumed HK rigidity result. The measured proof
must also preserve its Jacobian/volume equations and retain finite and
degree-zero Gamma forms.


For a finite disjoint partition, refine by the value status of every flat
monomial summand in every literal, as well as by outer-value equality.
A finite cover by true guarded clauses alone does not automatically give
a disjoint product partition after different monomial basis changes.
The released residue addition has an exact junk-zero branch. Prove its
selective congruence: matched residue/nonresidue status and equality of
actual residue summands suffice to preserve a flat total sum. On each
global finite value pattern, only characters of residue summands with
nonzero coefficients are active. This strengthens angular invariance to
all raw literal truth values and allows arbitrary Boolean formulas on one
fixed pattern. The explicit domains and guards remain in the original
formula; total semantics is an internal proof device, not a manuscript
change or an unguarded reinterpretation. The global value-pattern cells
are disjoint, so their product decompositions can be assembled using
positive scissor relations. The finite disjoint geometric construction is now checked at the real-base
scope. Original-Gamma-ground product assembly and RV[k] degree transport
remain distinct obligations.


## Checked geometric construction after the 580-module checkpoint

`RVNonzeroProductNormalForm.definableRV_nonzero_product_normal_form`
constructs actual finite pairwise disjoint source pieces for a definable
nonzero RV tuple locus, residue factors with finite Gamma support, full
Gamma-preimage factors, and same-base definable bijections. Each product
chart records that its two ambient arities add to the original ambient
arity. The theorem assumes a canonical structure, actual saturation at an
infinite cardinal, ACVF00, a small real base and a nontrivial Gamma value
definable over that real base. Its ambient arities are **not** RV[k] label
degrees. It does not yet certify surjectivity of the graded tensor map.

`RVGroundAngularPartition.gammaGround_finite_angular_partition` proves the
angular partition over the original real/Gamma base. This uses the actual
common-name DNF only inside the proof. Nonzero coefficient values descend
by `RVCoefficientNames.rvMonomialCoefficient_value_original_ground`, and
`RVGroundValuePatterns.globalGammaPattern_definable` defines every value
pattern over the original Gamma ground. Zero coefficients are retained as
separate branches. No chosen Gamma code is a final parameter. This theorem
supplies original-ground angular cells; the actual mixed quotient and
product-bijection APIs now also retain that ground.

The complete 601-module build and audit pass for these additions (1937
public theorem types; 3865 audited heads).
Later Gamma-ground code-logic drafts are outside that source snapshot.


The 613-module receipt checks
`GammaGroundRVNonzeroProductNormalForm.gammaGroundRV_nonzero_product_normal_form`.
It constructs all the geometric product charts over the original mixed
base, assuming its real and Gamma supports are small and its Gamma closure
is nontrivial. Only the nonzero input locus is covered. The chart's ambient
arities add to the source ambient arity; no RV[k] label-degree conclusion
is asserted. The next rank-extension lemmas select algebraically independent
points in full Gamma fibres for degree transport, not definable points.


The 623-module receipt checks the full-domain geometric theorem
`GammaGroundRVProductNormalForm.gammaGroundRV_product_normal_form`, including
zero RV coordinates via an injective code and a return to the original
source pieces. `RVProductDegreeBound` proves the residual rank budget from
a finite RV[k] label. `RVProductRESFactor.gammaGroundRVProduct_RES_factor`
constructs an actual RES[k-m] factor over the same ground. Its earlier
exchange/Gamma algebraicity records are discharged by checked [18] exports
in the next tensor-chart adapter. The full Gamma-unit factor has a proved
bijection with the paper's literal Gamma-to-RV lift. Finite scissor assembly
of these chart preimages is in progress; injectivity and the measured
equations are still separate work.


## Injectivity route after the 663-module checkpoint

Both actual positive tensor maps and their group-completed maps are now
proved surjective locally. The next geometric step is generic fibre
comparison, not an assumed normal-form uniqueness. Independence of a Gamma
tuple is expressed by the absence of nonzero integral characters with
old-ground Gamma-definable value. Active angular-coordinate values are
old-ground definable, so an angular cell containing such a tuple has no
residue coordinates. Consequently every same-ground definable subset of
its value fibre is empty or full. The checked finite Gamma-function cover
also makes Gamma-valued maps constant on that fibre. Residue-valued maps
are constant by naming the residue output, using the proved elimination of
finite-value-support RV parameters, and applying fibre invariance again.
These statements persist after fixing a residue input in a product chart.
They do not assert existence or density of independent Gamma tuples.

For a generic source fibre mapping into one target product chart, fix its
residue output. Its remaining coordinates give a finite-to-one map into
the target free RV tuple. The existing full-Gamma rank extension proves
that its free arity cannot drop. At maximal free arity, a nonzero target
character with old-ground value would create an additional residue output;
Smith reduction and the same arity bound should rule this out. Apply the
same argument to the inverse map to obtain a bijection of entire fibres.
Then use same-ground residue/Gamma rectangles and a decreasing-arity
exception argument for tensor invariance. Finite Gamma coefficient factors
must absorb changes of residual parameter values: a lift over an auxiliary
residue point cannot simply be treated as a lift over the original ground.
Generic integral monomial-map rigidity and this descent remain to be proved.


The 672-module full build and audit pass (2066 public theorem types;
4061 audited heads) for the generic-fibre and arity lemmas above. The
subsequent integer-character rigidity drafts use Smith bases and actual
residue roots of unity: injectivity on one full value fibre detects power
kernels in the embedded residue torus, so the square exponent matrix must
be unimodular. Pure group-algebra lemmas keep the power-kernel condition
explicit; the ACVF adapter proves it using characteristic zero and the
actual algebraically closed residue field, rather than assuming HK 3.26.
This draft checkpoint does not assert that every definable generic-fibre
bijection has yet been put in this integral monomial form.


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


A second route to generic matching arity is now in development. On an
angular chart, the original input values are old-ground definable
coefficients times integral monomials in the free Gamma values. Fewer free
values than independent input values would leave a nonzero integral left
kernel character. Smith reduction of the column span constructs that
character directly over the integers. Its input value would be old-ground
definable, contradicting independence. The actual finite label gives the
reverse arity bound. Together these justify the square-block hypothesis
of the checked monomial rigidity theorem, rather than assuming it.

For the next descent step, split the residue factor by its finite value
tuples. Within one fixed value tuple, an injective affine-monomial input
map with a unimodular free block can have at most one residue point: adjust
the free coordinates by the integral inverse to equalize the inputs.
Their values stay unchanged, so both adjusted points remain in the same
full fibre. Injectivity then identifies the residue points. Such a
singleton residue fibre is original-ground definable. This is intended
to recover the actual original-ground RV coefficients of a generic graph
map; it is not yet a completed tensor-injectivity argument.


Do not confuse the conditional generic-Gamma fibre comparison with the
remaining finite-Gamma/residue-torus cases of the coefficient embeddings.
A named Gamma tuple may have no coordinates independent over the full
mixed ground, while its RV fibre still has full residue dimension. The
finite-factor descent and fibre matching must handle those cases directly.
No existence of generic tuples over a base already naming them is asserted.


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


After the 703-module checkpoint, the next assembly targets actual maps on
nonzero RV tuples. `GammaGroundRVUnitGraphs` supplies their graph tuples,
finite input labels and injective coordinate projections. Partition that
graph over the original base. At a Gamma-independent input, the checked
arity theorem and graph-block theorem give a square unimodular input
block. Choose a product rectangle containing the graph point. Its residue
factor is finite by exhaustion of the input label degree, and every point
is individually old-ground definable by the singleton-fibre argument.
The checked output formula then gives an integral monomial with actual
old-ground RV coefficients. Unimodular input inversion carries the whole
input value fibre through that same residue point, so the formula must
hold on the full input fibre, not only at the selected graph point.

For categorical descent, the existing
`GammaGroundGammaHom.ofCodeBijection` needs preservation and reflection
of the complete decoding kernel. Convert the actual unit preimages to the
full Gamma code presentation and apply that theorem. An affine monomial
bijection with a unimodular matrix preserves and reflects value equality;
this is to be proved directly using the same integral inverse. This gives
local Gamma morphisms without selecting a Gamma section or enlarging the
ground. Finite/low-free-arity tensor matching remains separate.


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
