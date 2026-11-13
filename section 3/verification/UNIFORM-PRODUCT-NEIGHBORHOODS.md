# Original-ground local product comparisons

These are supporting lemmas for the reverse positive kernel inclusion
in corrected Proposition 3.18. Both reverse inclusions have now been assembled at the explicit
Gamma-ground scope; see the final checkpoint below. General imaginary-
ground presentation transport and final manuscript adoption remain separate.

## Coefficients and their values

`RealTupleParameterAbstraction.lean` abstracts a finite tuple of real
names into variables in a complete first-order relation. Its interpreted
presentation version retains all code representatives, and its mixed-base
version keeps the old Gamma names. `GammaGroundFunctionalRelations.lean`
constructs the definable unique-fibre locus and its actual definable
function. `GammaGroundPointUniformization.lean` combines them: a point
definable over B(r) becomes a definable partial function of r over B.
The result supplies actual maps, without an old-B RV point as an input.

`RESCoefficientNeighborhoods.lean` applies this to the generic monomial
coefficients over B(r). The actual singleton value image is finite,
so its coordinates are Gamma-definable over B(r). For r in a RES domain,
the proved residue/Gamma closure invariance removes r from those value
definitions. Restricting the coefficient function to the corresponding
value fibre gives a definable subset through r, with constant value tuple
Gamma-definable over B. The coefficient itself remains a function of r.

## Uniform product neighbourhoods

`GammaGroundCompactness.lean` proves finite-cover compactness for any
interpreted finite-tuple presentation over a small mixed real/Gamma
base. Common real representatives of old Gamma names occur only inside
the compactness proof. The finite family in the conclusion still consists
of the original-base definable sets from the given family.

`GammaGenericFiniteCover.lean` covers the complement of Gamma-independent
points by proper nonzero integral-character hyperplanes with old-ground
Gamma-definable constants. Adding these sets to any definable cover of
the generic locus and applying compactness gives a finite positive cover
by the original neighbourhoods and finitely many such hyperplanes. This
also works with arbitrary retained RES parameters in the source space.

`ResidueGammaProductNeighborhoods.lean` selects a rectangle through any
point of an actual mixed RES/Gamma definable relation, using the existing
finite rectangle decomposition. For a definable bad set in RES x RV^m,
it projects the bad set to RES x Gamma^m. If one whole value fibre is free
of bad points, the complement of this projection contains its RES/Gamma
point and hence a definable rectangle. This proves uniform avoidance on
the whole product rectangle, over exactly the original ground.

`RVGenericResiduePoints.lean` proves that a finite-value-support target
forces every row of a generic monomial exponent matrix to vanish. The
residue output is consequently a point definable over the map base.
`RVGenericFibreJointInjection.lean` proves unimodularity for a free
coordinate map jointly injective with such a residue output: on the
full generic value fibre the residue component is constant, so the free
component is injective. `RVProductFibreMonomials.lean` specializes both
facts after fixing the retained residue input. Coefficients are over
B(r), not silently descended to B.

`RVProductFormulaNeighborhoods.lean` encodes the original domain and both
output formulas in one graph relation. Its definable bad-set argument
extends the full-fibre formula to an original-base product rectangle.
`RVProductMonomialNeighborhoods.lean` combines the actual generic-fibre
monomial theorem, coefficient uniformization, constant old-ground values,
and that product extension. Its conclusion has a fixed unimodular integer
matrix and actual RES-dependent coefficient/output functions on an
original-base rectangle through the given generic point.

## Remaining assembly

`AffineProductResidueInjection.lean` proves that the residue output on
such a rectangle is injective, by surjectivity of its unimodular map on
the full value fibres and joint injectivity of the original map. Its
actual definable image therefore supplies the corresponding RES
isomorphism. The integrated build and audit pass through these local
steps (731 supporting modules and the Section aggregate, 2190 public
theorem types, standard principles only).

The global positive proof still needs the rectangular source/target
comparison assembled across the original product charts, finite disjoint
product refinement compatible with the actual RV bijection, and induction
assembling the tensor congruence. The local arity inequality itself is
now proved by `RectangularMonomialFibres.lean`, `RVGenericFibreArity.lean`
and `RVProductFibreArity.lean`: a full generic fibre jointly injected
with a RES output cannot have fewer free output coordinates.

`IntegerCharacterBasisReduction.lean` and
`IntegerCharacterFirstCoordinate.lean` put a nonzero integral character
into the first row of an integral basis, up to a nonzero integer multiple.
`GammaHyperplaneCoordinates.lean` proves that the resulting fixed Gamma
coordinate is old-ground definable, using its actual unique nonzero-power
root set. `GammaGroundIntegralMonomialImages.lean` constructs the genuine
Gamma monomial isomorphism and its full RV-code lift. Its image retains
the actual Gamma classes, without selecting an RV point over the fixed
Gamma value. `GammaMonomialHyperplaneImages.lean` combines the coordinate
normalization with that positive Gamma class equality.

`GammaFixedPrefixProducts.lean` identifies the actual fixed-prefix set
with a product of a finite Gamma point and the remaining coordinate set.
`TensorFiniteFactorAbsorption.lean` moves any finite Gamma factor to RES
inside both positive tensor products; this retains arbitrary measured
forms and includes degree zero. Finally,
`GammaHyperplaneTensorReduction.lean` gives the unmeasured one-coordinate
rank reduction by these genuine Gamma isomorphisms and positive
balancing, preserving total degree. The latest integrated build and audit
pass for 742 supporting modules and the Section aggregate, with 2215
public theorem types and only standard principles.

The measured proof additionally needs its actual form normalization and
the shared degree-zero weight-shift comparison. No cancellation of
semiring classes or HK input is part of these arguments.


## Finite positive assembly infrastructure

The full-audit checkpoint is now 810 supporting modules plus Section,
2483 theorem types, 2055 definitions, 151 named instances and 8 reused
heads. `RVProductFiniteMonomialCover.lean` gives finite original-ground
patch covers with actual product image bijections. The complementary
lower-arity branch theorem is in `RVProductLowerArityCover.lean`.
`TensorBooleanCells.lean` proves the finite disjoint product partition
identity in the positive tensor using a common Boolean grid.
`FiniteHyperplaneTensorReduction.lean` handles finite exceptional covers,
and `TensorRankZero.lean` proves the base case. The complete unmeasured global matching, residual comparison, rank
induction and degree reassembly are now checked, giving the exact positive
kernel and quotient semiring isomorphism. The measured form comparison
and reverse inclusion remain targets; see `POSITIVE-KERNEL-ASSEMBLY.md`.


The unmeasured quotient now has a checked multiplicative direct-sum grading
with the original total degree on pure tensors. For the measured proof,
RES combined weights have finite old-ground-definable images and normalize
positively by shared degree-zero measured Gamma scalars. The 799-module
receipt includes these steps; subsequent normalized single-piece and
weighted local comparisons are tracked separately in STATUS.md.


The 810-module audit now includes the full normalized measured single-
piece normal form, genuine weighted Gamma code descent, weighted
unimodular monomials, tuple translation generation and the normalized
weighted local product congruence. Actual measured native charts and
finite RES/Gamma partition identities keep all degrees and forms. The
global measured reverse inclusion is still unfinished.


## Both complete positive kernel comparisons

The 842-module integrated receipt audits 2566 theorem types,
2116 definitions, 151 named instances and 8 reused heads. The weighted
local matches, actual residual forms and bijection, finite hyperplane
reduction, rank-zero base, rank induction and degree reassembly now give
the exact measured positive kernel as well. Both positive quotients have
checked multiplicative direct-sum gradings and their original r+n object
formula. TensorPresentationContext supplies actual GammaGroundContext
wrappers. No HK premise, cancellation or groupification occurs. General
imaginary-ground presentation transport remains separate.
