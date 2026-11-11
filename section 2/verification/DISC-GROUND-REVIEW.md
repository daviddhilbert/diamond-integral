# Finite DC-ground proof review

Corollary 2.30 with a fixed finite DC ground tuple — independent proof review

Main text read independently: reference/diamond_integral_revision_annotated.tex,
part:rv:cons. The proof has a uniform good-disc predicate, type-local atomicity
via2.25/2.29, two compactness steps, Boolean refinement, and full tagged graphs.
Referee R031 is commentary and was not used as a mathematical premise. No new
main-text change was made. The approved TeX hash remains b2e68432e60db8c288cc10c5cd11a74bb0b41f24a3249cd5e31bdf54e4bdf98d.

NamedDiscCompactness: a presentation of the fixed old DC tuple is used only
for an auxiliary saturation base. Every original DC-definable set is raw
first-order definable over that same auxiliary base by real/Gamma transitivity.
The two finite name tuples keep this base small at any infinite saturation
cardinal. Finite subcovers are selected from ORIGINAL DC-definable members;
no arbitrary set over a chosen centre is descended. The final corollary makes
aleph0 <= kappa explicit. This expresses the standing sufficiently saturated
context; it is additional to the older real-only wrapper's printed type.

DiscTupleOperations: the entire Gamma-code and old-centre tuple stays free
while a uniformly first-order set operation is applied to each relation row.
Proper-code and output-sort guards remain explicit. Gamma representative
invariance follows from equality of input rows; actual DC invariance follows
from original R.fibre_eq_of_names. The output equality is proved before
specialization, not inferred from one named presentation.

ParametricTaggedPolydiscs / NamedGoodTaggedCodes: uniformity is quantified
over ALL raw tags. A nonempty tagged image must have its tag in every source
row, and every tagged image must be a singleton or an open-disc code (an
improper open code represents the empty image). RV-injectivity later gives
unique branches. This first-order formula is equivalent to the manuscript's
bounded finite-disjunction formulation in its finitary setting; it needs no
chosen enumeration of tags or global uniform bound as an extra input.
The same formula operates on all presentations of the old DC ground names.

NamedTypeCompactness: type locus includes the VF sort guard and all original
DC-formulas containing u. Sorted complement proves it decides every such
formula. Bad codes include their proper D guard and a witness outside C.
Projection proves original-DC definability. If all finite type fragments fail,
these bad-code sets cover D minus P; finite subcover contradicts inclusion
in the intersection of the selected fragments. The second compactness step
covers A by good original-DC neighbourhoods. NamedTypePartition constructs
nonempty Boolean atoms, proves disjointness/coverage and same-base formulas.
No good-partition or type-local-good assertion is assumed by the final result.

NamedTypeGoodDiscs applies the now-proved DC-ground2.25 to each open polydisc
inside the original-DC type locus. Its new disc names are appended; old names
are pulled back unchanged. DC-ground2.29 supplies the tagged branches and
point/open shapes. The raw good-code condition is then a direct consequence.
Only the four already-registered unary [18 section3] inputs occur: unary disc
atomicity, atomic Gamma base change, unary open-disc RV base change, unary
open-disc image geometry. No multivariable2.25/2.29/2.30 is assumed.

NamedGoodBranches constructs each full graph as source-polydisc membership,
original F membership, and rv(y)=actual tag. Old DC ground names, new polydisc
names and tag are all explicit. Finiteness comes from one finite row; every
row is reconstructed exactly. Constants are actual VF values, including zero.
Absent tags, empty finite values and zero VF source coordinates are allowed.
The total functions outside their supported source are arbitrary; definability
is asserted for their actual full supported graphs.

NamedFinitaryPartition exports corollary_2_30_disc_names. The partition is
original-real-plus-old-DC definable. Branches add only the new polydisc names
and actual RV tag. Theorem types retain canonical ACVF00, nontrivial ground
Gamma, genuine infinite-cardinal saturation and ground smallness. General
infinite DC parameter sets and the whole-field/improper disc code are not
silently included in the finite-radius chart interface. A source formula has
finite DC support; no general-purpose infinite-imaginary-base theorem is
claimed by this section's implementation.

Final audit PASS: 850 public section theorems / 378 selected reuse declarations,
section-2-final-disc-ground-verification.log. Full exported types were inspected
for 2.25 closed Γ∞, 2.29 and 2.30, including the branch-decomposition definition.
Only propext, Classical.choice and Quot.sound occur. Accepted interface count
stays9. No numbered target remains within the recorded COVERAGE.md scopes.
