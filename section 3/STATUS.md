# Section 3 status

The §3 formalization is complete in the documented paper contexts,
relative to the expressly accepted cited results. This includes both
corrected positive tensor presentations, both ordinary horizontal
positive monomorphisms, both full-ground affine-classification statements,
the actual degree-zero equivalences, and the stated integral comparisons.
The later [18] geometric kernels and approved R--Y classification remain
explicit replaceable inputs. No HK result is a given input.

The latest complete integrated check passes across 1,003 supporting modules
and 5,324 declarations. A separate semantic review links 21 manuscript
targets to 119 actual audited declarations; the verified receipt includes
that coverage record. See `verification/paper-targets.json`.
The adopted manuscript is unchanged. Independent disc-name extensions and
the concrete bounded categories of §4 are outside this §3 certificate.
T001/C002 and the four reviewed mathematical corrections are adopted;
minor existing editorial annotations have not been silently resolved.

Started from `diamond-integral` main `82fe1a127def2c24ca32a97935ff3de3f732a84c`.
The original checkout was `7b9e71f`; it was clean and fast-forwarded before
work began. The author has now authorized committing and pushing the
audited §3 work; the earlier no-push notes below are historical.

## Manuscript review protocol

Review one or two correction items at a time in manuscript order. Show only
an actual PDF in the right panel, with proposed wording in a different
color inside the manuscript context. Wait for the author's reading and
comments. After approval, incorporate the change, gray out its referee
item and add a brief resolution note. Do not open the TeX editor or replace
the manuscript review with a separate summary. This is also recorded in
`../AGENTS.md`.

## Approved: R050 / Remark 3.15

The author approved the R050-only PDF. The working manuscript now says
“piecewise Z-affine” in ordinary main-text color. Its restriction on
translation constants and the following piecewise GL(Z) characterization
are unchanged. The original R050 note is gray, with a brief green author
resolution. The original proposal PDF is preserved; the adopted change is
recorded in `reference/proposed-revisions/R050-approved.patch` and
`R050-approval.json`. The approved extract is
[R050-resolved-review.pdf](reference/proposed-revisions/R050-resolved-review.pdf).

## Approved: R051 and R053

The author approved the focused R051/R053 PDF on printed page 35. The
working manuscript now uses the correct spellings of homogeneous and
nonhomogeneous and states the existing (VF,Gamma)-generation hypothesis
before both lift homomorphism assertions. The lift on individual objects
is still distinguished from descent to isomorphism classes. Both original
referee notes are gray, with brief green author resolutions. The R053
resolution retains the approved nontrivially valued ground-field variant
of the definable-point obstruction.

The exact adopted change is `reference/proposed-revisions/R051-R053-approved.patch`;
`R051-R053-approval.json` records the review and before/after hashes.
[R051-R053-resolved-review.pdf](reference/proposed-revisions/R051-R053-resolved-review.pdf)
shows the approved passage. Its original proposal is preserved.

## Approved: R054 / manuscript review complete

The author approved the R054-only PDF. The measured superscript is now
incorporated in Theorem 3.22's characterization. The original R054 note is
gray with a brief green author resolution. The measured congruence and
lift-class equality are unchanged. Exact adoption and source hashes are
in `reference/proposed-revisions/R054-approved.patch` and `R054-approval.json`.

The four reviewed §3 items R050, R051, R053 and R054 are now resolved by
author approval. R052 was withdrawn in the supplied report. No manuscript
approval is pending. The original proposal PDFs remain as review history.
The author now requests sustained work on the actual formalization.

The §3 main statements were checked independently before the referee
annotations. `abs_not_affine` proves the algebraic obstruction behind R050.
For R053, `definableBijection_has_point_iff` proves the invariant needed in
the nontrivial-ground variant. Its Lean corollary does not itself construct
a particular model or parameter structure realizing that example.

The main manuscript and focused review PDFs compile locally using
unmodified TeX support files in `.scratch/tex-support`. Three passes
stabilize references. Only the actual PDF is requested in the right panel;
queued display is not reported as confirmed visibility.

## Earlier implementation milestones (superseded by the completion review)

The Gamma and measured Gamma constructions now include genuine coproducts,
partitions, product arrows, symmetry/associativity/unit and distributivity
with full RV code witnesses. Positive equality is exactly an actual
isomorphism, every positive class has an object representative, and each
universal semiring presentation is equivalent to the genuine graded direct
sum. Finite Gamma and finite measured Gamma have the corresponding
comparisons and injective positive inclusions. Full measured forms remain
present, including at degree zero and on finite objects.

`CompletionDirectSum` proves that additive group completion commutes with
these direct sums without assuming cancellation. `GradedGroupComparisons`
and `MeasuredGammaGroupComparisons` give the actual homogeneous generator
formulas. `MeasuredVFGroupComparison` supplies the analogous additive
grading relative to the two accepted measured lift records. These additions pass the integrated project build and declaration audit
across 228 supporting Lean modules. The ordinary VF group colimit, the
complete RV correspondence and its Jacobian abbreviation, and the RV
projection normal form are included in that audit.

The complete project build and declaration audit pass on Lean 4.35.0 at the
recorded dependency pins. The current receipt covers 774 theorem types,
926 definitions/structures/abbreviations, 82 named or groupoid typeclass
instances and eight reused declarations. Only the permitted standard logical principles occur.
This is local verification; nothing has been committed or pushed.

- `RVDimensionBridge` identifies the nonzero-target §2 RV dimension with
  the companion finite-map dimension, without increasing the target arity.
- `RVFibreDimension` includes bottom on the empty set, bounds every original
  VF fibre over the exact base obtained by naming that VF tuple, proves
  attainment, and proves Lemma 3.3 at a small real base using checked RV
  exchange. It does not assume fibre-dimension invariance.
- `VFDimensionBridge` and `VFDimensionComparison` identify §2's interior
  dimension with the companion dimension on nonempty definable sets and
  compare all upper bounds, including empty sets. The valuation must
  realize the actual model predicate. Positive-degree smallness is exactly
  the paper's smallness; at degree zero small means empty.
- `EssentialVFMap`, `EssentialVFGerms`, `EssentialVFMeasure`,
  `MeasuredVFPositive` and `MeasuredVFZero` implement genuine essential
  representatives, their agreement quotient and the measured groupoids.
  The positive-degree quotient agrees with the paper's co-small agreement
  relation. The zero-degree category retains the actual Gamma form.
- `FiniteFamilies`, `CodePresentations`, `GammaCategories` and
  `GammaVolumeCategories` retain disjoint-union tags and complete Gamma
  imaginary presentations. A Gamma morphism requires a definable RV
  representative contracting to it; arbitrary Gamma bijections are not
  silently admitted. The combined-weight formula is proved pointwise.
- `RVScissors`, `VFScissors`, `GammaScissors`, `MeasuredRVScissors` and
  `MeasuredVFScissors` give genuine fixed-degree additive scissor quotients
  and groupifications, with the original labels and inherited forms.
- `RVProducts` gives actual cartesian products and finite nonzero target
  maps and proves preservation of finite RES value support.
  `RVSemiring` gives the universal positive semiring presentation using
  these products, same-degree bijections and genuine scissors. Its
  comparison with the direct sum of the fixed-degree quotients is proved
  in `RVGradedSemiring` and `RVGradedComparison`. Each positive class has
  an actual same-degree object representative, and class equality is
  equivalent to an original-base definable isomorphism.
- `RESCoproducts` proves that genuine disjoint unions preserve finite
  source-value support and that fixed-degree RES classes inject into RV.
  `RESGradedSemiring` constructs actual graded products and proves the
  graded RES inclusion is an injective semiring homomorphism.
- `RVZeroStrata` partitions zero-allowed targets by their exact zero
  pattern, producing nonzero targets in degrees at most the original one.
- `GammaRVCodeLift`, the `RVFamily` modules and `GammaRVLift` realize
  every finite Gamma family by its full nonzero RV codes with explicit
  finite tags. `GammaCodeRestrictions` and `GammaRVScissors` prove
  scissor descent. `GammaRESLift` and `FiniteGammaScissors` construct
  the actual fixed-degree commutative square. `RVFamilyProducts`,
  `GammaRVProductCodes`, `GammaRVProductLift` and `GammaSemiringLift` now
  prove product and unit compatibility for the actual lift and induce its
  positive semiring map. Gamma-map injectivity remains open.
- `GroupifiedCongruences` proves that completion of a semiring congruence
  quotient is quotient by the ideal of its generator differences. It gives
  the distinct principal ideals for the unmeasured and measured pairs.
  `RVGenerators` instantiates the unmeasured relation with the actual
  degree-one point and strictly positive-value domain. This proves the
  algebraic comparison, not either geometric HK kernel.
- `RVFormGraphs` identifies the invariant graph interface for RV volume
  forms with genuine maps to the Gamma imaginary. `MeasuredLifting` gives
  the actual measured object lift in every degree, with exactly the
  pulled-back volume form. Class descent and surjectivity remain separate.
- `VFProducts`, `VFSemiring` and `VFFiltration` give actual products,
  the filtered semiring presentation and bound-raising additive maps.
  `VFCoproducts` and `VFPositiveComparison` prove genuine fixed-degree
  representatives, positive equality exactly when an actual definable
  isomorphism exists, and injectivity when forgetting a dimension bound.
  `VFSemiringComparison` identifies the filtered presentation with the
  companion positive quotient of all finite-RV-fibre mixed domains.
  `VFFilteredComparison` proves every inclusion and bound transition
  injective, and exhaustion by actual objects. `VFPositiveColimit` and
  `VFPositiveColimitCategory` prove the universal property and the actual
  categorical colimit in additive commutative monoids.
  `MeasuredVFData` is equivalent to the original separate degree-zero and
  positive categories; `MeasuredVFProducts` and `MeasuredVFSemiring` use
  those original genuine/essential groupoids and actual product forms.
- `MeasuredRVSemiring`, `MeasuredRESSemiring` and `MeasuredRESInclusion`
  give measured presentations and the genuine RES forgetful semiring map.
  `MeasuredRVIsomorphismClasses` and `MeasuredRESPositiveComparison`
  prove that fixed-degree equality is exactly a pointwise measured
  isomorphism and prove positive RES injectivity. The measured product-law
  and graded-comparison modules identify both presentations with the
  genuine direct sums and prove the graded measured RES inclusion injective.
- `GammaProducts`, the Gamma/finite-Gamma semiring modules and their
  measured versions use actual coordinate concatenation and full forms.
  `MeasuredGammaRVLift` and `MeasuredGammaRVMorphisms` prove the object
  and pointwise measure-preserving arrow lifts, including finite RES support.
  `MeasuredGammaRVScissors` and `MeasuredFiniteGammaSquare` prove measured
  scissor descent and the fixed-degree commuting square.
  `MeasuredGammaProductLift` and `MeasuredGammaSemiringLift` prove actual
  multiplicative lift compatibility, including every combined weight.
- `BalancedTensor` and `BalancedSquare` construct the ordinary balanced
  semiring tensor map and prove its pure-tensor formula and uniqueness.
  `CompletionTensor` proves that additive ring completion commutes with
  this balanced tensor product. `FiniteGammaSemiringSquare` and its measured
  counterpart assemble the concrete multiplicative coefficient squares.
  `UnmeasuredTensorMap` and `MeasuredTensorMap` give the canonical positive
  tensor maps and their ring-completed maps, with the stated object formula.
  Neither tensor map is yet proved bijective.
- `GammaAffineClassification` records the accepted [19] contraction and
  unimodular-matrix classification at the source's VF-generated real base.
- `CitedUnmeasuredIntegral`, `CitedBoundedIntegral` and
  `CitedMeasuredIntegral` now use explicit replaceable [18] inputs against
  the actual semirings, special generators and object lifts. They prove
  positive and ring integral comparisons, characterizations and bounded
  unmeasured transition compatibility **relative to those inputs**, over
  a small VF-generated real base. See `verification/cited-inputs.json`.
  These do not independently compile [18], extend the base scope, or supply
  the remaining measured graded/direct-sum identifications.

The measured VF grading comparison has also been derived relative to the
explicit accepted [18] lift records. `MeasuredRVQuotientGrading` independently
proves that the homogeneous measured special relation admits a polynomial
degree marker. `MeasuredVFRelativeComparison` proves compatibility of the
global and fixed-degree lifts, injectivity of each VF inclusion and actual
representatives. `MeasuredVFPolynomialGrading` and `MeasuredVFDirectSum`
prove independence and exhaustion by degree. `MeasuredVFGradedSemiring`
transports multiplication while preserving the original direct-sum addition
and proves the actual cartesian-product and unit formulas, as well as the
ring-completion comparison. These results require both precise lift records
over the same small VF-generated real base; neither record is globally supplied.
The declaration audit now also includes explicitly named local instances.

The Gamma positive comparison is now independent of the pending HK inputs.
`CoproductIsoClasses` constructs the isomorphism-class additive monoid from
actual coproduct isomorphisms. The finite-family tag, coproduct, full-code
and partition modules prove those maps explicitly. `GammaTagIsomorphisms`,
`GammaCoproducts` and `GammaPartitions` retain full RV contraction witnesses
and prove that positive equality is exactly genuine Gamma isomorphism.
`GammaRepresentatives` proves coproduct addition and an actual representative
for every fixed-degree positive class, including families with empty pieces
and zero tags. These results do not imply Gamma-to-RV injectivity or either
tensor isomorphism.

These results currently use real parameter bases, with saturation and the
small-base bound visible where required. The Gamma/disc ground-name
extensions have not been silently included. No conflict with the approved
nontrivial-ground-value hypothesis has arisen.

## Current completion boundary

The local constructions and results now cover the paper's ordinary real/RV
and complete Gamma grounds, with actual VF/Gamma-generation exactly where
the lift and integral statements require it. The numerical Euler maps and
concrete bounded §4 categories are subsequent work. The accepted later
[18] geometric results and the approved [23] classification are kept as
precise input records. Already definable interpreted names have checked
transport; an independently named disc imaginary outside the default
paper context is not included in this certificate. The chronological
entries below preserve earlier milestones and superseded open items.

All four reviewed manuscript corrections remain approved and applied.
The cloud connection has interrupted execution several times; after it
reconnected the saved source files were present and the full build/audit
was rerun successfully. No local restoration by the author was required.


## Parameter-scope extension in progress

`ImaginaryParameters` now defines sets over an actual named imaginary as
fibres of complete real-base definable relations. The defining relation
contains every code of that imaginary. Boolean operations retain the same
name. A comparison with the existing real-base geometry is proved after
explicitly adjoining the coordinates of a chosen code. This comparison
makes no VF/Gamma-generation claim about the enlarged real base and does
not yet extend the integral statements to imaginary ground parameters.

The named-imaginary extension now has complete map composition, inverse
bijections, products, images, inherited restrictions and finite fibres.
Fixed-name RV/RES and pointwise measured RV/RES groupoids, plus RV scissors,
have direct builds and are included in the latest 201-module audit. Their
comparisons with a chosen real-code expansion are faithful and retain the
actual functions and measured weights. The VF groupoid and the object lift
are being extended in the same manner. These finite-name constructions do
not yet identify the full arbitrary ground structure or extend the cited
integral inputs. The outstanding HK source decision is described in
`verification/HK-INPUT-REVIEW.md`.

The Gamma-ground extension now covers arbitrary Gamma-name collections:
Boolean operations join finite supports, maps and their inverses retain
complete graphs, and already definable imaginary names can be eliminated.
The RV/RES groupoids have finite-support object theorems; the VF groupoid
uses the same actual dimension and finite-fibre conditions. Pointwise
measured RV/RES forms and the measured VF object lift retain degree-zero
forms. The current 228-module receipt includes the Gamma-ground constructions
through the RV semiring, VF scissors and measured VF object lift. Full
ground-scope integral and tensor comparisons are still outstanding.

The Gamma-ground unmeasured integral now has an explicit accepted-[18]
input and proved positive/ring consequences, object characterization and
uniqueness. This is a comparison of concrete universal presentations;
identification with the manuscript's grading and filtration is still open
at this scope. The actual mixed VF product and the point/positive-value
principal relation are implemented over the same ground. The RV-tuple
syntax bridge is proved. Measured RV objects now retain one common finite
Gamma support for their set, label map and full form, and their cartesian
product has the exact combined-weight formula. The integrated audit of
those additions passed: 800 supporting theorem types, 957 definitions,
82 named instances and eight reused declarations, with standard principles
only. This receipt precedes the further constructions described below.

The small-real interpretation now treats finitely many formulas and full
map graphs simultaneously, with a proved equality of their VF coefficient
field to the original field. It yields the actual VF point-rank criterion,
finite-map dimension inequality, bijection invariance of VF dimension and
invariance of literal finite RV fibres over Gamma ground parameters.
The latter does not assert invariance of arbitrary RV ranks under a chosen
real-code expansion. Actual mixed tagged coproducts and positive additive
representatives are proved. Bound-raising maps and the additive universal
property of the dimension filtration are implemented over the full Gamma
ground, together with categorical colimits in additive commutative monoids
and their group completions. The degree-zero measured VF groupoid retains
every Gamma form and genuine pointwise form-preserving bijection. Positive
measured essential arrows and the universal-semiring comparisons at this
scope remain open.

The 251-module integrated receipt checked the preceding constructions:
832 supporting theorem types, 983 definitions, 83 named instances and
eight reused declarations, with standard principles only. Further
Gamma-ground essential-map work now proves cofullness by independence
over the original VF field, constructs actual composites on the overlap
of the middle domains, and identifies equality of induced bijections
with agreement outside a same-ground definable set of smaller manuscript
VF dimension. The quotient essential groupoid is constructed without
assuming its category laws. Same-ground fixed-label derivatives and
Jacobian composition/inverse products at independent points are proved.
The generic-point measure equation is closed under identity, inverse and
composition, giving a generic measured groupoid with full Gamma forms.
Its identification with pointwise preservation on a definable cofull cut
is not yet proved; it is not reported as the completed measured VF
category or used as a substitute in the cited integral input.

The integrated build/audit through these essential and generic measured
constructions passed across 263 supporting modules: 854 supporting theorem
types, 1006 definitions, 83 named instances and eight reused declarations.
Only the three standard logical principles occur. No HK input has been
installed and no complete numbered result is inferred from this count.

The generic/pointwise measured-VF gap described above is now resolved over
the complete Gamma ground. `GammaGroundRawLogic` and `GammaGroundRawDescent`
retain full real-code relations in both directions, including finite real
tuple quantifiers. `GammaGroundDerivativeFormula` transfers the companion's
fixed-label full-derivative formula to this logic. Its determinant graph
is the graph of full derivatives; it is not equated with the existence of
partial derivatives at every point. `GammaTopPresentation` keeps zero
determinants visible in the volume equation. The resulting regular measure
locus and its fibre interior are same-ground definable. Every independent
point survives, so a generically preserving essential representative has
a pointwise preserving representative on a definable cofull subset with
the same germ. `GammaGroundMeasuredVFGerms` proves the actual quotient
comparison, the manuscript-dimension agreement criterion and the measured
groupoid laws. `GammaGroundMeasuredVFScissors` combines these positive
degrees with the genuine degree-zero groupoid and constructs their
scissor quotients. A new integrated verification is running for these
additions. The broader ground-context translations, Gamma-ground graded
and universal-semiring comparisons and integral specializations remain
separate obligations; the outstanding HK source question is unchanged.

The 278-module integrated build/audit passed through the pointwise measured
category and its scissors: 895 supporting theorem types, 1050 definitions,
83 named instances and eight reused declarations, with standard principles
only. The next additions construct the actual Gamma-ground measured RV/VF
cartesian universal presentations, homogeneous principal relation and its
ideal completion. `GammaGroundCitedMeasuredIntegral` formulates accepted
[18] global and degreewise inputs and derives positive, ring and fixed-degree
integrals, object characterizations and uniqueness. The bounded unmeasured
input uses actual finite direct sums and VF dimension-bounded scissors;
its transition compatibility uses additive generator extensionality, without
assuming object representatives for every Gamma-ground RV class. These
interfaces retain genuine VF generation and nontriviality of the full
Gamma ground. Their identification with all manuscript grading and
filtration presentations remains separate.


The next Gamma-ground comparisons now have direct builds. The homogeneous
measured special quotient has a polynomial degree marker proved on the
actual presentation, including its fixed-degree formula by additive
generator extensionality. The global and degreewise accepted lifts agree,
and each measured VF degree injects into the universal presentation.
`GammaGroundMeasuredVFDirectSum` proves that the direct sum of the actual
fixed-degree scissors is additively equivalent to that presentation.
`GammaGroundMeasuredVFGradedSemiring` preserves the existing addition and
proves the cartesian-product and unit formulas; its ring and group grading
comparisons retain both explicit accepted inputs.

`PresentationAdditiveNormalForm` independently proves that every universal
cartesian class is a finite sum of object generators. This gives the
surjective direction without a geometric representative or a grading
assumption. For ordinary Gamma-ground VF, the accepted global/bounded lift
compatibility proves injective bound inclusions and bound transitions.
The unbounded additive quotient is equivalent to the actual universal
semiring, and that semiring, together with its group completion, is now
proved to be the actual categorical colimit of the dimension filtration.
The product on the unbounded additive quotient agrees with actual object
products. These injectivity and colimit comparisons are relative to the
precise accepted global and bounded [18] records.

`GammaGroundSortedSyntax` extends the complete-code syntax comparison to
arbitrary finite sorted real tuples, including VF coordinates. It proves
an equivalence with GammaParameters.DefinableOverBase and does not name a
representative in the ground. An integrated audit of all 294 supporting
modules is running. Pure Gamma-ground RV/RES and Gamma graded comparisons,
the remaining affine and RV-fibre-dimension scope obligations, and the
Proposition 3.18 tensor isomorphisms remain separate. The HK source decision
is still pending; no HK input has been installed.


The 294-module integrated build and audit passed: 964 supporting theorem
types, 1112 definitions, 84 named instances and eight reused declarations
(2168 total), with the permitted standard principles only. The explicit
cited input records remain hypotheses of their conclusions; no HK input
or global custom principle has been added.


Further Gamma-ground RV constructions now have direct builds: definable
map unions preserve finite fibres; actual RV tags and inverse maps give
genuine fixed-degree coproducts. Every ordinary and measured fixed-degree
positive RV class has an actual object representative. Auxiliary definable
map categories have proved initial objects and binary coproducts. Their
actual cut decompositions give the isomorphism-class additive monoids,
and positive class equality is exactly a genuine same-ground bijection,
with the full pointwise combined weight in the measured case. No [18]
lift or HK input is used in those RV class comparisons. Products of genuine
RV bijections are constructed, and homogeneous ordinary RV multiplication
is independent of chosen representatives. The accepted degreewise lift
now also supplies an actual measured VF object representative of each
fixed-degree positive class. The actual graded/filtered integral composites
retain the accepted input records explicitly.


Gamma-ground RES now has actual product/coprod closure of finite value
support, inherited restrictions and its genuine fixed-degree scissors.
The ordinary RES classes have actual representatives, equality exactly
when a same-ground RES isomorphism exists, and an injective positive
forgetful map into RV. Measured RES keeps arbitrary Gamma forms and has
the corresponding construction under direct verification. These positive
inclusions do not assume cancellation or an embedding into group completion.


The 322-module integrated build and declaration audit passed, including
the full Gamma-ground ordinary/measured RV/RES class comparisons and
positive RES inclusions: 1033 supporting theorem types, 1182 definitions,
97 named instances and eight reused declarations (2320 total).
Only the permitted standard principles occur. The broader grading,
tensor and parameter-scope obligations remain open; no HK input has
been installed and no new manuscript correction is pending.


The Gamma-ground ordinary RV grading comparison now has a direct build.
Actual cartesian symmetry, associativity, units and product/cut compatibility
give the graded commutative semiring on the fixed-degree scissors.
`GammaGroundRVGradedComparison` proves its equivalence with the original
universal cartesian presentation. `GammaGroundRVGradingConsequences` proves
the fixed-degree inclusions injective and identifies the actual graded
Grothendieck group, with homogeneous generator formulas. RES now also has
its actual graded cartesian semiring and an injective positive graded
inclusion, with the canonical ring-completed map and group grading.
These results have no geometric lift or HK premise. The measured RV
cartesian laws and product/scissor compatibility also have direct builds;
the corresponding graded semiring comparison is being completed.


Gamma-ground ordinary RV bounded inclusions are now proved injective by
extracting each actual finite-sum component from the established grading.
The graph-object normal form is also extended to this ground, with the
label map proved to be the first coordinate projection. Measured RV
cartesian associativity, symmetry, units and distribution over actual cuts
have direct builds, and the genuine measured RV direct sum now carries
its commutative semiring. The comparison to its universal presentation is
under verification. Ordinary RES has its group grading and the canonical
ring map to RV with actual object formulas; no unproved promotion of
positive injectivity to group-completion injectivity has been made.


The measured Gamma-ground RV direct-sum comparison now has a direct build,
including independence of degrees, the cartesian commutative semiring and
the equivalence with the universal presentation. Measured RES has its
actual graded cartesian semiring and an injective positive graded inclusion
into measured RV, retaining all Gamma forms and degree-zero objects.
Their group gradings and canonical ring-completed coefficient maps are
being included in the next integrated audit. No HK coefficient monomorphism
or tensor isomorphism is inferred from these positive inclusions.


The 347-module integrated build and declaration audit passed: 1123
supporting theorem types, 1246 definitions, 119 named instances and eight
reused declarations (2496 total), with standard principles only.
It includes ordinary and measured Gamma-ground RV direct-sum/presentation
equivalences and group gradings, both actual graded RES semirings and
canonical completed coefficient maps, bounded RV injectivity and the
Gamma-ground graph-projection normal form. Full Gamma/finite-Gamma family
categories and their graded/tensor comparisons remain in progress.


The full Gamma-ground finite-family layer now has direct builds, including
complete branch graphs, composition and inverse bijections. The full code
preimage and decoder keep every imaginary representative. The ordinary and
Gamma-measured Gamma groupoids, with actual RV-code contraction witnesses,
are now constructed at this scope, along with the finite full subcategories.
The measured category retains all piece forms and proves the exact combined
weight/Jacobian equation. Their fixed-degree scissors and coproduct/coherence
comparisons are under direct verification. These additions do not supply
the remaining affine classification or the HK tensor isomorphisms.


The Gamma-ground ordinary Gamma coproduct/partition comparison now has
direct builds. Its actual contraction witnesses commute with every full
code decoder, including tag permutations and disjoint cuts. Positive
class equality is exactly a genuine Gamma isomorphism and every class
has an actual object representative. The finite Gamma and measured finite
Gamma scissors and forgetful positive maps are constructed. Measured
Gamma coproducts retain each original form; their actual symmetry,
associativity and empty-family maps are checked. The measured positive
class comparison and finite positive inclusions are under verification.
A single Gamma-ground piece now has its complete nonzero RV-code lift,
identity target, actual code bijection and finite-Gamma-to-RES consequence.
The family-level lifts and cartesian graded/tensor comparisons are separate.


The full Gamma-ground measured Gamma positive comparison now has a direct
build as well: positive equality is exactly a genuine pointwise measured
Gamma isomorphism, and every class is an actual measured tagged family.
The finite ordinary Gamma positive classes have representatives and inject
into Gamma; their equality is exactly genuine finite Gamma isomorphism.
The measured finite comparison is under verification. The full piece-code
lift and all of these class comparisons preserve the original Gamma ground.


The 376-module integrated build and audit passed: 1212 supporting theorem
types, 1365 definitions, 121 named instances and eight reused declarations
(2706 total), with the standard permitted principles only. The receipt
includes full Gamma-ground ordinary/measured Gamma groupoids, genuine
contraction-witness coproduct/partition maps, positive representatives and
exact class-isomorphism comparisons, both finite positive inclusions,
actual Gamma cartesian object products and the full piece-code RV lift.
Family RV realization, its coefficient maps and graded/tensor comparisons
remain in progress. No HK input has been installed.


The explicit Gamma-ground RV family realization now has prototype builds
for the zero/one encoding, bijectivity, descent of arbitrary definable
family maps, actual RV objects with literal finite target fibres, and
bijections induced by family arrows. These are being installed as separate
modules against the existing full Gamma-ground category. The tag coordinates
are finite and zero-allowed; nonzero target labels are inherited separately.


The full Gamma-ground Gamma and measured Gamma cartesian semirings now
have direct builds of their direct-sum/universal-presentation equivalences.
Both finite full subcategories have actual graded products and injective
graded inclusions. The family-level RV/RES lifts, ordinary and measured
positive coefficient squares, full-code product comparisons, and their
multiplicative lift maps have direct builds. Group gradings and the
canonical balanced tensor maps at this full ground are being integrated.
No new manuscript change or HK input is being assumed.


The 445-module integrated build and complete audit passed: 1438 supporting
theorem types, 1571 definitions, 148 named instances and eight reused
declarations (3165 total), using only the permitted standard principles.
It includes all four full Gamma-ground Gamma graded/direct-sum comparisons,
actual group-completion gradings, finite graded and universal-semiring
positive injectivity, full family RV/RES lifts and both multiplicative
coefficient squares. The canonical positive and completed balanced tensor
maps have their actual object formulas. Their bijectivity and the
Gamma-to-RV coefficient monomorphism are not claimed. The broader affine
classification and original-ground RV fibre-dimension comparison remain
open. Further RV-dimension work is proceeding separately from this receipt.

## November 11: checked [18] dependency and original-ground dimension

The integrated checkpoint now covers **470** supporting Lean modules:
**1538** public theorem types, **1634** definitions/structures/abbreviations,
**148** named instances and **8** reused declarations (**3328** audited
heads). The project build and complete type/dependency audit pass, allowing
only `propext`, `Classical.choice` and `Quot.sound`. The receipt is
`verification/VERIFICATION.json`; this earlier checkpoint is superseded by the final linked checkpoint below. This does not certify complete numbered §3 coverage.

[18] is now a real dependency at
`daviddhilbert/integration-in-ACVF@3c3e478cf1f298061c4489cc03f95669d551ce5e`.
Its full consumer root builds locally. Twenty-six direct exports retain the
upstream full theorem types. Five proof bodies use the recorded compatibility
patch for the already approved proper-open-radius API; their statements are
unchanged. Both package revisions and both patches are checked by the runners.

`IntegrationGammaParameters` proves equivalence of the native sorted
real/Gamma syntax and the upstream full-base syntax on those parameters.
It derives a positive definable Gamma value from the original nontriviality
witness and supplies `AtomicGammaBaseChangeInput` under ACVF00. Thus
`integration_lemma_2_23` uses the checked upstream 3.3 proof.
`IntegrationBallShapes`, `IntegrationPrimitiveShapes` and
`IntegrationUnaryImages` supply exact point-set and parameter comparisons,
construct `PrimitiveImageInput` and `OpenDiscImageInput`, and export 2.27 and
2.28 without those geometric premises. `IntegrationFiniteImage` applies the
checked 2.15 proof to actual RV-infinity and nonzero RV functions.
`IntegrationDiscCodes`, `IntegrationGammaTail` and `IntegrationDiscBases`
prepare full finite-disc-name transport; they do not yet discharge the four
old DC-name interfaces or the original-base partition interface.
`verification/integration-reuse.json` records these distinctions, the exact
upstream symbols and the boundaries of 3.17, 3.24 and RV-volume descent.
Later [18] integral/kernel inputs and the distinct Gamma piecewise-affine
background input remain explicit. No HK input was introduced.

The original-Gamma-ground RV dimension and VF-fibre comparison are now
proved using the original real-field RV rank: finite-map rank bounds,
compactness and gluing, nonzero-target equivalence, finite and empty cases,
maximum fibre dimension, bijection invariance and agreement with the earlier
real-base dimensions. `GammaGroundLemma33` discharges exchange and Gamma/RV
algebraicity from their checked predecessors. `GammaGroundRVZeroStrata`
provides the finite zero-pattern decomposition, and
`GammaGroundVFDimensionCharacterization` relates the object finite-fibre
condition to RV fibre dimension zero. These results are included in the
470-module checkpoint.

The section 2 runner also passes against this integrated checkpoint:
850 public theorem checks and 378 selected reuse checks. The 470-module
receipt remains the checked source checkpoint. Further native finite-disc
syntax drafts are kept in `.scratch/integration-adapters/`; their successful
individual checks do not extend the integrated receipt until installed and
reaudited.


## November 11: all numbered [18] §3 citation interfaces linked

The final linked checkpoint covers **488** supporting Lean modules:
**1618** public theorem types, **1654** definitions/structures/abbreviations,
**148** named instances and **8** selected reused declarations (**3428**
audited heads). The complete project build (10,973 jobs) and complete
printed-type/dependency audit pass using only `propext`, `Classical.choice`
and `Quot.sound`. `verification/VERIFICATION.json` records this source
checkpoint. This supersedes the 470- and 480-module checkpoints; it is not
a certification that all numbered results of diamond-integral §3 are complete.

All **eight** legacy interfaces for numbered results from [18, §3] now
have checked native constructors, including finite disc-name bases and
mixed disc-to-disc partitions. The separate ninth interface,
`GammaPiecewiseRationalAffineInput`, remains the accepted background
statement; the upstream RV-linearity theorem does not assert it.
The 26 direct proof exports retain the source's exact hypotheses.

`IntegrationDiscForward` through `IntegrationDiscInverse` establish the
full finite-disc syntax equivalence on properly sorted mixed outputs,
without naming any centre/radius representatives. `IntegrationDiscAtomicity`
and `IntegrationDiscRVImages` supply the four finite-DC-name interfaces.
`IntegrationPolydiscAtomicity` and `IntegrationFinitaryPartition` export
2.25 and 2.30 with those arguments discharged by checked proofs.

`IntegrationCoordinatePartition` extracts finite real support of the graph
and positive Gamma witness, retains every old imaginary parameter, applies
the source's small-real-base 3.21 theorem, and enlarges back to the original
base. `IntegrationMixedCodes`, `IntegrationMixedFibres` and
`IntegrationMixedInverse` compare actual tuple graphs and fixed RV labels,
including the inverse fibre iff. `IntegrationZeroRefinement` and
`IntegrationOrdinaryFibres` refine by four source/target zero patterns.
A nonzero image excludes whole VF; a zero image cannot be paper-open by
the checked infinitude theorem. Thus both directions satisfy the native
ordinary-open-disc convention. `IntegrationDiscPartition` and
`IntegrationDiscToDisc` supply `DiscToDiscPartitionInput` and 2.32 with actual
saturation at an infinite cardinal, and no bound on the original real base.

Later [18] integral/kernel inputs remain explicit. Proposition 3.18 still
needs the distinct local HK-style proof campaign recorded in
`verification/HK-INPUT-REVIEW.md`. The proposed two input types and their
conditional equivalences have a separate successful Lean check in
`verification/proposed-inputs/HKProposedInputs.lean`; they are review drafts,
are not project roots or installed premises, and are excluded from this
receipt. No manuscript change was made during this linkage work.

The section 2 regression runner also passes against this 488-module
checkpoint: **850** public theorem checks and **378** reuse checks. Its
receipt records all eight checked constructors in
`section 2/verification/status.json`.

The author has now required local proofs of all HK coefficient/tensor
results; no HK input is authorized or pending approval. The former
conditional proposal is withdrawn. See `verification/HK-INPUT-REVIEW.md`.


## November 11: local tensor proof foundations

The author explicitly required local proofs of every needed HK result;
there is no HK acceptance question pending. The conditional proposal is
withdrawn. HK and arXiv:1509.07695 Section 4.2 are proof references only.

The **502-module** checkpoint passes the complete project build and audit:
**1650** public theorem types, **1670** definitions, **148** named instances
and **8** selected reused declarations (**3476** audited heads), with only
the permitted standard principles. It includes the new intrinsic unary RV
value partition, identification of its full-fibre part with the actual
Gamma lift, finite Gamma columns on a value fibre, original-base column
partitioning by definable Gamma tests, and the finite-image theorem for
Gamma-valued functions on definable subsets of one RV value fibre.

`ValueFibrePartition`, `RVUnaryValuePartition` and
`RVUnaryGammaDecomposition` prove a disjoint decomposition into an actual
finite-value-support residue part and a complete nonzero Gamma preimage.
The auxiliary angular exceptions are used only to prove finiteness. The
partition itself is defined intrinsically over the original full ground.
`GammaRVMinority` and `GammaRVFiniteRows` express finite sides with counting
formulas and apply the proved predecessor finite-projection theorem.
`GammaRVFibreDichotomy`, `GammaRVFiniteColumns` and `GammaRVBaseColumns`
retain genuine saturation, ACVF00 and small real support. `FiniteDefinableColumns`
and `FullGammaColumnPartition` use a decreasing finite column count and
checked original-base Gamma-point selection; no RV representative is named.
`GammaRVRectanglePartition` combines these proofs in native Gamma syntax.

The finite-value-support extensions and their full rectangle statement are
being checked separately after this receipt. These unary results do not
prove tensor bijectivity or coefficient injectivity in general dimensions.
Higher-dimensional decomposition, full-dimensional rigidity and invariance
of tensor expressions under RV isomorphisms remain local proof obligations.


The next complete checkpoint covers **515** supporting modules and
**1676** public theorem types. It includes full unary finite-value-support
rectangles and Gamma image/closure results, finite Gamma correspondences,
actual-code promoted relations, unary and finite-tuple residue-parameter
elimination, nonzero-RV-tuple value dependence, and finite Gamma projection
of finite correspondences over residue tuple domains. Saturation and
smallness of both original real and Gamma parameter sets are explicit in
the last compactness theorem. The build (11,000 jobs) and complete audit pass;
`verification/VERIFICATION.json` records this checkpoint. Later boundary
syntax drafts are outside this receipt until installed and reaudited.

These are local ACVF proofs, not HK cited inputs. They do not yet prove the
general tensor comparison. The next step uses intrinsic Gamma boundaries
and their common finite threshold set to extend the rectangle theorem to
RV tuples; the higher-dimensional RV product normal form, coefficient
injectivity and invariance of tensor expressions remain open.


The **524-module** checkpoint passes the full build and audit: **1708**
public theorem types, **1680** definitions, **148** named instances and
**8** selected reused declarations (**3544** audited heads). It adds the
intrinsic order-boundary/code formulas, their finite good-Gamma relations,
a common finite controller for residue-tuple Gamma columns, and the
original-ground finite rectangle theorem for any finite-value-support RV
tuple against one Gamma coordinate. The checked full-base Gamma-tuple point
theorem and generic definable separating-test compactness theorem prepare
the extension to Gamma tuples. This receipt does not cover later drafts
or certify coefficient injectivity or tensor bijectivity.


The **533-module** build and full audit pass with **1719** public theorem
types, **1682** definitions, **148** named instances and **8** selected reused
declarations (**3557** audited heads). The arbitrary finite-arity residue/
Gamma orthogonality theorem now supplies a disjoint original-ground rectangle
partition. Its proof selects Gamma tuples in symmetric differences, removes
both residue tuples from their Gamma definable closure, and uses saturation
to get finite original-ground separating tests. Finite correspondences from
Gamma tuples to residue tuples have finite residue projection. The section 2
regression also passes (850 public theorem audits and 378 reuse audits).
The later integer-monomial drafts are outside this receipt. General RV product
normal forms, coefficient injectivity and tensor invariance remain open.


The **544-module** build and audit pass, including actual same-ground
monomial RV bijections, basis matrices and integral inverses, Smith
residue-coordinate selection, value contractions, and the guarded equality
value split. All 1749 public theorem types and every recorded definition/
named instance have only the permitted standard dependency principles.
See the current verification receipt for the complete source hashes and
counts. The new residue-character syntax drafts are outside this receipt.
The geometric RV product normal form and both tensor isomorphisms remain
local proof obligations.


The **559-module** project build and complete audit pass, with **1799**
public theorem types. New checked pieces include finite active characters
for guarded equalities and flat residue polynomials, exact Gamma-value
dependence, finite clause value covers, and Smith-coordinate angular
invariance against the remaining free values. Coordinate product charts
and the literal full-preimage mixed quotient are also proved. The total
residue-sum lemmas retain the released junk-zero behavior and do not remove
any source guard. The next global value-pattern refinement addresses the
disjoint partition needed for positive scissors; it is outside this receipt.
The complete tensor and coefficient statements are still open.


The **566-module** build and complete audit pass with **1827** public
theorem types. Global value patterns now form a finite disjoint partition
of arbitrary raw guarded-DNF semantics, with finite residue-coordinate
values and angular invariance in each pattern. Original source guards
remain in the formula. The common-real-name Gamma closure elimination is
also proved; temporary representative names add no Gamma-definable value
to the original ground. The definability/source-DNF adapter and geometric
quotient assembly are being checked next, outside this receipt. No claim
of full Proposition 3.18 is made by this checkpoint.


The **580-module** project build and full audit pass with **1869** public
theorem types. The actual same-real-ground finite angular partition theorem
now preserves the source parameter package and all guarded-DNF domain
certificates. Its cells are definable, pairwise disjoint and cover every
nonzero RV tuple in the set. Each cell has proved integral monomial angular
data with finite residue-coordinate values. The semantic coordinate
quotient and nonzero RV presentation are checked. The latest section 2
regression passes (850 public theorem audits and 378 reuse audits).
Actual product maps, original-Gamma-ground assembly, finite-to-one label
transport, coefficient injectivity and tensor invariance remain open.


The **601-module** project build and full audit pass: **1937** public
theorem types, **1769** definitions, **151** named instances and **8**
selected reused declarations (**3865** audited heads). The local geometric
normal form now constructs finite disjoint definable pieces on a nonzero
RV tuple locus, actual residue and Gamma factors, and same-real-ground
definable product bijections. The residue factors have finite Gamma support
and the Gamma factors use their entire RV value preimage. Actual ambient
arities add to the input ambient arity; RV[k] label degrees are not inferred
from those arities. The original-real/Gamma-ground angular partition and
coefficient-value descent are also checked. General product assembly at
that ground, label/degree transport, generic torus rigidity, coefficient
injectivity and both tensor bijections remain local proof obligations.
No HK premise or manuscript edit is introduced.


The **613-module** project build and full audit pass with **1963** public
theorem types, **1783** definitions, **151** named instances and **8**
selected reused declarations (**3905** audited heads). The actual finite
geometric product normal form is now proved over the original real/Gamma
ground: all source pieces, residue and Gamma factors, and product
bijections retain that ground and every RV code of each Gamma fibre.
The hypotheses explicitly include small real and Gamma bases, saturation,
ACVF00, canonical structure and a nontrivial Gamma value definable over
the original mixed ground. There is no stronger real-base nontriviality
assumption. The theorem currently covers the nonzero RV tuple locus and
records ambient product arities; RV[k] degree transport, zero-coordinate
assembly, isomorphism invariance, coefficient injectivity and both tensor
bijections remain separate local obligations. No HK input is used.


The **623-module** project build and full audit pass with **1978** public
theorem types, **1796** definitions, **151** named instances and **8**
selected reused declarations (**3933** audited heads). The geometric
normal form now covers the entire original RV tuple domain, including all
zero coordinates, by injective parameter-free nonzero coding followed by
pullback of the product charts. Algebraically independent lifts in full
Gamma fibres give the rank bound rank(residue point) + Gamma arity ≤ RV[k]
label degree. A finite-value-support residue set with that rank bound has
an actual same-ground RES[k-m] representative with a nonzero finite-to-one
label. The full Gamma fibre is also bijective with the literal Gamma/RV
code lift. Later tensor-chart and finite-partition assembly is outside this
receipt. Coefficient injectivity, tensor injectivity and measured tensor
comparison remain local obligations; no HK result is assumed.


The corrected **631-module** project build and complete audit pass:
**1992** public theorem types, **1802** definitions, **151** named instances
and **8** selected reused declarations (**3953** audited heads). This
receipt includes local surjectivity of the actual unmeasured positive
balanced tensor map and of its group-completed map over the original
real/Gamma base. The proof uses full-domain product normal form, actual
RES label-degree transport, literal full Gamma fibre lifts and finite
positive-scissor assembly. All needed earlier exchange/Gamma algebraicity
records are supplied by checked [18] adapters; no HK premise is present.
An earlier attempted build detected a helper-file name collision. The
legacy `GammaGroundBijection.ofEmpty` public helper was restored, and the
new empty-class lemmas were moved to `GammaGroundRVEmptyClasses.lean`.
The complete rebuild and audit then passed, including its affected ordinary,
measured and Gamma-lift dependents. Tensor injectivity, coefficient
embeddings and the measured tensor comparison remain open.


The **641-module** full project build and audit pass: **2014** public
theorem types, **1811** definitions, **151** named instances and **8**
selected reused declarations (**3984** audited heads). The new local
Gamma-valued RV function theorem covers the graph by finitely many total
Gamma functions over the original base. It removes angular RV names from
Gamma definable closure, abstracts finite Gamma parameters using universal
full-code predicates, functionalizes the resulting graphs and applies
actual saturation. The actual volume-map adapter and finite Boolean
refinement give pairwise disjoint original-ground source cells, each with
one such Gamma function of its coordinate values. No definable Gamma
section or HK premise is used. Unmeasured positive/group tensor surjectivity
remains proved; injectivity and the measured tensor comparison remain open.
The next adapters expose the monomial value-reconstruction formula and
partition residue factors by finite individually definable value tuples.


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

## Follow-up: generators of the unmeasured tensor kernel

The author's request for a kernel calculation is answered mathematically in
`verification/TENSOR-KERNEL-PRESENTATION.md`. For each actual RES[r] object
X carrying an original-ground definable function c:X -> delta^sharp, the
complete generating family derived there is

    [X]_r tensor ([U]_m-[U+delta e_i]_m),  U in Gamma[m].

The proof retains the RES-dependent coefficients in the local unimodular
monomial formula. Product neighbourhoods and compactness handle full-rank
rectangles; balancing fixed Gamma coordinates into RES allows induction
on the remaining free Gamma arity. The positive version is a congruence
generated by the corresponding pairs, and groupification gives the ideal
of their differences. No cancellation or HK premise is used.

Each generator is killed by the single degree-one element
tau=1 tensor [{0}]_1=[G_m]_1 tensor 1, by a RES multiplication bijection,
finite-Gamma balancing and an integral shear. Thus the calculation also
gives tau*ker(Psi)=0 and the localized unmeasured isomorphism. It does not
identify the kernel with the whole annihilator of tau, reduce the
generators to finite RES objects, or assert a measured analogue.

This is a mathematical proof, not a completed Lean kernel theorem. The
uniform neighbourhood, finite-cover and scissor assembly steps remain
formalization targets. No Lean source, verification receipt or approved
manuscript has been changed. The one-item T001 review now shows this
calculation in blue next to Proposition 3.18 in
`reference/proposed-revisions/T001-kernel-review.pdf`, pages 34–36.
The PDF-only right-panel request returned queued; visibility is unconfirmed.

## Follow-up: the measured kernel

The measured calculation is now recorded in
`verification/MEASURED-TENSOR-KERNEL-PRESENTATION.md`. For a measured
RES[r] coefficient Xbold with a definable function c:X -> delta^sharp,
the generators are

    [Xbold]_r tensor ([(U,sigma)]_m-[(U+delta e_i,sigma_delta)]_m),
    sigma_delta(eta)=sigma(eta-delta e_i)-delta.

The subtraction compensates the Gamma-Jacobian delta. On generic product
rectangles, measured preservation makes the difference of the two RES
combined weights constant. The shared degree-zero measured finite-Gamma
coefficient p_a moves this weight shift into the Gamma factor. The local
monomial rectangle induction then proves completeness of the generating
presentation, at the mathematical level, without a same-ground RV lift.

For the fifth-root example the explicit element is
[(R,0)]_0 tensor ([(I,0)]_1-[(J,-1/5)]_1). It is in the measured kernel
and is nonzero after groupification: forgetting forms sends it to the
previously detected unmeasured element. More generally the assignment of
zero combined weight gives a section of forgetting forms and embeds the
unmeasured kernel into the measured one. The single degree-one measured
torus tau_mu=[(G_m,id,0)]_1 annihilates all the measured generators; the
localized measured map is an isomorphism by the kernel calculation and
surjectivity. Equality with the whole annihilator is not asserted.

These are mathematical proofs, not new completed Lean exports. No Lean
sources, verification receipt, or approved manuscript were modified. The
same T001 review now has a measured companion in blue beside Proposition
3.18 in `reference/proposed-revisions/T001-measured-kernel-review.pdf`.
The earlier unmeasured PDF remains preserved. This does not silently give
both sides of the old root example the zero volume form.
The PDF-only right-panel request returned queued; visibility is unconfirmed.

## Follow-up: the unmeasured kernel under the RES retractions

Both Euler evaluations annihilate the complete unmeasured tensor kernel:
Etilde_chi([X]_r tensor [U]_m)=q([X]_r)*tau^m*chi(U), for chi_g or
chi_b, sends every generator to zero because both characteristics are
invariant under the relevant Gamma translation. This vanishing holds
in the graded !RES target before localization. The existing !I quotient
is needed for finite-Gamma balancing, and no additional quotient is
required by the new tensor kernel. Surjectivity of Psi therefore gives
unique descended Euler maps on K RV[*]; Section 4's use of Psi inverse
can be replaced by this descent. The subsequent point/affine-line
normalizations preserve vanishing, so T001 does not obstruct the bounded
Euler retraction used later in the paper.

The balanced construction, generator calculation, original-ground Gamma
translation issue, and grading are recorded in
`verification/TENSOR-KERNEL-RES-RETRACTION.md`. This remains a mathematical
argument; no complete kernel/Euler/descent Lean theorem is claimed. Other
Section 4 comparison claims have not been certified by this calculation.
The same T001 review now shows this consequence in blue in
`reference/proposed-revisions/T001-retraction-review.pdf`, pages 34–35.
Earlier kernel PDFs are preserved. No approved main text, Lean source or
verification receipt was modified, and no new Section 4 referee batch
was opened.
The PDF-only right-panel request returned queued; visibility is unconfirmed.

## Author correction: the witness and the unary generating family

The kernel notation now indexes by delta, not c. The condition is
delta in Lambda_X, meaning there exists an original-ground definable
c:X -> delta^sharp; any such c witnesses the bijection but does not
otherwise affect the displayed tensor difference. This correction is
incorporated in both unmeasured and measured verification notes.

For the groupified unmeasured kernel, one Gamma variable suffices. The
refined generators are [X]_r tensor ([H_a]_1-[H_(a+delta)]_1), where
H_a=(a,infinity), a is any old-ground definable Gamma point, and delta
belongs to Lambda_X. A translation-compatible polyhedral cone expansion,
unimodular cone refinement and product telescoping reduce the full-arity
family to these unary differences. Singleton differences weighted by X
already vanish by finite-Gamma balancing; closed rays reduce to open
rays and singletons. No affine endpoint is assumed to have an RV lift.

The signed argument proves a ring-ideal refinement; a unary positive
congruence is not claimed. Merely fixing the translated coordinate to
i=1 is immediate even for the positive presentation. All RES degrees
and the variable endpoint a are retained. The proof and precise scope
are in `verification/TENSOR-KERNEL-UNARY-GENERATORS.md`. No measured
unary refinement or completed Lean cone/kernel theorem is asserted.

The current one-item colored review is
`reference/proposed-revisions/T001-unary-generators-review.pdf`, pages
34–35. Earlier PDFs are preserved. The working manuscript, Lean sources
and full verification receipt are unchanged.
The PDF-only right-panel request returned queued; visibility is unconfirmed.

## Finite coefficients: positive-dimensional RES objects are needed

`verification/TENSOR-KERNEL-FINITE-COEFFICIENTS.md` constructs the RES[1]
curve y^5=rv(t)x(x-1), with values (0,1/5) over C((t)), and projection
label x. Multiplication by y gives a degree-two tensor kernel element.
A balanced detector using S-definable-point counts in RES degree zero,
inertia-stable positive-genus curve components in degree one, and the
earlier Gamma endpoint invariant separates it from the ideal of all
finite-coefficient translation relations. The restriction to finite
RES[0] coefficients therefore fails. This does not prove every
individual X is indispensable or identify a minimal coefficient family.

The mathematical proof and detector are not yet concrete Lean exports.
The finite-coefficient PDF was compiled and preserved as
`reference/proposed-revisions/T001-finite-coefficients-review.pdf`.
Before its display, the author prioritized the P_Gamma compatibility
check, so no queued display of that finite-coefficient PDF is claimed.

## Priority check: P_Gamma pullback and RES descent

Let q=mu-Psi^db:T_mu_db -> K muRV^db[*], let f:T_mu_db -> T forget
forms and include bounded Gamma factors in the full unmeasured ring,
and let u forget forms and include bounded RV objects in the full
unmeasured RV ring. The actual product lifts give Psi*f=u*q. For the
stipulated generators P_gamma with a definable t_gamma, forgetting
gives the annulus (0,gamma]^sharp plus two cancelling singletons.
Its ring class is H_0^sharp-H_gamma^sharp=0 by multiplication by
t_gamma. Hence u((P_Gamma))=0, and the full pullback satisfies

    f(q^(-1)((P_Gamma))) subset ker(Psi).

This is a direct calculation independent of complete kernel generation;
it includes all coefficient multiples and tensor-preimage ambiguities.
The RES evaluation annihilates this pullback, so the bounded RES
retraction descends with no additional quotient beyond !I. The endpoint
gamma is included, the zero-radius case is handled, and the tail
cancellation occurs only in the full ring after groupification.

The correct bounded tensor quotient nevertheless retains both ideals:
q^(-1)((P_Gamma))=ker(q)+I_ann, where I_ann is generated by the canonical
annular tensor lifts. The inclusion ker(q) subset I_ann is false: a
bounded fifth-root relation with zero combined weights is separated
from I_ann by the original endpoint detector, with image -10 epsilon.
This non-absorption does not obstruct the RES evaluation, which kills
both ideals. The full calculation and its exact scope are in
`verification/P-GAMMA-PULLBACK.md`.

This remains mathematical work, not a new concrete Lean ideal-descent
export or a certification of every later theorem. No approved manuscript,
Lean source or audit receipt has changed. The current same-item T001
review is `reference/proposed-revisions/T001-p-gamma-pullback-review.pdf`;
earlier PDFs remain preserved.

The full pullback also explains the coefficient issue directly: replacing
the finite R in the bounded relation by the genus-two RES[1] curve gives
an element of ker(q), hence of q^(-1)((P_Gamma)), whose unmeasured image
is outside the finite-coefficient ideal (detector value -2 eta epsilon).
It lands in the full all-X kernel as required. The canonical annular
lifts alone would not reveal this tensor-preimage ambiguity.
The current pullback PDF display request returned queued; visibility is unconfirmed.

## Positive semiring kernel presentation — 2026-11-12

The author requests that the corrected Proposition 3.18 remain at the
semiring level. The primary comparison now uses the least semiring
congruences generated by all actual RES-coefficient coordinate
translations, with the measured Gamma form transported. Groupification
and the signed unary-ray ideal simplification are deferred.

The integrated build and full declaration audit pass for 718 supporting
modules and the Section aggregate: 2164 public theorem types, 1881
definitions, 151 named instances and 8 reused heads (4204 audited heads).
Only propext, Classical.choice and Quot.sound occur. The six positive
relation modules construct actual coefficient translations, transport
them through the packed product charts, check both unmeasured and
measured kernel inclusions, and construct both surjective positive
quotient maps. Actual coordinate projection and sparse assembly prove
that the native tuple coefficient convention agrees with the scalar
availability condition in the manuscript.

Both reverse kernel inclusions remain unproved in Lean. The remaining
geometric work is original-ground uniform product neighbourhoods,
finite positive product refinements, fixed-coordinate normalization
and induction on the remaining Gamma rank. Proposition 3.18 is not
certified complete by this checkpoint.

At the positive level the unary-ray family is insufficient: collapsing
the unbounded region to one class retains equality on bounded elements
and contains every ray pair, whereas the bounded fifth-root pair is
distinct in the tensor semiring and has equal RV images. The general
region-congruence separation lemma is checked in Lean; the concrete
boundedness flag and Laurent-series detector remain mathematical
arguments. This does not settle whether all bounded unary relations
could suffice, or prove that every Gamma arity is necessary.

The revised same-item review is the blue manuscript-context PDF
`reference/proposed-revisions/T001-semiring-proposition-review.pdf`.
The latest right-panel display call did not return, so visibility is
unconfirmed. The approved working manuscript remains unchanged.

## Original-ground monomial product neighbourhoods — 2026-11-12

The full build and audit pass for 731 supporting modules and the Section
aggregate: 2190 public theorem types, 1886 definitions, 151 named
instances and 8 reused declarations (4235 audited heads), using only
standard logical principles. The new local geometric work is recorded in
`verification/UNIFORM-PRODUCT-NEIGHBORHOODS.md`.

The actual generic full-fibre formula now extends to an original-base
product rectangle for equal free arities. Its exponent matrix is
unimodular, its RV coefficients are definable functions of the retained
RES input, and its coefficient value tuple is constant and Gamma-definable
over the original base. The residue output is definable and injective
on the rectangle. Finite-cover compactness over arbitrary interpreted
finite-tuple presentations is checked; the non-generic locus is covered
by finitely many proper old-ground character hyperplanes.

The reverse positive kernel inclusion still needs the maximal-rank arity
comparison, normalization and balancing on these hyperplanes, compatible
finite disjoint product refinement and the global rank induction. The
measured comparison additionally retains the combined weights and the
shared degree-zero weight shift. No completed Proposition 3.18 or whole
section certification is claimed.

The updated blue manuscript-context PDF is
`reference/proposed-revisions/T001-semiring-proposition-review.pdf`;
the latest PDF-only right-panel request returned queued. Visibility is
unconfirmed, and the approved working manuscript is unchanged.

## Positive Gamma-rank reduction — 2026-11-12

The full build and declaration audit pass for 742 supporting modules
and the Section aggregate: 2215 public theorem types, 1889 definitions,
151 named instances and 8 reused heads (4263 audited heads), with only
the standard logical principles. Dependency pins and the approved
manuscript are unchanged.

The rectangular generic-fibre arity comparison is checked, including
after fixing the RES input. A nonempty character-hyperplane factor now
reduces by one Gamma coordinate inside the actual positive tensor:
Smith reduction and an integral basis change expose a fixed old-ground
Gamma value, the actual Gamma monomial code lift gives a positive
Gamma class equality, and fixed-prefix factorization followed by
finite-Gamma balancing transfers the prefix degree into RES. The
general finite-factor balancing identity is checked for both positive
unmeasured and measured tensors, retaining all finite forms and degree
zero. No additive cancellation or extra RV coefficient point is used.

Remaining work is the local coordinate-generator assembly, compatible
finite disjoint product refinement and the global positive kernel
induction. The measured comparison also needs its form normalization
and the shared degree-zero weight shift. The numbered proposition and
the full section remain uncertified.


## Positive product partitions and finite rank reduction — 2026-11-12

The complete build and declaration audit pass for 765 supporting modules
and the Section aggregate: 2316 public theorem types, 1938 definitions,
151 named instances and 8 reused heads (4413 audited heads). Only propext,
Classical.choice and Quot.sound occur. Dependency pins and the approved
working manuscript are unchanged.

Actual finite RV coproduct injections, chart transitions, native tensor
charts and positive degree regrouping now connect the tensor normal forms
to the local geometric comparison. Square product-map branches have
finite covers by actual monomial patches and proper character hyperplanes;
a branch landing in fewer free Gamma coordinates lies entirely over
finitely many such hyperplanes. Each patch has an actual bijection onto
its entire product image and agrees with the original map.

Finite disjoint full-preimage product partitions now give equalities in
the positive tensor itself. Separate Boolean partitions of RES and Gamma
supply a common finite grid, so this step uses no cancellation of RV or
tensor classes. Finite hyperplane covers reduce free Gamma arity by one
in a positive finite sum, transferring its degree to RES. The rank-zero
kernel base case is checked by finite-Gamma balancing and the positive
RES embedding in RV.

Both reverse kernel inclusions and Proposition 3.18 remain incomplete.
The remaining unmeasured work is global finite matching through the RV
coproduct bijection, its actual residual comparison, and final rank
induction. The measured case also needs its form transport and shared
degree-zero weight shifts. Export counts do not certify the numbered
proposition. Native chart partition transport and patch restriction were
individually checked and added after this full-audit checkpoint.


## Two-sided finite matching — 2026-11-12

The complete build and declaration audit pass for **788 supporting
modules plus Section**: 2406 public theorem types, 2008 definitions,
151 named instances and 8 reused heads (4573 audited heads). Only
propext, Classical.choice and Quot.sound occur. Dependency pins and the
approved working manuscript are unchanged.

`TensorRankLayerNormalForm.lean` and `TensorRankLayerAtlas.lean` retain
the actual RV coproduct and its injective disjoint top/lower charts.
`TensorRankLayerMatchCovers.lean` covers each maximal-rank source chart
by actual product matches and finite proper hyperplanes; lower target
branches contribute only hyperplanes. `TensorRankLayerTwoSidedCovers.lean`
combines this with the inverse cover, keeping one finite matrix of
cuttable matches. `RankLayerSourceMatching.lean` selects disjoint source
cells, proves the positive congruence of the matched sums, and proves
disjointness of their actual images on both sides.

`TensorBoxRemainderPartitions.lean` retains matched target boxes whole
and proves a positive parent decomposition with uncovered Boolean-grid
cells. `NativeBoxImagePullback.lean` checks the pullback to children with
a specified parent, preserving the original labels.

After this full-audit checkpoint, three individually checked modules
add the actual residual RV bijection and preservation of both generic
covers (`RankLayerResidualCovers.lean`), positive residual partitions
regrouped by parent (`NativeBoxResidualPartitions.lean`), and homogeneous
smaller-rank native normal forms for finite hyperplane covers
(`NativeTensorHyperplaneReduction.lean`). They are not yet included in
this receipt.

Both global reverse kernel inclusions remain open Lean targets. The
unmeasured remaining assembly is the residual tensor/RV presentation
and rank induction. The measured version additionally needs its actual
form normalization and shared degree-zero weight shifts. These supporting
exports do not certify Proposition 3.18.


## Unmeasured positive tensor kernel — 2026-11-12

The complete project build and declaration audit pass for **794 supporting
modules plus Section**: 2435 public theorem types, 2028 definitions,
151 named instances and 8 reused declarations (4622 audited heads). Only
propext, Classical.choice and Quot.sound occur. The dependency pins and
approved working manuscript are unchanged.

`RankLayerResidualAtlas.lean` identifies the entire positive residual sum
with the actual inherited RV complement, including the old lower-rank
charts. It proves both the positive value decomposition and the smaller-
rank normal form. `UnmeasuredTensorRankInduction.lean` then proves the
homogeneous reverse kernel inclusion by induction on free Gamma arity.
`UnmeasuredTensorPositiveKernel.lean` reassembles total degrees and proves
the complete unmeasured positive kernel equals the explicit least
coefficient-translation semiring congruence. Its quotient map is bijective
and has a checked semiring isomorphism with the positive RV semiring.
The object-class formula is checked too. This is a concrete theorem, not
a kernel-identification hypothesis.

These statements retain canonical structure, ACVF00, saturation at an
infinite cardinal, both ground smallness hypotheses and nontrivial Gamma.
They use neither HK as a premise nor cancellation or groupification. The
separate formal graded quotient interface and complete parameter-context
translations remain. The measured reverse inclusion is still unfinished,
so Proposition 3.18 and the full section are not reported complete.

The same blue T001 manuscript-context PDF now gives the two-sided positive
proof and accurately distinguishes the checked unmeasured result from the
measured target. Its PDF-only right-panel display request returned queued;
visibility is unconfirmed. The approved working manuscript is unchanged.


## Graded unmeasured quotient and positive measured weights — 2026-11-12

The next complete build and declaration audit pass for **799 supporting
modules plus Section**: 2455 theorem types, 2037 definitions, 151 named
instances and 8 reused heads (4651 audited heads). Only standard logical
principles occur. The approved manuscript and dependency pins are unchanged.

`UnmeasuredTensorQuotientGrading.lean` now gives the unmeasured positive
quotient's multiplicative fixed-degree direct-sum decomposition, its
degree inclusions, and the original r+n degree formula on pure object
tensors. Thus the separate graded quotient interface mentioned at the
preceding checkpoint is now supplied at the explicit Gamma-ground scope.

The measured foundations in this receipt prove finite image and old-ground
definability of every RES combined weight; finite disjoint constant-weight
partitions; genuine shared finite measured Gamma scalars in degree zero;
positive balancing of a weight shift between RES and Gamma; and finite
normalization of every measured pure tensor to RES combined weight one.
No form is silently forgotten and no additive cancellation is used.

Later individually checked modules totalize partial Gamma forms over the
same ground, split the actual measured Gamma tags into positive sums,
produce normalized measured single-piece normal forms for arbitrary
positive tensors, and descend weighted full-fibre RV bijections to actual
measured Gamma morphisms. Tuple translations and weighted unimodular
monomials are checked individually too. The measured local-to-global
reverse kernel proof remains in progress; Proposition 3.18 as a whole
and the full section are not reported complete.


## Measured local comparison — 2026-11-12

The complete integrated build and declaration audit pass for **810
supporting modules plus Section**: 2483 theorem types, 2055 definitions,
151 named instances and 8 reused heads (4697 audited heads). Only propext,
Classical.choice and Quot.sound occur. The main manuscript and all pins
are unchanged.

The full normalized positive measured single-piece normal form is now
included: every original residue and Gamma degree is retained, the RES
combined weight is one, and each native Gamma piece has a full definable
combined-weight function over the original ground. The audit also covers
actual weighted Gamma fibre descent with its RV code contraction, weighted
unimodular Gamma monomials, all tuple translations generated by the
one-coordinate measured pairs, and their normalized local product
congruence. `MeasuredNativeTensorCharts.lean` gives actual measured native
product bijections, the full native weight formula and the positive tensor
image comparison. Native RES and Gamma finite partition identities retain
all labels and weights.

`MeasuredTensorBooleanCells.lean` was checked individually after this
receipt: finite disjoint full-preimage product partitions already give
identities in the positive measured tensor, by a common Boolean grid.
This does not identify the global measured kernel. The weighted matching,
residual comparison, hyperplane reduction and final rank induction still
need assembly. The unmeasured positive graded quotient remains proved at
the explicit Gamma-ground scope; the full numbered proposition is pending
the measured reverse inclusion and complete context translations.


## Measured rank-layer matching and inherited residual weights — 2026-11-12

The complete integrated build and declaration audit pass for **830
supporting modules plus Section**: 2537 theorem types, 2104 definitions,
151 named instances and 8 reused heads (4800 audited heads). Only the
standard logical principles occur; manuscript and dependency pins are
unchanged.

The receipt includes weighted Boolean product grids, local monomial
matches with all source and target cuts, the actual weight equation of
every patch of a measured RV bijection, and weighted disjoint source
selection. Finite injective-atlas gluing gives a genuine Gamma-ground
volume form on the literal old rank-layer RV object. Its top and lower
native weight formulas identify the positive tensor image. Forward and
inverse rank-layer covers retain the measured congruence. Source
refinement retains the complete target cover, and its actual residual
bijection agrees with the original ambient map.

Parentwise weighted residual partitions give equalities in the positive
tensor semiring. The measured residual atlas retains the full parent
Gamma function on each remaining product cell and presents the actual
inherited RV complement. The weighted hyperplane reduction, final rank
induction and degree reassembly remain in progress; this receipt does
not claim the measured reverse kernel inclusion or the whole proposition.


## Both positive kernel presentations and graded quotients — 2026-11-12

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


## T001 approved and incorporated — 2026-11-12

The author approved the final blue T001 manuscript PDF and instructed
continued formalization. The corrected Proposition 3.18 and both proofs
are now in ordinary main-text color. A brief green author resolution
records the author-initiated correction; no corresponding referee item
exists. Existing resolved §3 referee notes remain gray. The exact change,
before/after hashes and resolved PDF are recorded in
reference/proposed-revisions/T001-approved.patch and T001-approval.json.
The working manuscript hash is now
24c58ba674814c3f12f6097b9fd61dc5675af627b6b9d4a43cae46052e6f68cb.
The complete manuscript compiled in three passes; the resolved extract
covers printed pages 34–36. Only its PDF was requested in the right panel;
the request returned queued and visibility is unconfirmed. No review is
pending. No commit or push was made.


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


## Continuation: actual ring tensor kernels — 2026-11-12

The author's instruction to carry on prompted an additional check of the
concrete groupification consequences. The complete positive kernel
presentations had been checked, but their ideal presentations in the two
actual ring tensors had not yet been instantiated. That gap is now closed
by `CompletedKernelPresentation`, `RingPresentationDescent`,
`TensorRingKernelPresentations` and `TensorRingDescent`. Both full ring
kernels, quotient comparisons, exact evaluation-descent criteria and the
annular pullback into the explicit unmeasured relation ideal pass the full
integrated build and declaration audit. The new context wrappers retain
the actual paper ground and introduce no cited input.
The approved manuscript is unchanged; no commit or push is authorized.


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
