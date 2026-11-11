# Section 2 status

All tracked numbered §2 targets are implemented in their recorded scopes.
The final finite-DC-ground extensions of 2.25, 2.26, 2.29 and 2.30 are checked.
Latest project audit: **850 public section theorems / 378 selected reuse
declarations**, PASS. Only `propext`, `Classical.choice` and `Quot.sound`
occur; nine accepted cited interfaces remain explicit and replaceable.
See [COVERAGE.md](COVERAGE.md) for the exact numbered scopes and
[the disc-ground proof review](verification/DISC-GROUND-REVIEW.md).
Earlier milestone counts and unfinished-work notes below are historical;
this paragraph and COVERAGE.md state the current status.

The working manuscript is `reference/diamond_integral_revision_annotated.tex`.
The original upload is retained under `reference/original-upload/`; its SHA256
is `4ae67e2d9ac7a32928362487a7cd2952502eece726366bda4de601064adf94da`.
R022–R024 occur on printed PDF pages 11–13. Gray text preserves the referee's
original remarks; green text states the author-approved resolutions. Referee
remarks are commentary, not part of the main text or independent authorization.

## Author-approved interpretations

- **R022, Notation 2.5, `defn:disc`: resolved.** An RV-disc is the entire
  `rv` fibre, including the singleton `rv⁻¹(∞) = {0}`. The RV-hull keeps
  existing RV coordinates fixed. `RVHull.lean` proves containment,
  idempotence, minimality, preservation of tags, fibrewise saturation, the
  all-zero singleton case and equivalence with empty RV-boundary.
- **R023, Terminology 2.6, `rvfiber`: resolved by clarification of intention.**
  Composition retains the intermediate RV labels. `Continuity.lean` proves
  `GraphFibreContinuous.labelledComp` on the natural branch domains.
  The original fibrewise continuity convention remains in use. No discrete-RV
  topology is imposed. The retained counterexample concerns forgetting labels,
  which is not the clarified composition assertion. The author recalls that
  later constructions retain these labels; this session's general composition
  theorem is not a complete independent audit of every downstream application.
- **R024, Notation 2.10, `disc:exp`: resolved.** The maps are uniform in the
  radius, as the author intended. Origin discs retain their open/closed
  designation. `openDiscCode` takes an actual finite `Gamma`; `closedDiscCode`
  also accepts infinity, which codes the singleton closed disc.
- **Open radius infinity: corrected at the author's request.** Proper open
  discs have finite valuative radius. The companion library's `OpenRadius`
  is `OrderDual Γˣ`, excluding multiplicative valuation zero. The former
  singleton `openDisc_infinity` and `openPolydisc_infinity` declarations are
  removed. Singletons and the whole field use the closed chart. The affected
  geometry, centre, mean and polynomial-constancy callers in Sections 3 and 5
  are updated in `/workspace/special-transformations`.
  The direct Section 4 polydisc bridge is now migrated as well. The portable
  patch now covers 30 source modules, including the Section 8 unary-ball
  caller reached by differentiation. Its obsolete open-radius presentation
  is replaced with a nonzero finite radius in both companion checkouts.
  This does not claim a fresh build of every companion module.
- **R025, Lemma 2.14: resolved.** The author confirms scalar exchange over
  the same fixed base. The introductory sentence now states that scope; the
  two existing bullets are unchanged.
- **R026, Lemma 2.15: resolved by the author's reading of the original text.**
  Literal subsets of VF (or RV) specify one coordinate for both A and B;
  the general tuple convention does not change that wording. The statement
  and proof are unchanged. The proposed source restriction/tuple-target
  rewrite was withdrawn. Gray referee text and a green author explanation
  record this resolution in the rebuilt PDF.

- **R027, sentence after Lemma 2.20: resolved.** Unqualified definability
  still means definability over the fixed ground parameter set. Individual
  discs in a finite Boolean decomposition may need additional parameters to
  be named. The approved sentence says this explicitly. Lemma 2.20 itself
  is unchanged. `CMinimality.lean` retains exactly this distinction.
- **R164, empty dimensions: resolved.** The author approved
  `dim_VF(∅) = dim_RV(∅) = −∞`. Both definitions now specify the empty value
  separately. The previous review question mistakenly called this R032;
  **R032 is the separate boundary-definability wording issue**, now approved
  and applied as recorded below.
- **R028: standing hypothesis approved and applied throughout the paper.**
  The author confirms [18]'s blanket nontrivial-ground-value-group
  hypothesis and approves the same convention for diamond-integral.
  The standing paragraph in §2 now assumes nontrivial Γ(S); the
  VF-generation paragraph is consistent with it; and the contrary
  parenthetical in **§6**, “Special covariant bijections,” is removed.
  Earlier review messages incorrectly called that passage §5. The local
  reminders in 2.23 and 2.25 are retained. Parameter extension preserves
  nontriviality, so downstream uses through 2.30, 2.35 and §6 inherit the
  required hypothesis. This resolves the source-hypothesis issue; it does
  not claim a completed Lean formalization of 2.25 or every downstream proof.
  The original referee text is gray and the adopted resolution green.
  The author asks that later arguments be checked for any actual need for
  a trivial ground value group; see `reference/trivial-ground-base-audit.md`.
  Approved passages: printed pages 11, 13, 15 and 48 in
  `reference/proposed-revisions/standing-ground-assumption-review.pdf`.

- **R029, Lemma 2.24: both proposed proof corrections approved and applied.**
  The unary proof now uses a point algebraic over the fixed ground base and
  the finite ground-definable set containing it. Atomicity would place the
  whole infinite open disc in that finite set, giving the contradiction.
  The final sentence now excludes a nonempty **proper** t-definable subset.
  The statement is unchanged. The original referee text is gray and the
  author explanation green. The approved [18, Lemma 3.9] clarification now
  handles previously named disc parameters, so **R029 is fully resolved**.
  The real/Gamma proof and product induction are retained; 2.21 is not
  extended beyond its stated hypotheses.

- **R163, before Lemma 2.27: approved and applied.** A thin annulus is the
  finite-radius shell `C(a,γ) \ O(a,γ) = {x : val(x−a)=γ}`. The new paragraph
  precedes the first use and does not change theorem numbering. The original
  referee text is gray and the approved explanation green.

## Reuse and verification

Lean is 4.35.0. Mathlib and ACVF-QE retain the revisions in the project plan.
Special Transformations is pinned at `9cc9760892092dd34cfad4a6dee655843c52f30c`
with the explicit `reuse/open-disc-radius.patch`. `prepare-reuse.py` checks the
base revision, patch identity and effective source hashes; it refuses to
overwrite other Lean edits. This keeps a fresh checkout reproducible before
the library correction is published. No GitHub push is authorized by this work.

`verify.py` builds the project, prints the full public section theorem types,
prints the defining interfaces and audits axioms. It also audits public
declarations in every changed library module and selected downstream exports.
`verification/status.json` records the result and exact input hashes;
`verification/headline-audit.txt` contains the corresponding types and axioms.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. A passing
record certifies only the recorded source state and stated coverage.

The basic coordinate and hull facts require ACVF, without saturation or
characteristic-zero assumptions. The forgetting-label counterexample requires
ACVF(0,0); its compatible valuation and nontriviality are explicit or derived
in its full type. The imported centre and algebraicity theorems retain their
own base-generation, characteristic, smallness and saturation hypotheses.
No such theorem is silently treated as an unconditional paper result.

## Lemmas 2.11–2.13

`Bases.lean` distinguishes generation as an LRV substructure from generation
under definable closure. The inherited closure-generated interfaces are named
`DclVFGenerated` and `DclVFGammaGenerated`; they are not premises for 2.11.
`VFGeneratedFieldBase` records the VF field and RV representatives, proves
substructure generation, and proves that retaining those RV names does not
change definable closure. It also identifies VF algebraicity with algebraicity
over exactly the original field. None of these interfaces assumes henselianity
or definable closedness.

`Henselianity.lean` proves `henselian_of_definableClosure_eq`, the forward
implication of 2.11. A simple residue root lifts in the algebraically closed
ambient field. Its residue class and polynomial equation define a singleton;
Mathlib's uniqueness theorem (Stacks Project tag 06RR) proves uniqueness.
Definable closedness puts that root in the original field, giving the actual
`HenselianLocalRing` on its valuation ring. This direction requires only ACVF
and the standing VF-field convention; nontriviality and characteristic zero
are not needed for this stronger implication. The exported type retains the
compatibility of the valuation with the fixed LRV language.

`AlgebraicEnvelope.lean` now supplies the reverse implication and exports the
equivalence `lemma_2_11`. It constructs the elementary algebraic closure of
the original VF field, identifies the original base inside it, proves the
Galois property, transports henselianity, and derives valuation invariance.
The checked VF fixed-field argument and RV conjugate-average argument then
give definable closedness, which descends through the elementary embedding.
No envelope, Galois, valuation-invariance, or desired closure conclusion is
left as an additional explicit premise of the headline.

The headline uses `CanonicalStructure.IsCanonical`: this fixes off-sort
totalizations of the one-sorted encoding, as an implementation of the paper's
two-sorted language. It imposes no extra condition on the valued field.
The theorem is exported for that representation; a transport theorem for
arbitrary off-sort totalizations is not claimed. The original base is recorded
by its VF field and RV representatives, including zero, and the nontrivial
value-group witness remains explicit. No additional main-text revision was
made for these proof steps.

`FiniteSets.lean` exports `lemma_2_12`, an actual bijection onto a definable
RV set, with its full graph and image definable over the original base.
The output excludes `rv(0)` in every coordinate. A parameter-free two-entry
encoding removes zero from the companion library's finite RV-infinity codes.
The domain may have any finite VF tuple arity. This theorem also uses the
canonical encoding and ACVF(0,0).

`lemma_2_13` proves the VF algebraicity descent for all finite VF and RV tuple
arities over the original arbitrary base. It reuses the checked companion
Lemma 3.3 and needs only ACVF, with no canonical-totalization restriction.

## Lemmas 2.14–2.15

`Exchange.lean` exports `lemma_2_14_vf` and `lemma_2_14_rv`, applying the
checked companion scalar exchange theorems over the same base. The RV version
retains genuine saturation and smallness and includes the absorbing element
as a stronger version. The VF version retains the standing VF-field base.

`FiniteFibres.lean` exports `lemma_2_15_vf` and `lemma_2_15_rv`. The finitary
powerset-valued function is represented by its complete scalar relation.
Scalar exchange proves that reverse fibres outside acl(S) are finite.
Genuine saturation gives a finite definable cover by algebraic sets and
bounded-fibre sets. Its finite algebraic part covers every infinite fibre;
a final finite threshold defines exactly the desired exceptional set.
The theorem includes finiteness, original-base definability, containment in
the target B, and both directions of the infinite-fibre criterion.

These exports use the original real parameter set `S : Set M`, with the
canonical encoding for 2.15. A separate genuine-Gamma-base version is not
exported here or silently inferred from the real-base statements. Saturation,
smallness, sort conditions, and the VF-field convention remain visible in
the full theorem types.

## Dimensions, disc points and complete types

`Dimension.lean` implements the coordinate-projection and nonempty-interior
VF dimension directly. Its value is in `WithBot ℕ`; bottom is −∞. It proves
that bottom occurs exactly for the empty set, including zero coordinates,
and proves Lemma 2.17 using actual finite-radius open polydiscs. This geometric
equivalence does not require definability or saturation.

`RVDimension.lean` uses actual functions to nonzero RV tuples, their complete
ground-definable graphs and finite fibres. For every definable RV-infinity
set it constructs a finite-to-one map (an injection) into a nonzero RV tuple,
so the set of candidate arities is not merely assumed nonempty. For nonempty
definable sets the least arity is attained. Empty dimension is −∞.
The companion library's dimension conventions have not been silently reused.

`DiscPoints.lean` proves the algebraic and definable cases of Lemma 2.19
separately, using full invariant preimages of closed-disc codes. It also
proves Corollary 2.21 over a genuine real/Gamma base. These statements need
ACVF(0,0) but the reused proofs need no generation restriction. An algebraic
point is not silently promoted to an individually definable point.

`Atomic.lean` implements Definition 2.22, proves the stated equivalence
between its two descriptions of atomicity, and proves that infinite atomic
sets avoid finite ground-definable sets and algebraic ground points. It also
proves preservation on adjoining a Gamma name already definable over the
base, without a nontriviality assumption. This special case is not a proof
of the general cited Lemma 2.23.

`GeneralDiscPoints.lean` now proves the missing generation bridge for a
VF-generated real substructure recorded by `VFGeneratedFieldBase`, together
with arbitrary genuine Gamma names. It shows that taking dcl using the
original real names is equivalent to taking it using just their original VF
field names. The temporary dcl is therefore proved to be VF/Gamma-generated.
Both algebraic and definable cases of 2.20 are exported; the points descend
back to the original base. Genuine saturation and the explicit cardinal
bound on the temporary closure remain in both headline types. No such bound
is silently inferred from a bound on the original base. This is the stated
real/Gamma scope; arbitrary additional DC names are not covered.

`AtomicBaseChange.lean` exports 2.23 relative to the explicit cited input
`AtomicGammaBaseChangeInput`, as authorized for bibliography [18]. The input
states the nontrivial-base complete-type preservation result. Ground
definability after parameter extension is proved here. The hypothesis uses
two distinct actual Gamma values definable over the base; named Gamma values
supply it directly. The general transport from the value group of a raw
language substructure is not claimed. This is not an independent proof of
Yin's cited lemma, and does not include arbitrary additional DC parameters.
See `verification/CITED-INPUTS.md`.

An earlier combined verification passed **245 public section theorem audits
and 315 reuse audits**, with a successful project build. All
exported types and defining interfaces were printed and inspected; the only
logical axioms are `propext`, `Classical.choice` and `Quot.sound`. These axiom
checks do not discharge explicit mathematical premises. In particular 2.23,
2.27–2.29 take the recorded author-accepted cited inputs. Exact hashes and
provenance are in `verification/status.json`.

`AtomicDiscs.lean` now exports `lemma_2_24_unary` over an arbitrary actual
real/Gamma ground base. It proves atomicity after adjoining the complete RV
name using 2.21, VF algebraicity descent, and the approved finite-set
contradiction. The proof works for any infinite atomic valuative disc and
even permits the zero RV parameter. It needs ACVF(0,0), an explicit infinite
disc and its original-base atomicity, but no nontrivial-ground-value-group
assumption, saturation or cited atomic-base-change input. The infinitude
premise is supplied by the usual proper-open-disc geometry when applying it
to 2.24. The scalar export is complemented by `AtomicPolydiscs.lean`: `lemma_2_24`
proves all finite VF arities, including zero coordinates, and
`lemma_2_24_rv_tuple` retains any finite tuple of RV names. The proof promotes
coordinate sections back to the original base, so naming the other VF
coordinates does not silently replace the ground-base atomicity hypothesis.
It uses a finite sequence of coordinate updates. Additional DC ground names
remain outside this interface.

`DiscParameters.lean` gives an explicit finite-chart presentation of
algebraicity over actual DC names. A whole relation across centre/radius
codes is ground-definable, with its full proper Gamma-code preimage and
invariance under equality of DC names. The selected disc itself is not
assumed to be ground-definable. `DiscGeometry.lean` proves the code's
independence of its centre inside the same disc.

`BallAlgebraicity.lean` proves the field exchange and generic-point descent.
`PolydiscAlgebraicity.lean` exports `lemma_2_18_finite_names`: a VF point
algebraic over finite-radius open/closed polydisc names is algebraic over
the original real/Gamma base. The intermediate pointwise hypothesis is
proved internally from the invariant relation; it is not left as a premise.
The generic tuple is chosen in a genuinely definable open box, after naming
only finitely many temporary VF parameters. The proof establishes their
smallness and removes them all. It requires actual saturation, at least a
countable saturation cardinal and small original real parameters, but no
characteristic-zero or nontrivial-ground-value-group hypothesis. The finite
Gamma chart excludes singleton-radius coordinates and the whole-field chart;
transport to a general formal U-bullet language is not asserted.

`AtomicImages.lean` exports `lemma_2_26_rv_relation`, proving constancy of a
complete ground-definable RV-image relation on an atomic polydisc.
`RVImage.lean` proves the full VF-to-RV graph transport using the actual
well-sorted language rv equation, and exports `lemma_2_26`. It retains the
manuscript's finitary and fibrewise rv-injectivity hypotheses; constancy
itself is proved for arbitrary definable VF relations. All zero tags and
zero-coordinate cases are retained.

`PrimitiveDiscs.lean` implements open discs, closed discs and the approved
thin-annulus vocabulary, proving the shell equals the valuative sphere.
`ScalarImages.lean` proves original-base image atomicity independently.
`CitedUnaryImages.lean` exports 2.27 and 2.28 relative to explicit geometric
inputs from [18, Lemmas 3.8 and 3.13]. The source's characteristic and
nontrivial-ground-value-group hypotheses are explicit; image atomicity is
proved here. The constant case of 2.28 supplies an actual VF point.

`VFImages.lean` proves original-base atomicity of a scalar image from any
finite VF source arity. `RVBranches.lean` uses the checked 2.26 to construct
the finite family of single-valued branches. The complete tag set is finite
and ground-definable; each branch graph is definable and its image atomic
over the ground base plus its retained RV tag. The construction proves unique
values per row and reconstruction of the relation, including the zero tag
and the empty tag family. It supplies the logical part before the image
geometry in 2.29, without claiming 2.29's open-disc conclusion.

`RectangleImages.lean` proves the abstract coordinate-chain lemmas.
`OpenDiscGeometry.lean` proves nesting of actual proper open discs, their
infinitude and compatibility with the released ball predicate. It retains
the actual VF witness of a finite radius when describing encoded balls.
`BallConnectedSets.lean` proves the needed ACVF unary-set geometry from
proved ball classification and value density; no maximal-disc existence
premise is left in the final image theorem.

`PolydiscImages.lean` exports `rectangle_image_isOpenDisc`: a nonconstant
definable proper scalar image of a finite rectangle is an open disc when
every coordinate-line image is a point or an open disc. This general result
does not assume atomicity or any cited input. `CoordinateGraphs.lean` and
the public coordinate-section facts in `AtomicPolydiscs.lean` retain exactly
the other VF coordinates when defining a scalar line graph.

`atomic_open_polydisc_image` supplies those scalar-line hypotheses with
the explicit accepted unary [18, Lemma 3.13] input. It transports the
nontrivial ground-value-group witness to every temporary base. Finally,
`TaggedPolydiscImages.lean` exports `lemma_2_29`: an actual finite family
indexed by RV∞, with ground-definable tag set, exact branch graphs over
the original base plus each tag, point or atomic open-disc images, and
reconstruction of every VF row. Properness of each image is proved from
its retained RV tag; it is not an extra headline premise. Constant maps,
the zero branch and the empty family are included in the stronger checked
result. These exports cover real/Gamma bases, without an extra DC-ground
parameter extension being silently asserted.

`DiscTupleParameters.lean`, `DiscTupleLogic.lean` and `DiscGroundBridge.lean`
extend the actual finite-radius DC-name interface to arbitrary finite real
output contexts, including mixed VF/RV and zero output arity. A defining
relation has a full proper Gamma-code preimage and is globally invariant
under equal DC names. The code proves properness, invariance of its fibres,
sorted complement, real-coordinate preimages, and real/Gamma base extension.
Ground-base formulas embed globally while leaving the new disc variables
unused; no selected centres or radius representatives enter the ground base.
The auxiliary-presentation theorem explicitly names centres and actual Gamma
radii and is not asserted as a descent theorem.

The same modules define complete-type generation and atomicity over these
finite DC charts. They prove invariance under a change of presentation,
forgetting the DC parameters, and the finite-ground-set contradiction for
an infinite type-generating set, without assuming it ground-definable.
They introduce no new cited input. This is a parameter-logic foundation,
not a completed multivariate 2.25: polydisc membership, the unary cited
input and its coordinate induction, further logical operations, and the
singleton/whole-field chart cases remain to be connected.

`ScalarBoundary.lean` proves unary boundary finiteness from C-minimality,
without ground-definability of the component discs. It proves that the
zero tag cannot be a unary boundary tag and connects the scalar boundary
to the existing mixed-coordinate `rvBoundary`. It also proves the boundary
empty when there are zero VF coordinates, while retaining auxiliary RV
labels. `ScalarBoundaryDefinability.lean` proves actual boundary definability
over the original real/Gamma base via the complete rv graph.

`RVFiniteDimension.lean` constructs the complete original-real-base graph
of a finite-to-one map from a finite definable RV set to RV^0. It proves
dimension zero for nonempty finite sets and the strict bound by one also
for the empty set. `lemma_2_35_unary` covers the real-ground scope of the
current RV-dimension interface; zero-coordinate boundary dimension is
checked with the approved −∞ convention. The separate finiteness and
definability theorems already allow genuine Gamma bases. This does not
assert the full higher-dimensional boundary bound.

`BoundaryCoordinateExit.lean` proves the coordinate-chain witness used in
that induction: every partially met RV-polydisc yields a unary-section
boundary with the same coordinate tag and all original auxiliary RV labels.
The exit coordinate is proved nonzero. No cited input is added. The full
2.25/2.30 DC-base arguments and the remaining multivariate dimension
calculus for 2.35 remain to be completed.

The finite-open-radius correction applies to the companion `Balls.OpenRadius`
and the section's actual disc-code API. Pinned ACVF-QE still has a legacy
`IsOpenBall` predicate with a singleton alternative; the section's open-disc
API does not alias it. The uses of `IsBall` in 2.24 require infinite sides,
so they do not promote that singleton alternative to a proper open disc.
No upstream ACVF-QE predicate migration is claimed.

## Remaining review and formalization

The author approved and applied the coordinate-chain proof of 2.29 and
RV∞ tag ranges in 2.29–2.30. R030 is resolved with a brief green explanation.
The approved extract is `reference/proposed-revisions/coordinate-chain-review.pdf`;
the previous proposal is retained separately. The author points to a similar
proof pattern in the T-convex Euler-characteristic paper, while explicitly
not transferring its theorem to ACVF. The general ACVF image lemma and
the real/Gamma-base 2.29 are now compiled and audited.

R031 is approved and applied. Corollary 2.30 now explicitly allows
`(disc-name, RV-tag)` parameters for its full branch graphs, cites corrected
2.29, and gives the uniform coded compactness argument, including empty
fibers. The original referee text is gray and the approved explanation
green. The approved extract `reference/proposed-revisions/disc-parameters-review.pdf`
shows printed pages 16–19; the proposal is retained separately. The DC-base
Lean formalization needed for 2.25 and its downstream application remains
in progress.

R032–R033 are approved and applied. The approved
`reference/proposed-revisions/rv-boundary-review.pdf`, printed pages 19–20,
adds the explicit definability assumption, constructs exactly one VF
representative per boundary RV tag, and states constancy of the finite RV
image along a source RV fibre. The draft splits zero-coordinate faces
before applying 2.30, retains all graph tags, and includes the already
approved empty-dimension convention in the zero-coordinate proof case.
Both annotations are resolved, preserving the original text in gray and
brief author explanations in green. The earlier proposal is retained
separately. The panel-open response was queued.

R034 is approved and applied. The differentiability definition now uses
minimum coordinate valuation, with value ∞ at the zero tuple, and excludes
the zero increment. The input-first ijth partial derivative has matrix
position (j,i); coordinatewise boundedness remains a separate convention.
The original referee text is gray and the brief approved explanation green.
The rebuilt `reference/proposed-revisions/tuple-valuation-review.pdf` and
`tuple-valuation-resolved-review.pdf` show printed pages 20–21. The historical
proposal is preserved separately, and `R034-tuple-valuation-applied.patch`
records the exact change. The right-panel open request returned queued.
R035 is also approved and applied. The Jacobian statement now requires
equal VF arities, and its proof first obtains open fixed-label charts by
generic RV local constancy. It explicitly accounts for the smaller-dimensional
exceptional locus and the arity-zero determinant. The original annotation is
gray with a brief green author explanation. The rebuilt
`reference/proposed-revisions/jacobian-local-constancy-review.pdf` and
`jacobian-local-constancy-resolved-review.pdf` show printed pages 20–21;
`R035-jacobian-local-constancy-applied.patch` records the exact change, and
the historical proposal is retained separately. The panel request was queued.

R036 is approved and applied. Terminology 2.39 now uses `valim(A)` for the
coordinatewise valuation image, keeps `A_Γ` for projection to existing Γ
coordinates, and makes the existential finite bounds explicit. The original
annotation is gray with a brief green author explanation. The rebuilt
`reference/proposed-revisions/coordinatewise-valuation-image-review.pdf` and
`coordinatewise-valuation-image-resolved-review.pdf` show printed page 21.
`R036-coordinatewise-valuation-image-applied.patch` records the exact change;
the historical proposal is retained separately. The panel request was queued.

R037 is resolved using the author's original induction. After the author's
explanation and instruction to carry on, the proof now explicitly chooses
γ_t as the finite supremum of the absolute output values on the nonempty
fibre over t. Definable completeness gives the supremum and its least-upper-
bound formula gives a definable bound function. The unary Γ-valued case
then gives one bound for every fibre. The original unary argument is retained.
The original referee text is gray with a brief green explanation.
`R037-definable-fibre-bounds-applied.patch` records the exact change; the rebuilt
`reference/proposed-revisions/inductive-bounded-image-review.pdf` and
`inductive-bounded-image-resolved-review.pdf` show printed pages 21–22.
The right-panel open request returned queued. The earlier full-relation
replacement is only a historical alternative, not the adopted proof; do not
apply its patch from the old approval question.

R038 is approved and applied. Definition 2.42 now uses all of L and the same
punctured-neighborhood formula locally, without a global range bound. A finite
affine limit set supplies local boundedness, and any separately assumed range
bound means the union of all values is bounded. Minimality and the puncture
remain unchanged. `R038-local-limit-sets-applied.patch` records the exact
change. The rebuilt `reference/proposed-revisions/local-limit-sets-review.pdf`
and `local-limit-sets-resolved-review.pdf` show printed page 22; the historical
proposal is separate. The original referee text is gray with a brief green note.

R039 is approved and applied. Lemma 2.44 now assumes n>0, retaining the
unchanged punctured limit convention. The proof treats every finite inverse
branch on a neighborhood where its RV-label set is constant, including the
empty-label case. The author explains that the original ending uses the
principle that a definable RV-indexed union of VF sets of dimension less than
n still has dimension less than n; the expanded proof obtains the same
coverage. The original referee text is gray and the brief resolution green.
`R039-finite-branch-continuity-applied.patch` records the exact change.
`finite-branch-continuity-review.pdf` and its resolved copy show printed
pages 22–23; the original proposal is retained separately.

R040/R165 is approved and applied. Curve selection (2.46) explicitly has the
local hypothesis that S is VF-generated, takes definable A⊆VF^n and requires
finite nonempty values with singleton limit {b}. Projective charts handle
infinite coordinates. The proof extends its continuous germ by a constant
finite nonempty set on a clopen complement instead of rescaling by a scalar
of a definable radius. Standing nontriviality supplies the needed model
hypothesis. VF-generation is not imposed globally; later geometric arguments
may temporarily enlarge their parameter base. Both referee remarks are
resolved gray/green. `R040-R165-curve-selection-applied.patch` records the exact
change. `curve-selection-base-review.pdf` and its resolved copy show printed
page 24; `curve-selection-base-proposal.pdf` preserves the historical draft.
The main PDF was rebuilt in three passes after each approved revision.
Panel requests returned queued, which does not confirm display.

R041/R042 is approved and applied. Lemma 2.48 treats finite missing affine
boundary points and unbounded output separately. Finite nonempty choices
are justified by elementarity and compactness over a temporary VF-generated
base; finite-dimensional affine limits and continuity then prove closedness
and boundedness. Lemma 2.50 explicitly takes graph closure in A×B^p, where
B^p is the projective closure of the affine target B, with valuation topology.
Its reverse proof selects bad inputs first and then takes a finite projective
limit of their images. The projective-limit remark after 2.45 uses the same
valuation-topology convention. No global VF-generation assumption is added.
Both annotations retain gray originals and brief green author resolutions.
`R041-R042-geometric-proofs-applied.patch` records the exact adopted change;
`geometric-closedness-proposal.pdf`, the review TeX and original patch retain
the historical proposal. These are manuscript revisions, not a claim that
full Lean 2.48 or 2.50 has been completed.

R166 is separately approved and applied. Remark 2.47 now says every definable
one-parameter curve is piecewise rational-affine. One affine piece remains
near a one-sided endpoint, explaining why a positive affine coordinate cannot
tend to zero while another tends to infinity. The example and conclusion are
unchanged. Its annotation is resolved gray/green, and
`R166-eventually-affine-curves-applied.patch` records the exact change.
The approved `geometric-closedness-review.pdf` and resolved copy show printed
pages 25–27, including R166. The main PDF was rebuilt in three passes after
these changes; panel requests returned queued.

R043/R044 is applied as an author-agreed expansion of compressed proof
steps. The author confirms that the original proofs are quick and the
comments spell out details. Both statements and their proof strategies are
retained. R043's arity objection is explicitly withdrawn: literal A,B⊆VF
already says both are unary; the tuple convention does not change this.
The expansion explains the singleton limit and inverse tail-radius laws,
hence equality of whole thin annuli. R044 writes out the direct lower bound,
the finite nonempty choice and limit-point contradiction, and the definable
fibre endpoint bound giving uniformity. The original referee text is gray
and the author explanations green. These are not recorded as corrections
of false lemma statements.

`R043-arity-objection-withdrawn.patch` records the annotation correction;
`R043-R044-proof-details-applied.patch` records the subsequent adopted proof
expansions and resolutions. The prior long draft is preserved as
`annuli-partition-bounds-proposal.pdf`, its review TeX and original patch.
The independent comparison with the original uploaded proofs is retained in
`annuli-partition-original-proofs-review.tex/.pdf` as review history. The
current approved `annuli-partition-bounds-review.pdf` and resolved copy show
printed pages 27–29. The main PDF was rebuilt in three passes; panel requests
returned queued.

The author's standing review rule is now explicit in root AGENTS.md: first
check the main statement and proof independently, with its conventions,
earlier results and exact cited hypotheses; only then assess the referee
report. Separate mathematical errors, omitted justifications and optional
exposition. Do not repeat an arity objection to literal subsets of VF or RV.

R045 / Lemma 2.54 is approved and applied. The original bad locus is retained,
with valid-radius sets T_γ in place of a minimum radius or a codimension-one
assumption. The author's RV-indexed union principle supplies one radius on a
disc of base points; finite nonempty choices and unary generic continuity
produce an open product inside A meeting S. The proof works over a fixed
unary base with empty fibres allowed, so relative complementation gives the
closed case. The statement is unchanged; no global base hypothesis is added.
The original referee text is gray and a brief author resolution green.
`R045-fiberwise-openness-applied.patch` records the exact adopted change;
`.scratch/pre-r045-approved.tex` is the backup. `fiberwise-openness-proposal.pdf`,
the review TeX and original proposal patch retain the history. The current
approved `fiberwise-openness-review.pdf` and resolved copy show printed pages
29–30. The main PDF was rebuilt in three passes; panel display returned queued.
This manuscript approval does not claim a complete Lean 2.54 proof.

R046 / Proposition 2.55 is approved and applied. The original implication
was checked independently before the referee report. The proof details use
ambient closures of fibre graphs, the two affine charts of the projective
line, and intersection with the original domain before the closed-graph
criterion. The statement and “as in Lemma 2.54” are retained.
`R046-fiberwise-continuity-applied.patch` records the adopted change;
`.scratch/pre-r046-approved.tex` is the backup. The approved
`fiberwise-continuity-details-review.pdf` shows printed pages 30–31. The main
PDF was rebuilt in three passes and its display request returned queued.
Full Lean Proposition 2.55 remains in progress.

R021 is resolved using the author's existing scalar-scope clarification.
The tuple convention remains unchanged, and no editorial rewrite was adopted.
The section's manuscript-review pass now reaches Proposition 2.55: 29 of its
30 annotations are resolved, with only the additional DC-ground-base scope
of R029 partly resolved. No author approvals are pending. This review status
is separate from completion of Lean formalization.

The two approved R029 proof corrections are applied; the statement of
Lemma 2.24 is unchanged. The separate scope question about additional DC
ground parameters remains open. The approved standing nontriviality
hypothesis now supplies [18]'s source requirement throughout the paper.
Keep checking whether any later argument actually needs a trivial base;
report any genuine conflict rather than silently changing scope.

Lemma 2.18 is exported in the explicit finite-radius chart scope above;
the whole-field chart and general imaginary-language transport remain.
For 2.20 the generation bridge is now proved in the field-base real/Gamma scope described above, with the temporary
closure's smallness explicit. This does not certify a version over arbitrary
extra disc-imaginary ground names.

The author's accepted external inputs from bibliography items 18–22 are
recorded in `../ACCEPTED-CITED-RESULTS.md`. Their cited results may be used
as explicit inputs without searching for absent exports or formalizing those
papers here. This permission does not authorize main-text revisions.

## Approved standing-base revision

The author approved and the working manuscript applies the paper-wide
nontriviality assumption. The focused approved PDF is
`reference/proposed-revisions/standing-ground-assumption-review.pdf` (also
`standing-ground-assumption-resolved-review.pdf`), printed pages 11, 13, 15
and 48. The exact applied difference is
`reference/proposed-revisions/R028-standing-ground-assumption-applied.patch`.
It was checked against the previous audited manuscript hash: only the three
approved main-text passages and adopted R028 explanation changed.

The earlier draft TeX and proposal patch are retained as historical review
artifacts, with their original PDF at `standing-ground-assumption-proposal.pdf`.
They are superseded by the applied revision. A queued panel-open response
is not treated as confirmation that the user can see the PDF.


`Differentiation.lean` implements Definition 2.37 using the actual paper-order
Gamma quotient. `tupleValue` is the minimum coordinate value, including ∞
for the zero or empty tuple; `coordinateValues` remains separate. The approved
punctured quotient condition is proved equivalent to the companion derivative,
so uniqueness and the input-first partial's matrix position (j,i) follow from
checked analytic proofs. No new cited input is introduced.

`RVLocalConstancy.lean` connects actual single-valued VF-to-RV∞ maps to the
proved generic constancy theorem for full RV fibres. It retains the complete
graph and all output tags, including zero. One same-base definable open locus
covers generic inputs and has a complement of smaller companion VF dimension;
the exact hypotheses are a real base, canonical presentation, saturation and
base smallness, a compatible valuation, and positive input VF arity. Zero VF
arity is handled separately without a dimension premise. No topology on RV is
postulated. These supporting results alone did not complete the mixed-map Jacobian theorem
2.38, now assembled in `Jacobian.lean` as recorded below, or
the bridge between the companion VF dimension and the section's direct
interior-based dimension.

`DiscScalarBridge.lean` proves that the scalar DC-name interface used for
algebraicity and the unary VF case of the mixed-tuple interface define exactly
the same sets. Both conversions preserve all finite Gamma support and full
presentation invariance. The algebraicity formulations consequently agree.
This is a logical bridge for 2.25, not its complete atomicity proof.


`Boundedness.lean` implements the approved Terminology 2.39 over actual
VF/RV∞/Γ∞ coordinates. `valim` is the full coordinatewise image, retaining
the existing Γ∞ coordinates; the finite-bound and existential definitions are
printed in the audit. Doubly bounded boxes exclude ∞, so every VF coordinate
is nonzero, every RV coordinate avoids the zero tag, and every existing Γ∞
coordinate is finite. Subsets retain each given bound. This does not yet prove
the bounded-image Lemma 2.41.


`GammaSuprema.lean` proves finite infima/suprema for nonempty bounded definable
subsets of the actual Gamma quotient, over genuine real/Gamma bases in ACVF00.
It derives existence from the checked finite-threshold result, without
postulating Dedekind completeness. A supremum, when it exists, is definable
over that same base via the full nonzero-RV-code set of its upper bounds and
least upper bounds. No RV representative is added to the ground base. This
supplies the extrema behind the author's R037 argument; the complete uniform
family graph and unary bounded-image theorem are not yet integrated as a full
Lean proof of 2.41.

`Limits.lean` implements the approved affine local formula and minimality,
proves its exact equivalence to the companion finite-point predicates, and
proves that the original optional subfamily is redundant. Finite affine limit
sets imply a bounded range on some punctured neighborhood, including empty
candidate/value cases. The isolated-point assertion and Lemma 2.43 are proved;
the latter uses topological closure for any compatible Valued presentation,
with no definability, characteristic-zero or boundedness premise needed.
Zero-source-arity lemmas show that the empty set is always a limit set and a
nonempty candidate cannot be minimal. These establish the zero-arity obstruction behind the approved R039
restriction; they alone do not claim full 2.44, now assembled below.


`RVIndexedDimension.lean` derives the RV-indexed dimension bound and its image
version from the checked companion Lemma 4.3. It uses the companion finite-map
VF dimension, with positive threshold for its strict inequality because that
library assigns empty sets dimension zero. The real base, canonical model,
saturation and cardinal bounds are explicit.

`RVUnionDimension.lean` separately proves the author's RV-union principle in
this manuscript's direct interior-based `vfDimension`. The explicit definable
projection `forgetRVCoordinatesMap` drops RV labels to the singleton empty
RV tuple. Full-dimensional projected interior yields an independent VF point;
adjoining its RV label preserves the VF parameter field, so QE supplies
interior in that fibre. This proves that forgetting RV labels preserves the
bound dimension < n, including n=0 and the approved minus-infinity empty-set
convention. No comparison between the two dimension definitions is assumed.
The scope is an actual real parameter base S with explicit smallness,
saturation, canonical presentation and compatible valuation. General Gamma
or DC-base transport is not claimed.

`FiniteBranchLimits.lean` proves the local analytic step in approved 2.44:
a finite family of continuous VF maps has minimal limit equal to the set of
its values at the point, on a source neighborhood of positive VF arity. Empty
families and coincident values are included. Pairwise disjoint finite target
balls and nonzero points in every positive-dimensional source ball justify
minimality. Actual Gamma balls are bridged to the valuation topology. These
facts do not require definability or characteristic zero. The global finite
coding and exception-locus construction were still outstanding at that
checkpoint; they are now assembled in `FinitaryContinuity.lean` below.

`FiniteLimits.lean` proves Lemma 2.45 over an actual real ground base, for a
unary VF domain and arbitrary finite VF output arity. The checked prequel
Lemma 9.5 supplies a finite projective minimal limit with the same-base chart
definability. The explicit finite range bound excludes every infinite
coordinate, and closedness puts the affine minimal limit inside the target.
The exported `exists_finite_affine_limit` and `lemma_2_45` retain the exact
S-definability of the full graph, fibre finiteness, genuine saturation and
base smallness. A compatible valuation identifies closedness with the
manuscript topology. Minimal-limit frequent hits and nonemptiness from
frequent nonempty values are also proved. No new author-accepted premise or
custom axiom replaces the prequel theorem. This is the recorded real-base
scope, not arbitrary Gamma/DC imaginary-base transport.


`LimitGerms.lean` proves that local eventual equality preserves limit sets
and minimality, that finite constant correspondences have the required minimal
limit on a positive-dimensional source neighborhood, and that a continuous
correspondence on a clopen piece extends continuously by a constant finite
correspondence on its complement. These are the actual valued-field predicates
from the approved curve-selection proof. No definable scalar is chosen. The
full 2.46 finite algebraic-choice construction and projective-chart transport
remain to be integrated; this local gluing lemma does not assert them.

Earlier verification checkpoint: **245 public section theorem audits, 315 reused
declaration audits**, and the project entry-point build passed. The log is
`.scratch/r045-fibre-closures-verification.log`; exact types, axioms, source hashes and
approved manuscript hash are in `verification/`. All new exported statements
were inspected for domain arity, same-base graph/limit definability, actual
Gamma bounds, representation, saturation and smallness hypotheses. Only
`propext`, `Classical.choice` and `Quot.sound` occur; accepted cited-input
interfaces remain the three already recorded for 2.23 and 2.27–2.29.
The new RV-union and limit results introduce no additional cited premise.


`UnaryLimits.lean` bridges affine minimality to projective minimality and
uses the checked prequel Lemma 9.4 to bound the cardinality of a finite minimal
limit by the uniform fibre cardinality. Its same-base singleton-limit theorem
applies to a bounded single-valued unary VF map whose punctured domain
accumulates at zero, with arbitrary finite VF output arity. It retains actual
full-graph S-definability, canonical presentation, saturation and smallness;
the resulting singleton is definable over exactly S. No additional base
names or cited mathematical premise are introduced. Translation to arbitrary
centres and the full weak-concentricity theorem 2.51 remain to be integrated.

`OpenDiscPartitions.lean` implements the pure VF partition predicate with
actual finite Gamma radii. It proves constancy if one partition radius is
below a source box bound, hence a direct lower bound for the entire image.
It also proves the upper-bound contradiction: if a correspondence takes
values in A, has a minimal affine limit L⊆A and satisfies p(x)>val(c) on each
value at c, then L is empty. Nonemptiness from the finite-choice construction
therefore rules out such escape. The containment L⊆A is an explicit essential
hypothesis, supplied by closedness in the intended application. These analytic
steps need neither definability nor characteristic zero; the actual finite
choice construction and uniform definable RV-family endpoint bounds are not
yet assembled into a full Lean 2.53.

An earlier build and audit passed **245 section theorems and 315 reused
declarations** (9548 build jobs), with exact current source and approved
manuscript hashes checked. The log is `.scratch/r045-fibre-closures-verification.log`.
All six newly exported statements and the partition definition were inspected;
only the three permitted logical axioms occur. There are still exactly the
three previously recorded accepted cited-input interfaces. R043/R044's proof details have since been approved and applied.


`GammaFiniteFamilies.lean` proves that a definable family of finite VF sets
indexed by actual Gamma has finite union, in arbitrary finite VF output
arity. Its contrapositive yields an infinite fibre from an infinite union.
The full graph includes every nonzero RV code of every Gamma value; no
representative is added to the ground. The proof uses the checked prequel
finite-valued RV-to-VF relation theorem. Actual full-graph S-definability,
canonical presentation, saturation and original real-base smallness are
explicit. No topology, characteristic zero or new cited-input premise is
needed. This proves the radius-selection fact used in the approved R045
proof; it does not yet instantiate the openness-radius relation or construct
its uniform finite choices, and is not a claim of full Lean 2.54.

Earlier complete verification: **245 public section theorems, 315 reused
declarations**, 9548 build jobs. The log is
`.scratch/r045-fibre-closures-verification.log`. The new graph interface,
headline types and axioms were inspected, and all recorded source, reuse
patch and approved manuscript hashes match. Only the three allowed logical
axioms occur; the three accepted cited-input interfaces are unchanged.
R045 is approved and applied, as recorded above.


`FibreClosures.lean` proves the topological relative-family steps behind
Proposition 2.55. `fibreClosure` takes closure only in the tail space, separately
at each base point. Every resulting fibre is closed. Intersecting with the
original relative ambient set recovers any relatively closed fibre family.
The complementary open extension similarly recovers a relatively open family.
For a fibrewise continuous graph into a Hausdorff space, the ambient fibre
closure intersects its domain in exactly the original graph.

All six results are proved for arbitrary topological tail spaces and an
arbitrary index set; the graph theorem explicitly requires a Hausdorff target.
No topology on the index, definability, valued field, characteristic or
compactness is assumed. This establishes the analytic closure/intersection
steps, not the full finite-exception Proposition 2.55. Uniform same-base
definability of valued-field fibre closure, projective chart transport and the
complete model-theoretic 2.54/2.55 proofs remain to be integrated. The legacy
prequel `ClosureDefinable` declaration is a proposition interface, not a
verified closure theorem, and has not been adopted as a new premise.

Earlier verification passed **245 public section theorems and 315 reused
declarations**, with 9548 build jobs. The log is
`.scratch/r045-fibre-closures-verification.log`. The three new definitions and
all six theorem types were inspected, including the relative subtype domains
and Hausdorff hypothesis. The only logical axioms are the three permitted
ones. Exact source, reuse-patch and approved manuscript hashes match the audit
record. Accepted cited-input interfaces remain unchanged at three; R046 is approved
and applied, as recorded above.


## Quoted-result integration: Lemma 2.36

The manuscript quotes **[17, Lemma 8.7]**; it contains no new proof of 2.36.
`AlmostContinuity.lean` integrates its existing checked proof
`SpecialTransformations.Section8.lemma_8_7_canonical`. The new work transports
the dimension bound to this paper's direct `vfDimension`, and includes zero
source arity using the approved minus-infinity empty-set convention. The
exception is closed and definable over the same real base S. The full type
retains the canonical encoding, saturation, smallness and compatible valuation.
This is reuse of a quoted theorem, separately from new numbered paper proofs.

Complete audit before the subsequent 2.44 coding work: **247 public section
theorems and 317 reused declarations**, log `.scratch/lemma-2-36-verification.log`.
The subsequent coding and inverse-branch work was audited with the full
Lemma 2.44 assembly recorded next.


## Complete numbered result: Lemma 2.44 (real parameter bases)

`FinitaryContinuity.lean` now exports `lemma_2_44`, with its entire conclusion:
there is a subset E of A definable over exactly the original real base S,
its manuscript VF dimension is less than n, and every a in A outside E
satisfies `HasMinimalLimitSet A a F (F a)`. The domain and the complete supported
correspondence graph are S-definable. The finite values may be empty; the
output VF arity may be zero. Source arity n is positive as approved. The
proof is valid even when A has smaller dimension, so the paper's full-dimension
condition is unnecessary for this stronger version; the manuscript is unchanged.

The implementation uses ACVF(0,0), the canonical one-sorted encoding, a
compatible valuation, genuine saturation and smallness of S. It covers real
parameter bases; transport to arbitrary additional disc-code ground bases
is not claimed. No coding, choice, branch-continuity or dimension conclusion
is left as an extra mathematical premise of the numbered theorem.

Supporting modules are distinguished from the completed result:
`FinitaryCoding.lean` reuses the checked uniform tuple-family RV coding;
`FinitaryBranches.lean` constructs total inverse branches by unique inversion,
with zero as the default, and proves uniform full-graph definability;
`FinitaryGeneric.lean` constructs one same-base definable exceptional set.
RV labels, including the zero label and the singleton empty RV tuple, remain
proper RV data. Naming them does not enlarge the VF parameter field. Thus
every inverse branch is continuous at an independent VF input, and the
exceptional set has smaller dimension. On a neighborhood with constant finite
labels, all branches give the actual minimal limit; the empty-label case is
handled directly on A.

The implementation follows the approved finite-branch argument and uses the
already proved generic-point dimension criterion to assemble its uniform
exception. No further manuscript edit or mathematical assumption was added.

**Lemma 2.44 verification checkpoint: 269 public section theorems and 323 selected
reuse declarations**, log `.scratch/lemma-2-44-verification.log`. The project
entry point builds, every public type and axiom report was inspected, and
only `propext`, `Classical.choice`, `Quot.sound` occur. The full 2.44 type has
no additional unverified mathematical premise. Exactly the previous three
accepted cited-input interfaces for 2.23 and 2.27–2.29 remain. The namespace-aware
audit inventories the nested coding theorems as well as numbered results.
Counts include supporting lemmas and do not certify complete §2 formalization.


## Complete integration: mixed-map Jacobian Lemma 2.38 (real bases)

`Jacobian.lean` exports `lemma_2_38` for definable maps between arbitrary
mixed sets with equal VF arity and independent input/output RV arities. It
constructs a same-S definable VF-valued Jacobian map and a same-S definable
exception E contained in the source, with this paper's VF dimension less
than n. Outside E the partial Jacobian exists, and its restriction to every
fixed input RV fibre is continuous. The chart keeps the original map's output
RV labels constant on a genuine source neighborhood. RV is not topologized.
Zero VF arity is included, with empty exception and empty determinant 1.

This integrates the checked companion full-derivative, Jacobian-uniqueness
and definable-Jacobian-map results. The local assembly repeats the scalar
Jacobian in n VF coordinates to obtain a square map. Removing the definable
nondifferentiability loci of that map and the original map gives a single
exception: neither contains an independent VF point. The checked dimension
criterion and local open-polydisc bridge give the manuscript dimension bound.
Differentiability of the repeated-coordinate chart proves scalar Jacobian
continuity directly. The new analytic helper proves that the manuscript's
derivative condition implies actual valuation-topology continuity.

The full exported type requires CharZero(VF), canonical encoding, a compatible
valuation, saturation and smallness of the original real base S. It introduces
no new cited mathematical premise, parameter names or restriction on RV
arities. Additional ground DC codes remain outside this real-base interface.
The manuscript is unchanged; this is formal integration of the approved
statement, separately from Lemma 2.36's explicit quoted-result integration.

**Latest complete verification: 272 public section theorem audits and 329
selected reuse audits**, log `.scratch/lemma-2-38-verification.log`. The project
entry point builds; full types and the fixed-label chart/Jacobian interfaces
were inspected; only `propext`, `Classical.choice`, `Quot.sound` occur. All
recorded source, reuse-patch and approved-manuscript hashes match. The three
author-accepted cited-input interfaces for 2.23 and 2.27–2.29 are unchanged.
This does not certify completion of §2; remaining items include 2.25/2.30 and
additional DC-base transport, multivariate 2.35, 2.41, 2.46 and the later
geometric/open-family results.


## Accepted [18, §3] inputs and finite-radius Lemma 2.25

The author reiterated that §3 of [18] is being formalized and its results
are to be taken as given for now, with possible changes when that Lean work
is complete. Its ball-imaginary context was consulted; none of its results
is being reproved here. `CitedDiscAtomicity.lean` supplies replaceable explicit
inputs for unary Lemma 3.4 and Gamma base change Lemma 3.3 with existing finite
disc names. There are now five cited-input interfaces in total, retaining
ACVF(0,0) and nontrivial ground Gamma. See `verification/CITED-INPUTS.md`.

`NamedPolydiscAtomicity.lean` proves `lemma_2_25_finite_names`: a product of
actual finite-radius open/closed discs contained in a set generating a
complete type is atomic over the original real/Gamma base and its own disc
names. The containing set need not be definable. Mixed open/closed products
and zero coordinates are included. This covers the full open-polydisc case
and the finite-radius closed case. Closed radius-infinity singleton
coordinates and the whole-field chart remain outside this particular interface.
No multivariable atomicity statement was taken as an external input.

The product proof is local work. Coordinate projections supply the unary
hypotheses for [18, Lemma 3.4], and actual disc-name formulas define the
product. In a coordinate line, the fixed other points generate a temporary
real base. First the unary disc becomes atomic over its own name; only then
does [18, Lemma 3.3] add the other radii. `CoordinateDiscNames.lean` proves
that the other discs can be represented by those fixed points and radii,
using full invariant Gamma-code relations. The varying coordinate centre is
never named as a ground parameter. Coordinate chains prove the complete-type
conclusion. No preservation of arbitrary nonisolated types under Gamma
extension is assumed. The manuscript is unchanged.

Supporting logical modules implement projection, conjunction, selected disc
names, normalized real substitutions in Gamma relations, and complete-type
coordinate fibres. These are separate from the accepted unary inputs and
from the assembled finite-radius theorem.

**Latest complete audit: 294 public section theorems and 333 selected reuse
declarations**, `.scratch/lemma-2-25-finite-verification.log`. The entry point
builds, full types and explicit premises were inspected, and only the three
permitted logical axioms occur. Exact sources, reuse patch and manuscript
hashes are recorded. This is not completion of §2 or of the remaining chart
transport and Corollary 2.30. The current Lemma 2.25 PDF excerpt is queued
right; this does not confirm visibility.


## Lemma 2.25: arbitrary closed singleton positions

`BlockTypeFibres.lean` proves complete-type generation after fixing a real
coordinate block. `SingletonDiscNames.lean` proves that closed radius infinity
is a singleton and that its actual DC name gives exactly the definability of
its unique point. These points supply no freely chosen extra centres.
`PolydiscNormalForm.lean` combines them with the finite-radius theorem.

`PolydiscCharts.lean` constructs a name chart for every closed radius tuple in
Γ∞, using a finite partition of the coordinates. `PolydiscAtomicity.lean`
removes the coordinate-order restriction and exports `lemma_2_25_closed` and
`lemma_2_25_open`. Both include zero coordinates; the closed case allows
singleton coordinates anywhere. Their containing set may be nondefinable.
The complete-type conclusion tests every chart presentation of the actual
disc tuple. Only uniquely decoded singleton points enter the real base;
finite centres stay inside the invariant disc-code relations.

These are the full uniform open/closed cases over a real/Gamma ground base,
relative to the two explicit accepted [18, §3] inputs. No multivariable
atomicity or name-chart existence premise remains in the wrappers. This is
separate from arbitrary additional DC ground parameters (including R029),
the whole-field DC code, and the compactness argument for Corollary 2.30.
The manuscript is unchanged. Independent proof review is recorded in
`.scratch/lemma-2-25-charts-proof-review.txt`.

**Latest full audit: 313 public section theorem audits and 335 selected reuse
audits**, `.scratch/lemma-2-25-charts-verification.log`. The project entry
point builds, the complete interfaces and theorem types were inspected,
and only `propext`, `Classical.choice`, and `Quot.sound` occur. The five
author-accepted input interfaces remain explicit and replaceable; hashes
record the exact sources, approved manuscript and reuse patch. This does
not certify completion of §2. Finite-choice and later geometric arguments
remain active work.


## Affine curve selection: assembled and audited

`FiniteChoice.lean` builds same-base finite-valued tuple relations from
pointwise algebraicity using checked scalar finite rows and a genuine
saturated finite subcover. `AlgebraicChoice.lean` derives the local algebraic
witnesses from the checked elementary algebraic-closure model over a pure VF
core. Its VF-generated wrapper and finite-VF-parameter extension construct
that core. `VFFiniteChoice.lean` decodes actual VF tuples and retains their
complete original-base graph, finite values and exact nonempty support.
These are local supporting proofs, separate from the five accepted [18]
input interfaces.

`UnaryFinitaryContinuity.lean` proves the finite-exception unary version of
2.44. The generic bad locus is definable and contains only algebraic points,
so saturation makes it finite. `AffineApproach.lean` constructs finite
nonempty values in the shrinking target balls with minimal limit {b}.
`FiniteExceptionDiscs.lean` defines a clopen origin neighbourhood avoiding
the finite nonzero exception, retaining its entire same-base defining
formula. `FiniteVFSubset.lean` constructs a finite nonempty same-base
definable subset of A without selecting an individual conjugate.
`CurveGluing.lean` proves full graph definability and continuity for extension
by that constant subset. `CurveSource.lean` proves the source is exactly
{c ≠ 0 : v(c) < 1}, is parameter-free definable and open, and accumulates
puncturedly at zero. No scalar section of Γ is used.

`AffineCurveSelection.lean` exports `lemma_2_46_affine`. It proves the full
curve-selection conclusion at an affine closure point over the original
VF-generated real base plus exactly b: all values are finite and nonempty
on the maximal ideal minus zero, are contained in A, are continuous there
in the paper's minimal-limit sense, and have minimal limit exactly {b}.
The headline retains canonical LRV encoding, ACVF(0,0), genuine saturation,
smallness, the compatible valued topology and nontrivial ground valuation.
Modelhood, pointwise choice, a finite continuity exception and a constant
target set are constructed, not left as additional premises.

**Latest complete audit: 348 public section theorem audits / 338 selected
reuse audits**, `.scratch/affine-curve-selection-verification.log`. The project
entry point builds, full interfaces and theorem types were inspected, and
only the three permitted logical axioms occur. Exact source, manuscript and
reuse hashes are recorded. Independent review is in
`.scratch/curve-selection-affine-review.txt`. The five accepted [18] inputs
remain unchanged and replaceable.

The infinite-coordinate projective case of 2.46 is still active work, so
this does not certify full 2.46 or §2 completion. The manuscript is unchanged.
The current curve-selection PDF excerpt is queued right (physical pages
24–25); visibility is not confirmed by that response.


## Full coordinatewise projective curve selection

`CurveSelection.lean` now exports `lemma_2_46`, including infinite coordinates
and zero target arity. The projective point uses the prequel's Option VF
carrier and explicit valuation-neighbourhood predicate. `projectiveClosure`
is proved to agree with ordinary affine closure at finite points. At infinity
the reciprocal chart excludes zero; `ProjectiveCharts.lean` proves exact
neighbourhood transport, chart involution and continuity on its actual
domain. No topological one-point compactification is assumed.

`DefinableVFInverse.lean` proves the full raw inverse graph, including the
off-sort extension: inverse is not silently treated as an LRV function
symbol. `ProjectiveChartDefinability.lean` retains full graph definability
over the original base by guarded preimages under the involution.
`FiniteLimitMaps.lean` proves continuous images of finite minimal limits
remain minimal, using uniform finite neighbourhood estimates and the
checked frequent-hits criterion. It covers empty finite limit sets.

The affine theorem constructs the curve in the chart; inversion returns
all values to the original A. The exact ball equivalence gives limit {b},
nonempty values give minimality, and continuity at each finite chart value
gives continuity throughout the punctured maximal ideal. The parameter set
is exactly the original real base plus the finite coordinates of b; the
equality with the affine centre parameter set is proved because zero already
belongs to the ground substructure. No VF name represents infinity.

The headline retains ACVF(0,0), canonical LRV encoding, genuine saturation,
smallness, a compatible valued topology, VF-generation and nontrivial ground
valuation. It has no extra chart, modelhood, finite-choice, continuity or
limit premise. Arbitrary additional DC ground-parameter transport remains
a separate scope. The manuscript is unchanged.

**Latest complete audit: 371 public section theorem audits / 342 selected
reuse audits**, `.scratch/curve-selection-verification.log`. Full types and
interfaces were inspected; only `propext`, `Classical.choice`, `Quot.sound`
occur. The audit explicitly names the canonical exported inverse-continuity
projection. Exact sources, approved manuscript and reuse hashes are recorded.
The five author-accepted [18] input interfaces remain unchanged. Independent
review is in `.scratch/curve-selection-projective-review.txt`.

This completes 2.46 in the stated encoding and base scope, not the rest of
§2. Work continues with 2.48 and the recorded dimension, boundedness,
compactness and later geometric/open-family items.


## Closed bounded images: full arbitrary-real-base Lemma 2.48

`RelativeLimitMaps.lean` uses continuity within A, keeping every approaching
value in A. `ClosedBoundedLimitCore.lean` proves the two finite-limit
contradictions. `CorrespondencePullback.lean` defines the full inverse-image
family graph by quantifying the actual map-output tuple.
`InfinityApproach.lean` gives a uniform original-base code for escaping
values and proves its equivalence to val(y)<−val(c). These are local proof
steps, not additional cited inputs.

`SmallVFGeneratedBase.lean` removes the temporary VF-generation premise:
Downward Löwenheim–Skolem gives a countable elementary substructure
containing the finite defining parameters and a nontrivially valued VF
element. Definable singleton witnesses close its VF field under inverse,
and elementary witnesses give VF representatives for every RV element.
Thus it supplies `VFGeneratedFieldBase` and smallness below an uncountable
saturation cardinal. The original real parameter base need not itself be
small or VF-generated. No global VF-generation assumption is imposed.

`ClosedBoundedImages.lean` exports `lemma_2_48`: the image of a definable
closed bounded VF set under a definable continuous map is closed and
bounded. Both arities, including zero, are retained. The headline constructs
the temporary base and the finite choices; none of those conclusions is an
extra premise. It retains canonical LRV encoding, ACVF(0,0), genuine
uncountable saturation and compatible valued topology. Definitions and
function graphs use an arbitrary original real parameter set. Imaginary
base transport not already represented by such a raw graph remains separate.
The manuscript is unchanged.

**Latest complete audit: 391 public section theorem audits / 347 selected
reuse audits**, `.scratch/closed-bounded-images-verification.log`. The project
entry point builds, full types and interfaces were inspected, and only
`propext`, `Classical.choice`, `Quot.sound` occur. The five accepted [18]
interfaces are unchanged. Independent review is in
`.scratch/closed-bounded-images-proof-review.txt`. The current PDF excerpt
for this argument is queued right, physical pages 25–26; visibility is not
confirmed. Corollary 2.49 and the remaining recorded §2 work continue.


## Corollary 2.49: actual homeomorphism onto the image

`ClosedBoundedHomeomorphism.lean` exports `corollary_2_49`, constructing
a Homeomorph from A onto f(A) whose underlying map is explicitly f.
Images of the definable closed bounded cuts A minus an open ball are closed
by 2.48; their complements give the inverse neighbourhoods. No closed-image
claim for arbitrary nondefinable cuts is assumed.
`VFDefinableSets.lean` proves the full graph restrictions, typed VF set cuts,
definability of actual VF balls and their openness.

**Latest complete audit: 396 public section theorem audits / 347 selected
reuse audits**, `.scratch/homeomorphism-verification.log`. The entry point
builds, full exported types were inspected, and only the three permitted
logical axioms occur. Both arities include zero; the same arbitrary-real-
base and ambient hypotheses as 2.48 are retained. Independent review is in
`.scratch/homeomorphism-proof-review.txt`. No manuscript change. Work now
continues with the actual two-chart projective topology for 2.50.


## Lemma 2.50: actual projective closed-graph criterion

`ProjectiveLine.lean` equips a wrapped finite/infinity carrier with the
valuation topology from its two affine charts. Both charts are proved open
embeddings; no local compactness is assumed. `ProjectiveTopology.lean` proves
that the released valuation-neighbourhood predicate agrees with actual
closure in the finite product of these projective lines.

`ProjectiveGraphClosure.lean` identifies the explicit cluster condition with
actual graph closure and with closedness relative to the source.
`ClosedGraphCriterion.lean` follows the approved 2.50 proof: failure of
continuity gives a definable bad-input set, a temporary small VF-generated
base, a finite-valued curve tending to the input, and a different projective
output limit. The full graph of the image correspondence is constructed by
`CorrespondenceImages.lean`; no curve or limit conclusion is an extra input.

`ClosedGraph.lean` exports `lemma_2_50` as continuity iff the graph is closed
in **A × Bᵖ**, with Bᵖ the actual projective closure of B. It proves Bᵖ equals
the finite image of B when B is closed and bounded. `BoundedClosedGraph.lean`
transports this to the actual affine relative graph in A × B and exports
`lemma_2_50_bounded`. Both arities may be zero. The theorem retains canonical
LRV, ACVF(0,0), compatible valuation topology and uncountable saturation;
the original real base need not be VF-generated or small. General extra DC
ground transport remains separate. No new cited input or manuscript edit.

**Latest complete audit: 430 public section theorem audits / 352 selected
reuse audits**, PASS in `.scratch/closed-graph-verification.log`. The full
headline types and logical principles were inspected; only `propext`,
`Classical.choice` and `Quot.sound` occur. The proof review is recorded in
`.scratch/closed-graph-proof-review.txt`. Remaining numbered results and
parameter-scope obligations recorded above are still active.


## Quoted Lemma 2.32 and the pure VF case of Lemma 2.53

`DiscToDisc.lean` states concentricity on the actual fibres with both RV
label tuples fixed, using finite-radius open discs. It integrates the
quoted [18, Proposition 3.19] via the explicit replaceable
`DiscToDiscPartitionInput`; it does not reprove that external result. The
finite disjoint partition is definable over the original real/Gamma base.
Its model and nontrivial ground-Gamma hypotheses are explicit. There are now
six accepted-input interfaces, recorded in `verification/CITED-INPUTS.md`.
General additional DC-ground transport remains separate.

`PartitionEscape.lean` constructs the full invariant RV-code graph for the
Gamma-valued partition and its escaping fibres. `PartitionBoundedVF.lean`
proves `lemma_2_53_vf`: both bounds for a partition on a closed bounded
pure-VF set, including the empty set and zero arity. Finite nonempty choices
and the finite limit inside the source are constructed over a temporary
base; continuity of those choices is not assumed. The mixed RV case remains
unfinished and needs the uniform bound in 2.41 and definable fibre endpoints.

**Complete audit at this checkpoint: 437 public section theorem audits /
352 selected reuse audits**, PASS in
`.scratch/partition-and-cited-disc-verification.log`. Full types of 2.31 and
2.53's pure VF case were inspected, with only the three allowed logical
principles. `.scratch/partition-bounded-vf-proof-review.txt` records the proof
review. Later 2.54 helper modules are active work, outside this audit record.


## Lemma 2.54: fibrewise openness and closedness

`FibrewiseOpenness.lean` now exports `lemma_2_54_open`,
`lemma_2_54_closed` and the combined `lemma_2_54` over a fixed definable
unary base I, allowing empty fibres and zero tail arity. The original-base
finite definable exception is the projection of the actual relative bad
locus. Both the uniform-radius projection and its Gamma-indexed union are
proved finite; no codimension-one or minimum-radius assertion is assumed.

`FibreBadLocus.lean`, `UnaryInterior.lean`, `BadFibreChoice.lean` and
`UniformBadFibres.lean` prove the open-rectangle contradiction, unary
empty-interior finiteness, finite-choice continuity contradiction and
uniform-radius projection theorem. `GammaBallRelations.lean`,
`UniformRadiusCodes.lean` and `RadiusProjection.lean` construct the full
representative-invariant Gamma formulas used for the union step.
`VFPairClosure.lean` and `FibreBadDefinability.lean` transport the checked
raw closure formula through an actual head/tail homeomorphism; the bad
locus and its projection remain definable over S.

The headline retains canonical LRV, ACVF(0,0), compatible valuation topology
and uncountable saturation, with an arbitrary real original base. Finite
choice and the temporary small VF-generated base are constructed, with no
extra mathematical conclusion premise. Additional DC-ground transport
remains separate. This follows the approved proof and changes no manuscript
text. The review is `.scratch/fibrewise-openness-proof-review.txt`.

**Latest complete audit: 472 public section theorem audits / 357 selected
reuse audits**, PASS in `.scratch/fibrewise-openness-verification.log`. The
full 2.54 headline and both cases were inspected; only the three allowed
logical principles occur. Proposition 2.55 and other recorded unfinished
results remain active work.


## Proposition 2.55: supporting topology and uniform graphs

The next assembly is active. `ProjectiveSeparation.lean` proves density of
finite tuples and Hausdorffness of the actual projective product.
`ProjectiveFibreGraphs.lean` recovers a continuous fibre graph from its
projective closure on the original domain. `ProjectiveChartClosedness.lean`
proves closedness from the two open affine chart preimages.
`UniformFibreClosure.lean` proves full same-base definability of closure in
each VF fibre, with the base variables kept free.
`ProductClosedGraph.lean` transports the full closed-graph criterion to the
unary-base/tail source coordinates, including its full map graph.
`FibreChartGraphs.lean` constructs both original-base affine and reciprocal
presentations of the fibre graph, using the checked definable inverse.
These are supporting results; the finite-exception conclusion of 2.55 is
not yet exported.

**Latest full audit: 488 public section theorem audits / 359 selected reuse
audits**, PASS in `.scratch/fibre-graph-foundations-verification.log`. The
principal topology, full graph and uniform closure types were inspected;
only the three allowed logical principles occur. There are six explicit
accepted cited inputs, unchanged at this checkpoint. The PDF extract
`reference/fibrewise-current-text.pdf` (physical pages 29–31) is queued
for the right panel; visibility is not confirmed.


## Proposition 2.55: finite exception for joint continuity

`FibrewiseContinuity.lean` now exports `proposition_2_55`: a map with one VF
output coordinate that is continuous on every fibre becomes jointly
continuous after removing a finite definable set of unary base points.
The exception is definable over exactly the original real parameter base.
Empty fibres and zero tail arity are included.

`FibreProjectiveCharts.lean` identifies the two actual open chart preimages
of intrinsic projective fibre closure with the closures of the constructed
affine and reciprocal graph presentations. Their full family graphs are
proved uniformly S-definable. `ProjectiveFamilyClosedness.lean` applies
2.54 to both families, unites the finite exceptions and glues closedness
over the two open charts. The actual graph is recovered on its original
domain by fibrewise continuity, and the full product-source closed-graph
criterion gives joint continuity. The restricted map graph is constructed
over S; no chart, closed-family or finite-exception conclusion is a premise.

The headline retains canonical LRV, ACVF(0,0), compatible valuation topology
and genuine uncountable saturation. The original real base need not be
VF-generated or small. General extra DC-ground transport remains separate.
No manuscript change or accepted-input addition was needed. The proof
review is `.scratch/fibrewise-continuity-proof-review.txt`.

**Latest complete audit: 499 public section theorem audits / 360 selected
reuse audits**, PASS in `.scratch/fibrewise-continuity-verification.log`.
The complete 2.55 type and its logical principles were inspected; only
`propext`, `Classical.choice` and `Quot.sound` occur. Section 2 is still
incomplete: the remaining Corollary 2.30, multivariate 2.35, full 2.41,
2.51, mixed 2.53 and DC-ground scope obligations remain active.

## Corollary 2.30: finite partition and complete branch decomposition

`FinitaryPolydiscPartition.corollary_2_30` is now proved over the original
small real ground base. It supplies the finite disjoint definable partition
and all open-polydisc branch decompositions, including full graphs over
the actual DC tuple and RV tag, point/open image alternatives, and exact
row reconstruction. Empty fibres, zero RV tags and zero source coordinates
are included. No type-local good-disc property, partition, branch graph,
or multivariable image conclusion is an extra premise.

`TypeLoci` proves the actual sorted complete type locus. The unary [18,
Lemmas 3.4, 3.9 and 3.13] inputs retain the varying disc as an imaginary
parameter while the other VF coordinates are fixed. `TypePolydiscTags`
and `TypePolydiscImages` prove the coordinate-chain consequences.
`RawTaggedPolydiscs` defines the uniform first-order predicate by
quantifying over all tags. `TypeLocalCompactness` proves both compactness
steps; `FiniteGoodPartition` retains precisely the nonempty Boolean atoms.
`OpenPolydiscNames` proves own-DC definability with global presentation
invariance, without atomicity. The final branch extraction gets finiteness
from one finite row and retains every tag.

The source's set-valued RV constancy is recorded in its unary atomicity
after an RV name formulation, and its unary open-image result retains the
existing finite DC prefix. These are replaceable accepted cited inputs,
as authorized by the author, bringing the recorded interface count to
eight. Their exact types and scope are in `verification/CITED-INPUTS.md`.
They do not assert an arbitrary extra-DC transport theorem for our proof
of 2.24. No main-text changes were made for this implementation.

**Latest complete audit: 541 public section theorem audits / 360 selected
reuse audits**, PASS in `.scratch/corollary-2-30-verification.log`.
The complete `corollary_2_30` type, branch-decomposition definition and
logical principles were inspected. Only `propext`, `Classical.choice`
and `Quot.sound` occur. The proof review is
`.scratch/corollary-2-30-proof-review.txt`. Printed pages 16–18 are queued
in the right panel as `reference/compactness-current-text.pdf`.

Remaining targets include multivariate 2.35, full 2.41, 2.51, mixed 2.53,
and general additional DC-ground transport. No pending mathematical
approval or critical blocker was found; work continues with RV dimension.

## RV finite-map calculus for the remaining boundary induction

`RVMapGraphs` supplies full graph construction and sortedness.
`RVArityBound` maps RV∞^m finitely to RV^m by sending zero to `rv(1)`
coordinatewise and keeping other tags. Each fibre injects into the finite
set of zero patterns. This proves the sharp arity upper bound without
changing the earlier two-coordinate injective code used elsewhere.
`RVMapRestriction` proves restriction, the bound from any finite map,
and monotonicity of RV dimension. `RVMapUnions` constructs maps on empty
sets, binary unions and arbitrary finite definable unions at a fixed target
arity; selecting the first source piece adds no target coordinates.
`RVProjectionDimension` proves that a definable set finite over m existing
RV coordinates has RV dimension at most m, giving the strict bound when
m is smaller than its ambient arity. The projection's finite fibres remain
an explicit hypothesis of this general calculus result.

These supporting results require canonical ACVF and preserve the original
real ground base. They introduce no cited input, saturation, characteristic
zero or base-generation assumption. They do not yet assemble the full
multivariate 2.35 boundary induction. Product bounds, common-arity padding,
uniform unary-boundary representatives and the zero-face/fibre assembly
remain active work.

**Latest complete audit: 558 public section theorem audits / 360 selected
reuse audits**, PASS in `.scratch/rv-finite-map-calculus-verification.log`.
The arity, monotonicity, finite-union and finite-projection types and their
logical principles were inspected; only the standard three occur. The
eight accepted §3 input interfaces are unchanged.

## Product bounds and uniform choice support

`RVMapPadding` appends parameter-free unit coordinates to a finite map.
`RVMapProducts` forms products of finite maps and defines the full RV∞
universe over the original base. `RVMapReindexing` transports a finite
map through an actual input-coordinate equivalence. `RVDimensionBounds`
characterizes dimension below n+1 by a finite map into RV^n, proves the
finite-union bound, and proves the bound for adding one free RV∞ coordinate.
Empty sets and zero input tags are retained throughout.

`RawSingletonRows` proves the uniform singleton-row guard and unique
definable inversion. `FinitePartialChoice` selects the first available
definable partial choice using finite syntactic indices. `UniformPartialChoice`
uses genuine saturation to reduce an original-base definable family of
partial choices to that finite case. `UniformDefinableChoice` then proves
uniform VF choice from pointwise definability over the actual real input
parameters, using the checked singleton-promotion theorem. The original
small real base and all input sorts are retained. This is a logical
compactness argument, with no added geometric cited input or uniform
choice conclusion assumed in advance.

The actual boundary-family application of Corollary 2.21, the zero-face
split and the final multivariate 2.35 induction remain. Corollary 2.21 is
to be applied to partially met RV fibres; no assertion that arbitrary RV
fibres have definable sections is being used. No manuscript edit was made.

**Latest complete audit: 575 public section theorem audits / 360 selected
reuse audits**, PASS in `.scratch/dimension-and-uniform-choice-verification.log`.
The complete uniform-choice, cylinder and finite-union types and the
product, padding, reindexing and choice principles were inspected; only
the standard three logical principles occur. The eight cited inputs are
unchanged. No pending mathematical approval or critical blocker was found.

## Actual uniform boundary representatives

`RVFibrePoints` proves that every partially met RV fibre contains a point
definable over the original real/Gamma base plus its tag, using 2.21.
The fibre itself has its full graph over that tag and is a proper open
disc when the tag is nonzero. Boundary tags cannot be zero.
`CoordinateBoundaryPoints` retains exactly the fixed other VF coordinates
and the tag in the point's base. `CoordinateBoundaryFamily` proves uniform
definability of the actual inside-and-outside witness relation over the
original base, with all mixed sorts guarded. `BoundaryTagFibres` identifies
its fibres with the actual finite unary RV-boundaries.

`UniformBoundaryRepresentatives` discharges the pointwise-definability
premise of the earlier choice theorem using those actual data. Its full
choice graph is defined over S, and each selected point has its prescribed
RV tag. `BoundaryRepresentativeValues` and
`BoundaryRepresentativeDefinability` construct the paper's finite-valued
VF correspondence: one selected point per boundary tag, or singleton zero
when the boundary is empty. The full graph over any original-base
definable VF source is constructed, its fibres are proved finite and
RV-injective, and its RV image contains every boundary tag. Neither uniform
representatives nor their full graphs remain an extra premise.

These are supporting results for 2.35, not its completed multivariate
dimension conclusion. Its finite partition, zero-coordinate split and
final boundary coverage/dimension assembly remain. The source model is
canonical ACVF(0,0) for the final full correspondence graph, with genuine
saturation and a small original real base. No new cited input or manuscript
edit was needed. Printed pages 19–20 are queued in the right panel as
`reference/boundary-current-text.pdf`; visibility is not confirmed.

**Latest complete audit: 595 public section theorem audits / 360 selected
reuse audits**, PASS in `.scratch/boundary-representatives-verification.log`.
The full correspondence and uniform representative types, point bases,
and logical principles were inspected. Only the standard three occur;
the eight accepted cited interfaces are unchanged.


## Full multivariate RV-boundary dimension

`BoundaryDimension.lean` proves `lemma_2_35` for every finite VF arity,
including zero, over the original small real ground set S in canonical
ACVF(0,0), with genuine saturation and the approved nontrivial Γ(S).
`BoundaryCoordinates.lean` identifies the raw boundary with
`tupleRV '' A ∩ tupleRV '' Aᶜ` for actual VF tuples and exports
`lemma_2_35_vf` from an original-base full definable set. No VF-generation,
uniform representatives, good partition, or finite projection premise is
left in this numbered result. The three accepted unary inputs used by
2.30 are explicit; the recorded total remains eight cited interfaces.

`ZeroFaces`, `ZeroFacesVF`, `ZeroFaceRVFibres`, `OpenRVPartition` and
`FinitaryRVPartition` implement the finite zero-pattern split. Source
charts insert parameter-free VF zero, project the free coordinates,
transport full correspondence graphs, and lift the resulting original-base
partitions. Every contained actual RV polydisc, including any singleton-zero
factors and zero free arity, has constant full RV rows.
`BoundaryRepresentativePartition` applies this to the actual boundary
correspondence over each coordinate projection of A.

`RawMapImages` and `RawRVBoundary` prove full same-base definability of
RV images, boundaries and interiors, with the complement taken in VF^n.
`RVMapDomains` and `RVCylinders` supply definable finite-map domains and
cylinders in any coordinate position. `BoundaryRVGraphs` retains all input
tags and the output tag in its specified coordinate. `BoundaryGraphDimension`
proves its projection fibres finite from actual RV-row constancy and a
single finite VF row. `BoundaryCover` gives the first-coordinate-exit
coverage. Finite unions and induction then finish the dimension inequality.
The unary finiteness theorem used for the representatives was already
proved independently from the Boolean disc decomposition, so no induction
cycle is introduced.

This follows the approved main-text proof, not the referee's generic-lift
alternative. No manuscript change, new cited input, companion-source edit,
commit, or push was made. Remaining work includes full 2.41, 2.51, mixed
2.53, and general additional DC-ground transport.

**Latest complete audit: 655 public section theorem audits / 360 selected
reuse audits**, PASS in `.scratch/full-boundary-verification.log`.
The complete 2.35 raw and typed theorem types, finite RV partition and
representative partition were inspected. Only `propext`, `Classical.choice`
and `Quot.sound` occur. The review is
`.scratch/full-boundary-proof-review.txt`. The current printed pages 19–20
PDF excerpt was re-queued in the right panel; visibility is unconfirmed.


## Full unary weak concentricity, Lemma 2.51

`WeakConcentricity.lean` proves `lemma_2_51` for an actual definable bijection
between unary open VF sets with bounded target. For every source point,
it supplies a target centre and, for every sufficiently large finite Gamma
radius, a finite target radius with equality of whole punctured discs.
The theorem assumes canonical ACVF, genuine saturation at an infinite
cardinal, a small original real base, and a compatible valued-field topology.
It adds no accepted cited input; the recorded total remains eight.

`ScalarExtensions`, `ScalarTranslations`, `ScalarDefinableImages` and
`ScalarSingletonLimits` construct the full graphs, zero extension, named
translations, source/image projections and singleton-limit continuous
extension. The temporary bases add only the two real centre parameters and
remain small. `SingletonLimitTopology` identifies the singleton limit with
the ordinary punctured topological limit. The exceptional preimage of the
target centre is finite by injectivity and is excluded near the source.

`UnaryValueGerms` applies the checked [17] polynomial-relation and unary
valuation calculation at the specified centre, rather than invoking the
generic good-locus statement at an exceptional point. It proves a positive
power law and converts it to the actual Gamma quotient. `GammaPowerRadii`
constructs the associated increasing rational-affine radius order isomorphism.
`InverseGermControl` spells out the C-minimal inverse-neighbourhood step:
the definable image of each small source punctured disc contains a target
punctured disc, and injectivity controls all its inverse images.
`PuncturedDiscImages` combines these facts to prove equality of entire
punctured discs. No assertion that the rational slope is one is used.

The main text and statement are unchanged. The formal inverse-control lemma
supplies directly the neighbourhood consequence of the inverse-limit paragraph;
there is no need to assume a projective inverse limit or a reciprocal law as
an extra input. The target's openness is retained in the headline theorem
although the checked argument proves a stronger statement without using it.
This is not the RV-contraction assertion, and no intermediate RV labels
are dropped.

**Latest complete audit: 686 public section theorem audits / 366 selected
reuse audits**, PASS in `.scratch/weak-concentricity-verification.log`.
The complete 2.51 and fixed-centre power-law types and logical principles
were inspected. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The review is `.scratch/weak-concentricity-proof-review.txt`.
Printed pages 27–28 are queued in the right panel as
`reference/weak-concentricity-current-text.pdf`; visibility is unconfirmed.
Remaining targets include full 2.41, mixed 2.53 and additional DC-ground
transport. No pending approval or critical blocker was found.


## Gamma bounds and uniform suprema for 2.41

`GammaAffineBounds` proves that a finite family of signed rational-affine
power laws preserves two-sided Gamma bounds, including empty domains.
`CitedGammaLinearity` records the precise piecewise-linearity background
used in [18, §3, proof of Lemma 3.18] as an explicit replaceable input under
the author's cited-results instruction. It requires the complete guarded
Gamma-code graph, ACVF(0,0), and nontrivial Γ(S). The resulting unary
Gamma-domain bounded-image theorem is proved from those finite laws.
The total cited-interface count is now nine; the RV-domain statement and
higher-dimensional 2.41 have not been assumed as an input.

`RawFibreComparisons` and `UniformGammaSuprema` prove uniform definability
of upper bounds, least upper bounds, and the actual supremum selector
from pointwise existence. The complete selector graph is over the original
real S; every nonzero RV code of a Gamma value is retained. No uniform
bound function or its graph is taken as a premise.
`RVGammaCuts` derives every strict order cut from a full RV-to-Gamma graph
and applies the checked finite-image theorem on a fixed input value fibre.
This supplies the finite Gamma range used in the unary RV reduction.

**Latest complete audit: 701 public section theorem audits / 367 selected
reuse audits**, PASS in `.scratch/uniform-gamma-suprema-verification.log`.
The full uniform-supremum and fixed-value-fibre types and principles were
inspected, with only the standard three principles. Their proof review is
`.scratch/gamma-bounds-and-suprema-proof-review.txt`.
Full 2.41 still needs the unary RV bound and the author's higher-arity
supremum induction; mixed 2.53 and additional DC-ground transport remain.
No manuscript change, pending approval or mathematical blocker occurred.


## Full bounded RV image, Lemma 2.41

`RVBoundedImages.lean` exports `lemma_2_41` for actual RV-valued functions;
`RVBoundCoordinates.lean` exports `lemma_2_41_gamma` for actual Gamma-valued
functions. Both include arbitrary finite input arity, zero arity and empty
domains. The source uses the released RV∞ tuples, and its double bound
proves that every source tag is nonzero, exactly the paper's RV scope.
The full original-base function graphs are required and retain all input
tags; Gamma-valued graphs contain every proper code of each output value.

The scope is canonical ACVF(0,0), a genuine saturated model at an infinite
cardinal, a small original real S and nontrivial Γ(S). The only cited
premise in these results is the precise piecewise rational-affine Gamma
background from [18, §3, proof of 3.18]. Nine interfaces are recorded in
total. The full 2.41 is proved, not taken as a cited input.

`GammaAbsoluteValues`, `GammaFamilyFibres`, `GammaFamilyProjections`,
`GammaDomainSuprema`, `RVValueFamilies`, `RVValueFinite` and
`UnaryRVGammaBounds` construct the unary RV reduction. Each fixed input
value fibre has a finite Gamma output set. The supremum of its absolute
values descends to a definable function on the actual Gamma value-domain;
its bound gives the unary RV bound. Temporary names used for the pointwise
finiteness proof do not enter the uniform original-base graphs.

`RVGammaBounds` then implements the author's induction on the RV arity.
Each remaining-coordinate fibre is bounded by induction over its actual
named first coordinate. Its nonempty absolute-value image has a finite
supremum by definable completeness. The least-upper-bound formula gives
a full graph over the original S. The unary RV case bounds this function,
and hence bounds the whole original image. `GammaFamilyMaps`,
`GammaHeadFamilies` and `GammaFamilyRestrictions` supply the graph transport.
Finally the actual RV output's value graph is constructed by the full
same-value relation, proving the RV-valued conclusion as well.

**Latest complete audit: 736 public section theorem audits / 369 selected
reuse audits**, PASS in `.scratch/full-rv-bounded-images-verification.log`.
The complete raw Gamma, actual Gamma and actual RV types were inspected;
only the standard three logical principles occur. The proof review is
`.scratch/full-rv-bounded-images-proof-review.txt`.
Printed page 22 is queued in the right panel as
`reference/rv-bounded-images-current-text.pdf`; visibility is unconfirmed.
No manuscript or companion-source edit was made. Mixed 2.53 and general
additional DC-ground transport remain active; no pending approval or
mathematical blocker was found.


## Full mixed-coordinate Lemma 2.53

`PartitionBoundedMixed.lean` exports `lemma_2_53` and
`lemma_2_53_image_bounds` on actual mixed VF/RV coordinates. Both finite
arities may be zero and the source may be empty. The source RV projection
is doubly bounded; every VF fibre is closed and bounded. Its full source
and Gamma partition graphs are definable over the original real S.
`MixedGammaFamilies` projects this graph while retaining the existing RV
tags and every proper output Gamma code. `MixedGammaFibres` derives each
VF fibre graph after naming exactly its actual finite RV tuple. The proved
pure VF 2.53 supplies its two bounds.

`RVIndexedGammaBounds` constructs the full original-S graph of the
supremum of absolute values of each nonempty fibre image, and applies the
completed 2.41. `GammaEndpointBounds` proves that this supremum equals the
paper's max of the absolute endpoint values and zero (one in multiplicative
notation). The implementation follows the approved endpoint strategy;
no manuscript change or choice of uniform bounds is assumed.

The exact scope is canonical ACVF(0,0), genuine saturation at κ > ℵ₀,
a small original real S, nontrivial Γ(S) and a compatible valued VF topology.
The sole cited premise here is the Gamma piecewise-linearity background;
the registry total remains nine. Full project entry-point audit **748 public
section theorems / 369 reuse declarations**, PASS in
`.scratch/full-mixed-partition-verification.log`. Both headline types and
their standard three logical principles were inspected. Proof review:
`.scratch/full-mixed-partition-proof-review.txt`. Current printed page 28 is
queued in the right panel as `reference/partition-bound-current-text.pdf`;
visibility is unconfirmed. General additional DC-ground transport remains
active. No new manuscript approval or mathematical blocker is pending.


## Finite disc-ground transport and current coverage audit

`FiniteDiscCodeEquality` and `FiniteDiscCodeRows` provide a full definable
test for equality of finite-radius DC names and its exact Gamma-row bridge.
`FiniteDiscInvariantHull`, `FiniteDiscHullInvariance`,
`FiniteDiscPromotedRelations` and `DiscTuplePromotion` prove real-parameter
promotion while retaining the actual ground disc names. The hull restores
DC invariance globally after promotion; it agrees with the original formula
at the named tuple. `DiscTypeFibres` then proves complete-type projection
and block fibres over exactly the original base plus the actual fixed block.
No arbitrary disc centre or Gamma representative is added to the ground base.

`AtomicDiscGroundChange.lean` proves full finite-product 2.24 over existing
finite DC prefixes, using only the already registered unary [18, Lemma 3.9]
input. The product induction is checked here. `AtomicImaginaryGround` retains
finite RV tuples and singleton closed-disc ground names through their unique
VF points. The exact scope is canonical ACVF(0,0), nontrivial Γ(B) and the
explicit unary cited input; no saturation or smallness premise is needed for
this finite syntax/product step. See `.scratch/disc-ground-transport-proof-review.txt`.
The accepted-interface count remains nine. This does not assert applicability
of 2.21 to arbitrary imaginary parameter bases.

A green source clarification citing [18, Lemma 3.9] for this extra-disc case
is prepared in `reference/proposed-revisions/disc-ground-base-review.tex` and
its focused PDF, printed pages 16–17. The original real/Gamma proof and product
induction are retained. It is **unapplied and awaiting author review**;
R029 remains partly resolved in the working manuscript. The PDF is queued
right; visibility is unconfirmed.

The final coverage audit also added `GammaJacobian` for Notation 2.8 and
`Contractions` for Definition 2.40, with exact bridges to the companion
implementations. Gamma labels have actual finite values, source/target
arities may differ, and zero arity is included. The contraction is unique
on the actual coordinate images, retains existing RV labels, and has the
companion's full original-base definable-map implementation. The generic
coordinate-map formulation also states the residue/valuation variants.
The disc-to-disc export was corrected to `lemma_2_32`: 2.31 is its preceding
definition in the current PDF. No mathematical content changed in renumbering.

Full project entry-point audit **796 public section theorem declarations /
373 selected reuse declarations**, PASS in
`.scratch/section-final-numbering-verification.log`. The full type and
principle audit is current; only the standard three logical principles
occur. [COVERAGE.md](COVERAGE.md) records the numbered formal scopes and
remaining integration limits. No working-main-text or companion-source
change, commit or push was made in this interval.


## Approved R029 clarification applied

The author approved the green [18, Lemma 3.9] clarification in Lemma 2.24.
It is applied verbatim from the reviewed proposal. R029 is now marked fully
resolved, with a short explanation of how the cited unary result handles
previously named disc parameters. The original real/Gamma proof, product
induction and statement are retained. No extension of 2.21 to arbitrary
imaginary bases is asserted. The preserved upload still has SHA256
`4ae67e2d9ac7a32928362487a7cd2952502eece726366bda4de601064adf94da`.

The main PDF is rebuilt; the focused approved extract is
`reference/disc-ground-base-resolved-review.pdf`, printed pages 16–17.
The draft proposal remains unchanged as review history. No mathematical
input or source approval is pending. This is a manuscript/documentation
change only: the latest audited Lean state remains **796 section theorem
declarations / 373 selected reuse declarations**, with nine explicit
accepted cited interfaces and the standard three logical principles.


Post-approval verification passes again: **796 public section theorem audits /
373 reuse audits**, `.scratch/approved-r029-verification.log`. The recorded
manuscript SHA256 matches the approved current TeX exactly:
`b2e68432e60db8c288cc10c5cd11a74bb0b41f24a3249cd5e31bdf54e4bdf98d`.
No Lean source changed. The approved PDF extract is queued right; display
visibility remains unconfirmed. No source review or mathematical input is
pending. All 30 §2 referee annotations are resolved.

## Final finite disc-ground integration

The entry-point build and full type/principle audit pass with **850 public
section theorems and 378 selected reuse declarations** in
`.scratch/section-2-final-disc-ground-verification.log`. Exact types were
inspected for `lemma_2_25_disc_ground_closed`, `lemma_2_26_disc_names`,
`lemma_2_29_disc_names` and `corollary_2_30_disc_names`, including the
branch-decomposition definitions. The accepted interface count remains nine.

2.25 retains the old finite DC tuple through every new finite/singleton
chart, including arbitrary singleton positions in closed Γ∞ polydiscs and
zero source arity. 2.26 retains the full set-valued RV image. 2.29 retains
the original DC context in its finite tag set, each full branch graph and
nonconstant-image atomicity; coordinate-chain geometry is proved here.

2.30 constructs the good-code formula uniformly before specializing old
disc presentations. Both compactness steps select sets definable over the
original real-plus-DC base. Chosen old centres and radius representatives
are used only to apply saturation, never as new partition parameters. The
DC-ground wrapper explicitly assumes `aleph0 ≤ κ`, genuine κ-saturation
and a small real ground set. Its four [18, §3] inputs were already registered
unary inputs; no partition or multivariable conclusion is assumed. The
result includes full graphs, point/open images, exact row reconstruction,
the zero RV tag, empty fibres and zero source arity.

There are no remaining tracked numbered §2 implementation targets or
pending manuscript approvals. This does not assert a universal transport
theorem for arbitrary infinite sets of imaginary parameters: use the exact
scopes in COVERAGE.md and the exported types. All 30 §2 referee annotations
remain resolved. The main TeX hash is unchanged from the approved R029
state, and no new main-text departure was made during this integration.
The approved PDF extract is queued right; visibility is unconfirmed.
The 30-file companion patch and unrelated uncommitted work are preserved.
Nothing was committed or pushed.
