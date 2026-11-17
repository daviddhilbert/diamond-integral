# Full-paper handoff: continue with Section 7

**November 17 coverage correction.** Read the [numbered audit of Sections 2–6](verification/numbered-coverage-audit/README.md) before relying on the earlier completion records. The audit distinguishes missing proofs and constructions, missing bridges, narrower statements, and accepted inputs. Section 6 still lacks the restricted category, groupoid and surjective positive scissor lift of 6.34–6.37.

**November 17 local proof update:** all four Section 3 Gamma-valued measured
lift/kernel records now have proved producers, including the positive-degree
reverse kernel over the original base. Read
[the completion note](<section 3/verification/GAMMA-KERNEL-COMPLETION.md>) and
[verification progress](<section 3/verification/GAMMA-EXTENSION-PROGRESS.json>)
before the historical input-boundary discussion below. These proofs retain
the full weighted zero categories and do not assume a resolved base. They
do not prove the separate revised variable-aperture kernel in Section 7.26.

This note is for an agent working in another program, using only this public
repository and the original paper PDF with referee report that the author
will supply separately. No previous chat, Dropbox access, Codex runtime or
private workspace is needed to understand the current work.

The checked proof baseline is [da5441b](https://github.com/daviddhilbert/diamond-integral/commit/da5441b92acbf4f58e2e1444f7aae353fb09e505),
published on November 15, 2026. This handoff adds documentation to that
baseline. The next active mathematical task is Section 7. The note covers
all eight sections and the working protocol, including the Section 8
consequences that must remain visible while Section 7 is revised.

**Upstream migration, November 16:** see the
[corrected-pin compatibility record](verification/upstream-weighted-zero-upgrade/README.md)
and its current `status.json`. Both corrected releases are published on main.
The local weighted Gamma-zero conventions are retained. The four Section 3
Gamma-valued lift/kernel records were still open at that checkpoint. The
November 17 local proof supplies their producers. The corrected upstream
Section 7 kernel uses RV-valued densities. This paper's bounded-aperture
kernel has its own proof obligations.

## Read these sources first

1. [AGENTS.md](AGENTS.md), then this note.
2. [The adopted annotated manuscript](<section 2/reference/diamond_integral_revision_annotated.tex>).
   This is the single working TeX source for the entire paper. Other
   section-specific TeX snapshots and old review PDFs may be historical.
3. The original PDF and referee report supplied by the author. Reconcile
   them with the adopted source: the original PDF does not contain all
   subsequently approved corrections. In particular, do not restore the
   original scalar-only Definition 6.11 from that PDF.
4. [The accepted citation policy](ACCEPTED-CITED-RESULTS.md), the relevant
   section coverage maps, and the current verification receipts below.

Use LaTeX labels as stable identifiers. Page ranges in old READMEs refer to
earlier manuscripts; inserted proofs and the new Section 4 items have
changed pagination. Earlier progress notes in READMEs, the formalization
plan and the dependency audit sometimes describe unfinished work that was
later completed. Their current completion headers, exact theorem types and
fresh source-hash receipts take precedence over those historical notes.

## Status of every section

| Section | Current status | Main records and next responsibility |
| --- | --- | --- |
| 1. Introduction | Introductory claims are implemented in their substantive sections; there is no separate Section 1 Lean library. The aperture-dependent bounded-integral target and diagrams now use the relative ideal. | Reconcile the introduction with the final Section 7 and Section 8 results. No blanket claim is made that every introductory referee annotation has been resolved. |
| 2. Technicalities | The tracked technical exports passed verification. The numbered coverage audit flags the 2.14 field-base premise and partial coverage of 2.47. | [Coverage](<section 2/COVERAGE.md>), [status](<section 2/STATUS.md>), [receipt](<section 2/verification/status.json>), [upstream links](<section 2/verification/UPSTREAM-LINKS.md>). Preserve the original-base and finite-disc-name hypotheses. |
| 3. HK-style integral and categories | The four measured kernel records and the corrected tensor presentations have checked producers. The bounded unmeasured part of 3.22 retains a separate accepted input. See the audit for scope and citations. | [Status](<section 3/STATUS.md>), [targets](<section 3/TARGETS.md>), [paper-to-Lean map](<section 3/verification/paper-targets.json>), [receipt](<section 3/verification/VERIFICATION.json>). The map records 21 manuscript targets and 119 declaration links. Do not turn a retained cited interface into an unconditional theorem. |
| 4. Uniform retraction to RES | The retractions and chart-ideal compatibility are checked. The numbered audit flags the positive bounded tensor map in 4.10 and the identification of the chart ideal with the full generator family in 4.17. | [Coverage](<section 4/COVERAGE.md>), [status](<section 4/STATUS.md>), [receipt](<section 4/verification/status.json>), [Section 3 adapters](<section 4/Section3T001Integration.lean>), [linked retraction statements](<section 4/Section3LinkedRetractionStatements.lean>). Keep the old scalar ideal distinct from the new relative ideal. |
| 5. RV decomposition and Fubini | The recorded Fubini entry points and actual-variety corollary are checked, with the Gamma-linearity and ground lift inputs discharged. The numbered audit flags 5.16 and the exact fiber and inflated-family comparisons. | [Current README header](<section 5/README.md>), [discharged entry points](<section 5/Section5DischargedInputs.lean>), [variety corollary](<section 5/VarietyCorollaryDischarged.lean>), [receipt](<section 5/verification/status.json>). Cross-section computations and the computational results cited from [19] were excluded from this requested scope. Do not silently expand that completion claim. |
| 6. Special covariant bijections | The revised aperture construction and map-level theorem 6.38 pass the audit of existing declarations. The restricted category, groupoid and positive scissor lift remain open. The numbered audit also records arity and degree restrictions. | [README](<section 6/README.md>), [review record](<section 6/reference/REVIEW.md>), [receipt](<section 6/verification/status.json>), [applied review PDF](<section 6/reference/review/section6-aperture-revision-applied.pdf>). Reuse these checked constructions rather than reopening completed proofs without a concrete incompatibility. |
| 7. Integrating proper invariant sets | Next active work. Its main text still has the old scalar Definition 7.2 and old scalar kernel conclusion in 7.26. No Section 7 Lean library or complete kernel theorem has been implemented here. | Synchronize 7.2, construct variable blowups and their VF lifts, prove the full congruence/kernel chain, and revise 7.26 and its comparisons. The detailed plan is below. |
| 8. Motivic Milnor fiber | Not completed here. Its main text was deliberately left unchanged. Some algebraic specialization and geometric support lemmas exist in Section 6, but the full equivariant geometric trace and specialization assembly remain open. | [Section 8 handoff](<section 8/SECTION6-HANDOFF.md>). Check fixed-order coefficient comparison, rationality/limit and Theorem 8.11 against the enlarged relative ideal. Do not infer preservation of the final values merely from Section 4 compatibility. |

Sections 2–4 retain the coverage boundaries recorded in the numbered audit. Eight
legacy Section 2 geometric interfaces have checked Section 3 constructors.
Section 5 now supplies the exact Gamma rational-affine producer and its
required ground lifting/kernel producer. Use those actual constructors when
their hypotheses match. Older inventories still describe some of these as
pending. The approved Reichstein–Youssin consequence and any other retained
external inputs keep their explicitly documented scopes.

The current paper's Section 7 is a different target from Section 7 of the
upstream paper [18]. In particular, neither an ordinary [18] lift kernel
nor an absent upstream measured kernel proves this project's new bounded
variable-aperture kernel theorem.

## Standing decisions and mathematical conventions

- Keep the original VF-generated ground base where the paper requires it.
  Nontrivial Gamma(S) is an approved standing assumption throughout the
  paper. The former exception at the opening of Section 6 was removed.
  Actual ACVF(0,0), canonical-model, saturation and smallness hypotheses
  remain explicit in the Lean declarations; do not discard them in adapters.
- Literal subsets of VF or RV are unary. General tuple notation does not
  change that scope. Retain original RV labels through all constructions.
- Paper Gamma notation is additive; several Lean APIs use multiplicative
  Gamma and a zero/infinity element. Check the actual valuation order and
  conversion maps before translating an inequality. An RV class, a value
  fibre and an additive-ball quotient are different objects.
- The author approved the almost-everywhere repair R102. Special covariant
  bijections and standard-contraction lifts have a total derivative of
  determinant one outside a definable VF-small set. Do not restore an
  everywhere partial-derivative claim or apply an everywhere chain rule.
- No HK theorem may be introduced as a given input. The needed coefficient
  and tensor arguments were proved locally. The existing external citation
  policy is in ACCEPTED-CITED-RESULTS.md; an authorized cited result must be
  an exact, replaceable input with its hypotheses and source, not a custom
  global axiom. An external result does not discharge a changed interface
  until its presentation and parameter bridge are checked.
- The adopted aperture change is authorized. Do not ask again whether to
  allow bounded variable apertures. A further non-obvious change of
  definition, theorem scope or hypotheses requires mathematical review by
  the author. Clear independently verified corrections are already authorized.

## The aperture repair already applied in Sections 1, 4 and 6

The extra compatibility work was done specifically to support synchronized
changes to 6.11 and 7.2. Continue on that basis. Avoid unrelated changes to
earlier completed sections unless a real dependency requires them.

In revised 6.11 an aperture is an actual original-base definable function
tau on the full retained RV-label domain U. It is nonzero and has one
original-base named finite bound Delta:

~~~text
0 <= gamma(u) := vrv(tau(u)) <= Delta.
gamma_p = rad(active coordinate of p) + gamma(u_p).
t_p = tau(u_p) * rv(active coordinate of p).
~~~

The original cutoff-dominates-invariance-radius requirement is retained.
A bijective VF lift includes an actual definable endpoint b in the inactive
VF variables, continuous on each fixed-label fibre, with rv(b) = t_p. Its
existence is part of the data. There is no definable VF section assumed for
an arbitrary RV function. The lifted clauses are x_j - lambda off the core
and x_j - lambda + b on the core, with distinct retained branch tags.
The endpoint need not have finite VF image in higher VF arity; its relative
valuation is uniformly bounded. Constant apertures embed with exactly the
old point maps. Thus existence results such as 6.19 remain valid through
their original, stronger constant-aperture constructions.

The new native class is RelativeApertureData and its finite
RelativeApertureChain. The original CentripetalData and
SpecialCovariantChain are retained scalar subclasses. Their continued
presence is not evidence that the manuscript definition was left unchanged.

The actual new-class exports are:

~~~text
DiamondIntegral.Section6.lemma_6_14_bounded_variable_apertures
DiamondIntegral.Section6.lemma_6_38_bounded_variable_apertures
~~~

The latter starts from original proper objects, actual Gamma forms with
open fixed-label levels and the generic measure identity. It constructs
both genuine finite chains, actual bounded aperture graphs, paired whole
cores, the literal conjugate T_B f T_A^{-1}, an RV bijection and the volume
identity at every retained label. Arbitrary retained RV fibres are allowed.
Both squares in the manuscript's 6.38 diagram commute literally.

Section 4 now defines J_var independently by actual relative annular
differences (Notation 4.17, label relative:annular:ideal). Its compatibility
lemma is 4.18, label relative:annular:compatibility. Keep I = (P_Gamma),
with its original RV-liftable scalar radius indexing. Constant apertures
give I contained in J_var; equality is not asserted. Ordinary volume
forgetting kills J_var, the existing bounded retraction descends with its
residue restriction preserved, and the whole degree-zero subring survives.
In the full measured RV ring the relation has the exact image

~~~text
image([U^{tau,j}] - [U]) = ([W_gamma] - [W]) * P.
W       = (U, f_off_j, omega + vrv(f_j)).
W_gamma = (U, f_off_j, omega + vrv(f_j) + gamma).
~~~

The intrinsic RV tensor presentation is intact. For a presentation q:T -> B,
the new target is T / q^{-1}(J_var); an unchanged factorwise scalar-radius
formula does not follow. The introduction already announces the relative
quotient. The remaining mismatch in Section 7 is intentional pending this
next work, not proof that its scalar theorem has already been repaired.

## Section 7: construction and proof plan

First check the [weighted-zero compatibility boundary](UPSTREAM-WEIGHTED-ZERO-AUDIT.md):
preserve the entire density on degree-zero factors and weighted finite
families. Do not substitute an ordinary-zero upstream measured theorem
for a weighted local interface, and do not infer I = J_var from density
absorption. The local Section 6 constructions remain checked at the
recorded pins.

Read the main statements and proofs independently before the referee notes.
The existing [mathematical draft](<section 6/reference/downstream-kernel-and-preservation-draft.tex>)
is a starting argument to verify, not a completed Section 7 or Section 8
formalization. The [short handoff](<section 7/SECTION6-HANDOFF.md>) and
[full earlier handoff](<section 6/reference/downstream-handoff.txt>) provide
additional context. The following order keeps the new kernel noncircular.

1. **Synchronize 7.2 and define the actual operations.** For a positive-degree
   measured RV object (U,f,omega), require the inactive structural projection
   to be finite-to-one. Use exactly the bounded nonzero function tau above.
   Replace the fixed product annulus with the relative shell
   0 < vrv(s) <= gamma(u), disjoint from a separately tagged endpoint
   s = tau(u). Its structural coordinate j is s*f_j(u); the others and the
   pulled-back form are retained. Keep the full graph, even for infinite
   image. At depth zero the shell is empty and the endpoint is still tau(u),
   including valuation-zero endpoints other than 1. Infinite aperture is not
   an operation in the doubly bounded category. Instantiate finite blowup
   words and the relative congruence, rather than merely postulating them.
2. **Prove common refinement and congruence.** Pull apertures back through
   actual measured isomorphisms. Partition by the pointwise depth order;
   on the smaller distinguished endpoint use the ratio of the two aperture
   functions, then multiply the new shell parameter by the old endpoint.
   Check bounds, tags, finite structural fibres and exact total weights.
   Include equal depths with different endpoints and empty-locus identity
   padding. Prove iteration, disjoint unions and products. Do not choose a
   global coefficient to stand in for a variable function.
3. **Construct both special/blowup directions.** In special:to:blowup:coa,
   prove the finite inactive projection condition: after fixing an inactive
   VF representative, the focus is an RV-to-VF map and has finite image.
   For blowup:same:RV:coa, use the continuous finitary lifting construction
   of 6.30 on the complete source/endpoint correspondence over the full
   inactive VF input. Construct actual centres b_0,b_1 with the two required
   leading terms; the core translation is x-b_0+b_1. Prove source membership,
   full branch images, inverse, proper covariance, double bounds, retained
   labels and the AE measure identity. A choice c in tau(u)^sharp is not an
   available global definable section. Obtain the unary kernel from revised
   6.38 and these actual constructions.
4. **Complete witness descent in 7.14.** At isp:VF:fiberwise:contract,
   uniformize the whole finite witness: loci, structural maps, intermediate
   forms, complete aperture graphs, final isomorphism and inverse. Freezing
   only aperture valuations or the original forms is insufficient. Protect
   original domains and every form level; check the current product-domain
   condition for each FMT replacement. Descend the actual full row to the
   RV quotient over the original base. Construct named aperture bounds
   after descent; do not assume a uniform bound in the initial VF parameter.
   Include arbitrary head starts and general VF-base dimension.
5. **Finish same-order and two-cell comparisons.** At
   contraction:same:perm:isp, use a common invariance radius for both source
   pairs, both first contracted pairs and their forms. Include measure and
   differentiability failures in the bad set. An ambient AE identity does
   not automatically hold on every unary fibre. At decom:into:2:units,
   supply the exact RV-affinity in the paper's definition; valuation-affinity
   alone is weaker. Prepare whole RV-slope and disc-image relations, using
   the checked local-linearity/subball/full-row inputs. Verify paradigms,
   protected fibres and proper covariance. Then assemble the balanced-cell
   measure calculation, form preparation and adjacent-coordinate swaps.
6. **Prove the actual kernel and 7.26.** At kernel:L, handle degree zero,
   short relatively unary chains, consecutive maps in the same coordinate,
   every arrow including the last, and endpoint tautological contractions.
   After an RV contraction, do not assume that adjoining its new RV name
   leaves the ground VF-generated. Use the lifted VF representative and
   the full-witness descent/head-start argument. Prove both directions of
   the congruence characterization and the ring ideal identification with
   the independently defined J_var. Do not define J_var to be the lifting
   kernel and thereby assume the conclusion. Combine this with the checked
   lifting surjectivity, justify groupification without an unwarranted
   cancellation assumption, and update thekernel, main:prop (7.26) and the
   comparison corollary db:to:novol. Retain the old scalar Section 4 statements
   as statements about I; do not rename I to J_var.

Pending referee items provide useful audit locations, not automatic approval
of their proposed repairs. In particular: R118–R120 concern zero/infinite
apertures and refinement; R171 the finite inactive projection; R124 the
continuous tagged lift; R125 whole-witness constancy; R126 common-radius
and good-fibre reduction; R130 stronger RV-affinity; R132–R133 balanced-cell
and form preparation; R134–R135 chain bookkeeping and base descent;
R136 the old scalar generator calculation. Bibliographic, codomain, torsor
intercept and notation comments also remain in the unedited Section 7 text.
Independently resolve them and retain the review history.

## Checked inputs worth opening before building replacements

| Need | Existing source |
| --- | --- |
| New arbitrary-arity primitive and chain | [RelativeApertureData](<section 6/RelativeApertureData.lean>), [RelativeApertureChains](<section 6/RelativeApertureChains.lean>), and their bounds, graph, core membership/saturation and homeomorphism modules |
| Old/new inclusion and complete unary matching | [ScalarApertureInclusion](<section 6/ScalarApertureInclusion.lean>), [UnaryApertureInclusion](<section 6/UnaryApertureInclusion.lean>), [BoundedVariableUnaryMatching](<section 6/BoundedVariableUnaryMatching.lean>) |
| Continuous finite lifting and measured preparation | [UnaryFinitaryLifting](<section 6/UnaryFinitaryLifting.lean>), [UnaryLiftingFieldBase](<section 6/UnaryLiftingFieldBase.lean>), [MeasuredExistenceFieldBase](<section 6/MeasuredExistenceFieldBase.lean>), and the standard-contraction/head-start exports in [Section.lean](<section 6/Section.lean>) |
| Full frozen RV row descent | [FrozenRVWitnessDescent](<section 6/FrozenRVWitnessDescent.lean>), especially the exact quotient row, protected membership, form equality and complete-witness validity transport; actual blowup-word instantiation is still required |
| Exact RV-affinity ingredients | [RVLocalLinearity](<section 6/RVLocalLinearity.lean>), [RVSubballSpecialization](<section 6/RVSubballSpecialization.lean>), [RVLinearRadiusClosure](<section 6/RVLinearRadiusClosure.lean>); these are inputs, not the assembled two-cell theorem |
| Independent relative-ideal compatibility | [FunctionalApertureCompatibility](<section 4/FunctionalApertureCompatibility.lean>), [VariableApertureMeasuredComparison](<section 4/VariableApertureMeasuredComparison.lean>), [RelativeAnnularQuotient](<section 4/RelativeAnnularQuotient.lean>) and their ray/annular-domain modules; similarly named Section 6 files are compatibility imports |
| Discharged Gamma and ground-lifting inputs | [GammaQEFiniteLaws](<section 5/GammaQEFiniteLaws.lean>), [Completed18GroundLiftInput](<section 5/Completed18GroundLiftInput.lean>), [Section5DischargedInputs](<section 5/Section5DischargedInputs.lean>) |

Inspect each complete public type, its source/codomain representation and
all base hypotheses. Supplying a convenient abstract certificate as a
premise is not the same as constructing it from the original paper object.

## Section 8 and whole-paper consequences to preserve

Carry forward [the Section 8 handoff](<section 8/SECTION6-HANDOFF.md>).
Its specialization must use the entire retained aperture/endpoint graph.
At fixed m, the intended trace uses integral M = m*gamma and an annular
factor L*T^(-1)-1. The algebraic identities in
[FiniteApertureSpecializationFactors](<section 6/FiniteApertureSpecializationFactors.lean>)
are checked; the complete equivariant geometric adapter is not.
Natural quotients must use J_var intersected with the relevant natural
subring. Global scalar-aperture or equal-cutoff arguments do not alone
verify this. Final specialization values, zeta rationality/limit and the
Milnor-fibre theorem must be checked at their actual hypotheses.

The approved Section 5 integration also leaves two undefined Section 8
references, bipo:desc and shift:K:csn:def. Resolve their current counterparts
there. Existing truncation and bounded-summability issues are separate from
the aperture repair. Record downstream obligations explicitly rather than
claiming whole-paper preservation from an upstream compatibility lemma.

## Working protocol

1. **Read and reconstruct the mathematics first.** For each target, read the
   actual statement, proof, conventions and cited hypotheses independently.
   Then assess the referee report. Distinguish a false assertion, a missing
   justification and an optional explanation. Work in paper order, recording
   a precise forward dependency and returning to the target after it is proved.
2. **Keep source and scope honest.** Record the source version, stable label,
   printed result number, exact parameters and any accepted external input.
   Prove original-base definability, bounds, continuity, finite structural
   fibres and actual maps/inverses where the paper requires them. Include
   empty and zero-arity cases. Do not replace actual objects by toy models
   and report the latter as the numbered theorem.
3. **Apply obvious corrections directly.** The author requests autonomous
   completion and input only for critical mathematical decisions. Do not
   stop after a routine edit, supporting lemma or build milestone. For a
   further substantive mathematical departure, first make the proposed
   repair concrete and check its upstream/downstream consequences, then
   seek the author's review. Continue independent work while waiting.
4. **Review mathematical changes in paper context.** Present one or two
   correction items at a time, in paper order, in an actual PDF with proposed
   changes in a contrasting colour. Wait for the author's reading before
   moving to the next critical review batch. The previous program used a
   right-side PDF panel; a program without that UI should provide the PDF
   file/link directly. A TeX editor or separate prose summary is not a
   substitute for the contextual review PDF. After approval, incorporate
   the change, gray the original referee item and add a brief resolution.
5. **Formalize the actual final statements.** Keep the adopted manuscript and
   Lean class synchronized. Distinguish a complete numbered result from a
   supporting lemma or a conditional interface. No sorry/admit/custom axiom
   may stand in for a required local proof. Preserve the source of every
   already authorized external input. Prove needed HK arguments locally.
6. **Verify the relevant final state.** Follow the existing section audit
   pattern: registered modules and root imports, full printed public types,
   transitive logical axioms, exact pins and source hashes. Only propext,
   Classical.choice and Quot.sound are permitted logical principles.
   Check adapters against their full types; an axiom audit does not by
   itself show that all mathematical premises were discharged. Add Section 7
   to Lake, the root entry point and CI as its implementation is assembled.
   Rerun affected upstream checks if definitions or shared sources change.
7. **Maintain a usable project state.** Preserve uncommitted work, exact
   dependency overlays and author-approved decisions. Keep concise status
   notes separating manuscript review, supporting native proofs and complete
   numbered results. Do not claim completion from declaration counts.
   Publish the final verified changes when instructed, with a clear commit
   description and explicit remaining downstream boundaries.

## Reproduce the published build in another program

Use the toolchain in [lean-toolchain](lean-toolchain): Lean 4.35.0. Activate
it using your own environment (for example elan). The commands below are
POSIX-shell examples, run from the repository root. They require no private
activation script or Codex-specific path.

~~~sh
git clone https://github.com/daviddhilbert/diamond-integral.git
cd diamond-integral
lake update
python3 'section 5/prepare-dependencies.py'
python3 'section 5/prepare-dependencies.py' --check
lake build DiamondIntegral
lake env python3 'section 2/verify.py'
lake env python3 'section 3/verify.py'
lake env python3 'section 4/verify.py'
lake env python3 'section 5/verify.py'
lake env python3 'section 6/verify.py'
~~~

Keep the checked package revisions in [lake-manifest.json](lake-manifest.json):

| Package | Revision |
| --- | --- |
| mathlib | 56a005855ea17e0b0958f73ec801ae140b0a1679 |
| acvf_qe | 939346b0a99899e22a873479364e3cc5d142731c |
| special_transformations | 25852c85a31c67069b148bd31348128318303510 |
| integration_in_acvf | 7675d31332f20421c803ea16af84964ed74cd51f |

Dependency preparation checks the published 250 completed Section 5 files and
39 proper-open-radius sources, then restores only the two recorded Section 6
hypothesis-scope adapters. Their actual proof producer is retained. Preserve
unexpected local modifications. The preparation script checks revisions and
hashes; `--check` performs a read-only check. See the
[migration record](verification/upstream-weighted-zero-upgrade/README.md) for the
new-pin receipts and the surviving conditional mathematical boundaries.

Current dependency compatibility evidence is in
[the corrected-pin receipt](verification/upstream-weighted-zero-upgrade/status.json).
The earlier manuscript aperture-revision evidence is in
[integrated-audits.json](<section 6/verification/aperture-revision/integrated-audits.json>),
[the source-hash check](<section 6/verification/aperture-revision/final-source-hash-check.json>)
and [the completion boundary](<section 6/verification/aperture-revision/completion.json>).
Section 3 uses VERIFICATION.json; the other section receipts use status.json.
The receipts certify the checked source state and their documented scopes.
Once you change a proof or shared interface, refresh the affected receipts.

## What completion of the next task must mean

The expected Section 7 deliverable is a synchronized 7.2 and 7.26 with all
intermediate results proved in their actual scope, both kernel directions,
the explicit J_var quotient and comparison diagrams, an implemented native
Section 7 library and audit, and any required Sections 1–6 changes verified.
Record remaining Section 8 obligations clearly. A draft proof, a family of
supporting lemmas or a quotient defined to equal the desired kernel is not
that deliverable. The supplied original PDF/report, this note and the public
repository are enough to begin without reconstructing private chat history.
