# Lean formalization plan

**Forey and Yin, _Bounded integral and motivic Milnor fiber_**

Current checkpoint: §§2–3 are formalized in the documented manuscript
contexts, relative to the explicitly accepted cited inputs. Section 3
includes the corrected positive tensor kernel congruences, their actual
ring ideals, the ordinary positive coefficient monomorphisms and both
full-ground affine classifications. See [§3 status](<section 3/STATUS.md>)
and [the manuscript target map](<section 3/verification/paper-targets.json>).
No HK result is a given input. The supplementary unary-ray refinement
was explicitly skipped by the author.

The working source is
[the annotated TeX](<section 2/reference/diamond_integral_revision_annotated.tex>),
with [its PDF](<section 2/reference/diamond_integral_revision_annotated.pdf>)
for printed numbering and pagination. The unmodified upload is preserved in
`section 2/reference/original-upload/`. Author-approved resolutions of all 30 §2 annotations are recorded in [the section status](<section 2/STATUS.md>).
Use LaTeX labels as stable identifiers across revisions. Record the manuscript
version, printed number, and relevant purple referee or blue author notes when
opening a target. Keep the annotated source as the reference for proposed
corrections.

## Layout and order

Section 1 is the introduction. Record its technical claims in the sections
where they are defined and proved.

| Folder | Annotated PDF | First work and exit milestone |
| --- | --- | --- |
| [section 2](<section 2/README.md>) | pp. 10–24 | VF/RV/Gamma/DC conventions, parameter bases, discs, atoms, continuity and fiberwise results. Start with §2.1 and Lemma 2.11. |
| [section 3](<section 3/README.md>) | pp. 25–28 | Grothendieck constructions and VF, RV, RES and Gamma categories with and without volume forms. Establish lifting and the two HK integral presentations at their stated parameter scope. |
| [section 4](<section 4/README.md>) | pp. 29–35 | Prove the unmeasured and measured retractions to their respective RES targets. Verify Euler characteristics, convolution, interval generators and factorization through each quotient. |
| [section 5](<section 5/README.md>) | pp. 36–46 | Prove the reduced-section and twistoid lemmas, then tropical Fubini and the fiberwise equality theorem. Track witness uniformization and arithmetic residue descent separately. |
| [section 6](<section 6/README.md>) | pp. 47–61 | Prove proper covariance and standard contraction results, then lifting into the proper invariant categories. Audit Jacobians, global bounds, continuity and finite RV fibers under the actual operations. |
| [section 7](<section 7/README.md>) | pp. 62–70 | Check the unary annular blowup relation, prove the 2-cell and contraction-order comparison, then identify the bounded lift kernel and construct the bounded integral (Theorem 7.26). |
| [section 8](<section 8/README.md>) | pp. 71–80 | Prove the equivariant fixed-order coefficient comparison, rationality and the limit identity for motivic Milnor fiber (Theorem 8.11). Track the extended bounded zeta construction separately. |

Read and specify targets in paper order. For a forward dependency, identify
the exact statement and schedule the smallest prerequisite first. Record the
dependency and resume the section after its proof. In particular, §5 cites
preparation whose bounded counterpart is developed in §6. Its unbounded
polynomial preparation target can be compared directly with Yin's
*Special Transformations*, Theorem 5.5.

## Reuse and compatibility

- Use the existing two-sorted ACVF language. This project pins Lean `v4.35.0`,
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and
  [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE) at
  `939346b0a99899e22a873479364e3cc5d142731c`. Check companion developments
  against these versions before importing their modules.
- In [*Special Transformations*](https://github.com/daviddhilbert/special-transformations),
  inspect the section libraries and their verification records. Start with
  `Section3.BallGeometry`, `Section3.GeneralBallCenters`, `Section3.VFAlgebraicity`
  and `Section3.GammaBaseCMinimal`. Sections 4–7 supply candidates for
  categories, dimension, special bijections, henselian descent and lifting.
  Sections 9–10 supply Jacobian and measured-lifting candidates. Published
  checkpoints, local repairs and explicit hypotheses have separate status.
  The local open-disc correction is an explicit patch over revision
  `9cc9760892092dd34cfad4a6dee655843c52f30c`; run
  `python3 'section 2/prepare-reuse.py'` after materializing dependencies.
  It matches the changes in `/workspace/special-transformations` and avoids
  an absolute-path Lake dependency. Replace the patch with a published pin
  when publication is authorized.
- The [Integration in ACVF](https://github.com/daviddhilbert/integration-in-ACVF)
  dependency pins `7d4acc730496b3bd05a22c268ffd89540ca694f9`.
  Eight original §2 cited interfaces have checked native constructors.
  Exact later §6 exports are also linked; they retain the unfinished §5.8
  input and native closure/category conditions. Preserve explicit accepted
  lift records until the remaining comparison maps are compiled. Measured
  §7 is not yet available. The exact review and compatibility patches are
  recorded in [the reuse inventory](<section 3/verification/integration-reuse.json>).
  Preserve parameter scope, proper invariance and boundedness, and
  distinguish accepted inputs from compiled proof exports.
- The same authorization applies to bibliography items 19–22. Exact titles,
  citation keys and the explicit-input convention are recorded in
  [ACCEPTED-CITED-RESULTS.md](ACCEPTED-CITED-RESULTS.md).
- Compare definitions before importing each headline. Preserve equicharacteristic
  zero, the actual parameter base and saturation requirements, the single
  RV zero/infinity element, the reversed valuation order in the existing Lean
  encoding, and the distinction between an RV class and a value-group fiber.
  In particular, distinguish VF-generated, (VF,Gamma)-generated, arbitrary
  RV-parameter, and disc-imaginary bases. Track descent back to the original base.

## First proof session

1. Inspect the target repository and check that the QE package and selected
   Special Transformations modules build at a compatible revision.
2. §2.1 conventions and R022–R024 have been implemented under the author's
   approved interpretations: the singleton zero RV fiber, preservation of RV
   tags, uniform disc maps and finite open radii. Composition retains intermediate
   RV labels. The original fibrewise topology remains in use; the theorem here
   does not constitute an independent audit of every later application.
3. Lemma 2.11 (`cut:to:hensel:substru`) is proved and audited in the canonical
   encoding of the paper's two-sorted language. The base interface distinguishes
   language generation from definable closure, records the VF field and RV
   representatives, and retains the nontrivial valuation witness. The reverse
   proof constructs the algebraic envelope and discharges its Galois and
   valuation-invariance premises internally. Exact scope is in the section status.
4. Lemmas 2.12–2.15 are proved and audited in their recorded scopes. Finite-set
   internalization gives an actual bijection onto a definable set in nonzero
   RV; algebraicity descent keeps all finite tuple arities and the original
   base. The author confirmed scalar exchange and clarified that 2.15's literal
   subsets already mean one coordinate. The 2.14 scalar scope is explicit;
   2.15's statement and proof are unchanged. Both VF/RV forms of 2.14–2.15
   are proved over the real base. The approved empty-set value −∞ (R164)
   and component-disc parameter clarification (R027) are applied. The separate
   R032 boundary wording and R033 proof clarifications are approved and applied.
5. Direct VF/RV dimension definitions and Lemma 2.17 are implemented, with
   the empty and zero-coordinate cases. Closed-disc points (2.19), the proper
   disc-intersection corollary (2.21), C-minimality and complete-type vocabulary
   are in the section modules; see the status record for verification scope.
   The author-approved nontriviality assumption for Γ(S) is now standing
   throughout the paper (R028), matching [18]'s blanket hypothesis. The
   former permission for trivial Γ(S) at the opening of §6 is removed.
   Check later arguments for an actual need for triviality and report a
   genuine conflict before changing scope.
   Both cases of 2.20 and the language-generation-to-dcl bridge are
   implemented in the recorded real/Gamma field-base scope. 2.24 is proved
   in all finite VF arities and for finite tuples of RV names. 2.18 is
   exported for the explicit finite-radius DC charts, with code invariance,
   generic-point construction and descent back to the original base.
   2.26 is proved from the full VF-function graph, with zero RV tags retained.
   The approved thin-annulus definition is applied (R163). 2.23 and the
   geometric parts of 2.27–2.28 retain explicit author-accepted cited inputs.
   The finite tagged branch construction, original-base image atomicity and
   the general ACVF rectangle-image lemma are proved. 2.29 reconstructs the
   full finite RV∞-indexed branch family, with point or atomic open-disc
   images, using only the accepted unary input from [18] at temporary bases.
   The coordinate-chain proof and zero-tag clarification for 2.29–2.30 are
   approved and applied. R031's disc-parameter and compactness clarification
   is approved and applied. The finite DC-ground interfaces for 2.25,
   2.26, 2.29 and 2.30 are now implemented and audited.
   Mixed-output definability, logical operations and complete-type
   vocabulary over actual finite-radius DC names are implemented, with a
   ground-formula bridge. The completed 2.25 and 2.30 scopes are recorded below.
   Unary boundary finiteness/definability, the zero-coordinate case, finite
   RV dimension and the coordinate-exit witness for the induction are proved
   in their recorded parameter scopes. Full multivariate 2.35 is now proved
   over a small original real base, including zero arity and zero RV factors.
   R034–R036 are approved and applied with brief resolutions in their PDFs.
   Tuple valuation and punctured differentiation, matrix indexing, and generic
   RV-label constancy are implemented in their recorded scopes. Scalar and
   unary tuple DC-name interfaces now agree; full 2.25 is assembled in its
   finite DC-ground and closed Γ∞ chart scope. Mixed-map 2.38 is now assembled over real parameter
   bases, including zero arity, using checked fixed-label derivatives and
   the definable Jacobian value map. Coordinatewise boundedness is implemented. R037’s original induction is retained and its definable-bound step is
   explicit. R038 is approved/applied. Actual Gamma suprema and their same-base
   definability, affine local limits and Lemma 2.43 are implemented. Both
   conclusions of 2.41 are now proved in every finite arity. R039 proof/arity changes and R040/R165 curve selection
   are approved/applied. The RV-union principle for the manuscript dimension,
   finite-branch minimal limits and 2.45 in the real-base scope are implemented.
   R041/R042 geometric revisions and R166 wording are approved/applied.
   R043/R044 details are applied as author-agreed expansions of compressed
   proofs; their statements are unchanged and the arity objection is withdrawn.
   Independently reconstruct each main proof before assessing the report.
   R045’s independently reconstructed fibrewise-openness proof is approved
   and applied. R046’s relative graph-closure details are approved and applied.
   Relative fibre closures and the Hausdorff graph-intersection identity are
   proved topologically; uniform definability and full 2.54/2.55 remain. The actual Gamma-indexed finite-union theorem and its
   infinite-fibre contrapositive are proved over the same real base. The unary singleton-limit
   theorem and the pure VF partition lower-bound/escape arguments are proved
   in the recorded scopes; full 2.51 and 2.53 remain.
   Lemma 2.36 integrates quoted [17, Lemma 8.7] via its checked existing proof;
   the dimension-convention bridge is new local work, not a new cited proof.
   Full Lemma 2.44 is now assembled over the original real base, including empty
   finite fibres and the approved n>0. Its helper modules implement uniform RV
   codes, inverse branches and the same-base exceptional locus.
   The finite-radius open/closed 2.25 is now assembled from accepted [18, §3]
   unary and Gamma inputs, including zero arity and nondefinable containing
   sets. The closed Γ∞ case now includes singleton coordinates in arbitrary
   positions through proved name charts. The open/closed wrappers retain only
   the accepted unary and Gamma inputs, with no chart-existence premise.
   Arbitrary additional DC ground bases remain a separate transport task.
   The affine case of 2.46 is now assembled over the VF-generated base plus b:
   finite nonempty values, continuity on 𝓜\{0}, and minimal limit {b}.
   Algebraic modelhood, finite choice, finite exception and clopen extension
   are constructed. The full coordinatewise projective 2.46 is now assembled:
   reciprocal charts include infinity and retain the original base plus b,
   with finite-limit transport proved. Full 2.48 is now assembled over an
   arbitrary real base: a countable temporary VF-generated base is constructed
   from finite defining parameters, and relative continuity proves both image
   closedness and boundedness. Corollary 2.49 now constructs the actual
   homeomorphism onto f(A). The two-chart projective topology bridge and
   full closed-graph 2.50 are now assembled, including the bounded affine
   relative graph version. The open and closed cases of 2.54 are assembled
   over a fixed unary base with empty fibres allowed. Full 2.55 now gives
   joint continuity outside a finite same-base unary exception, using the
   actual projective fibre closures and both open affine charts.
   Corollary 2.30 now constructs the finite disjoint original-base partition
   and all tagged branch decompositions over a small real ground base.
   Its only geometric inputs are the accepted unary [18, §3] results;
   complete type loci, both compactness steps, coordinate chains, full
   DC-plus-tag graphs, point/open images and reconstruction are proved.
   Empty fibres, zero RV tags and zero source coordinates are included.
   RV finite-map calculus now includes the RV∞ arity bound, restriction,
   dimension monotonicity, finite unions, products, padding, reindexing,
   and the strict dimension bounds for finite projections and cylinders.
   Uniform choice from pointwise definable VF points is proved by singleton
   promotion, compactness and finite formula priority. The actual unary
   boundary family and its finite RV-injective representative correspondence
   now have full original-base graphs; the pointwise premise is discharged
   by 2.21. Its finite zero-face partition, retained-tag graphs, finite
   projection fibres, cylinder bounds and coordinate-exit coverage now
   assemble the full multivariate 2.35 induction. Its typed VF export
   retains the three existing unary [18, §3] inputs used in 2.30.
   Full unary 2.51 now supplies singleton limits, fixed-centre positive
   value laws, inverse-neighbourhood control and whole punctured-disc
   image equality, using checked prequel results and no new cited input.
   Uniform Gamma supremum graphs and fixed-value-fibre RV-to-Gamma
   finiteness now support the retained 2.41 induction. The pure Gamma
   case uses a ninth precise cited background input for piecewise
   rational-affine maps from [18, proof of 3.18]; full 2.41 is not assumed.
   Full 2.41 is now proved for both actual RV and Gamma outputs in
   every finite input arity, using the author’s original supremum induction
   and retaining all source tags and output Gamma codes. Mixed 2.53 and
   general additional DC-ground transport remain active.
   The latest complete audit covers 736 section theorems and 369 reused declarations;
   exact scopes are recorded in `section 2/STATUS.md`.

## How a lemma moves from manuscript to Lean

For each numbered target, record its LaTeX label, exact statement and
parameter base, dependencies, Lean declaration, referee IDs and proof status.
Group tightly related declarations into one module. Expose verified results
through a section entry point as sections acquire proof code.

Check each referee claim against the statement, the proof and its callers.
For a false claim, preserve a counterexample and propose a precise replacement.
For a proof gap, record the missing implication and attempt it under the stated
hypotheses. For a change of mathematical scope, keep the original statement
and the proposed correction in the record for author review. Apply accepted
corrections to the manuscript and Lean together.

A completed target has a passing build in the pinned environment, a checked
full theorem type, and a `#print axioms` audit of the actual export. Use the
existing project's standard allowance of `propext`, `Classical.choice` and
`Quot.sound`. Audit explicit premises separately and identify conditional
results as such. When correcting an earlier statement, recheck affected
exports in downstream sections.

## Specific obligations to track

- **§2, R023 and R040–R046.** Test the continuity convention under composition
  and verify the exact parameter and lifting conditions for curve selection,
  compactified graph arguments and the downstream openness claims.
- **§3–4, R053, R060 and R062–R071.** Put the generation hypothesis on the
  lifting map, distinguish measured and unmeasured quotient targets, and
  verify the domain and vanishing of each ideal generator.
- **§5, R088–R089 and R095.** Prove the Fubini statement first in the original
  definable RES target. For arithmetic realization, retain residue-field descent
  together with inertia and require the ramified quadratic counterexample as
  a test of any proposed restriction to unramified points. For VF-to-RV
  descent, check uniformization of the complete finite congruence witnesses.
- **§6–7, R102, R170 and R134–R136.** Check the locus where Jacobian equations
  hold under composition and whether an RV-hull preserves finite RV fibers.
  Prove the contraction-order comparison and parameter descent before
  deriving the global bounded kernel.
- **§8, R144, R146, R148 and R173.** Check the equivariant affine-action quotient,
  work first with the finite lattice trace at fixed order, and prove normalized
  class invariance under compatible truncation cutoffs. Test the shear in
  R173 before choosing a cutoff lemma. Give rationality, the limit map, and
  any extension beyond doubly bounded support their exact domains.


Earlier §2 checkpoint (superseded by the final inventory below): full mixed-coordinate 2.53, in
[PartitionBoundedMixed.lean](section%202/PartitionBoundedMixed.lean), now passes
the project entry-point build and audit (748 section theorems / 369 selected
reuse declarations). Its full RV-indexed image graph retains the original
base and tags. The uniform supremum of absolute fibre images is proved equal
to the approved endpoint bound and bounded by completed 2.41. Nine accepted
cited interfaces remain explicit. The later finite DC-ground extensions are recorded in the final inventory
below; no manuscript change was made for this implementation.


Current §2 numbered scope inventory:
[COVERAGE.md](section%202/COVERAGE.md). Latest full project audit: **850 public
section theorem declarations / 378 selected reuse declarations**, standard
three principles only. Finite DC-ground promotion, complete-type fibres and
2.24 product transport are checked relative to the existing unary [18 3.9]
input. The registry still has nine replaceable cited interfaces. Notation2.8
and Definition2.40 now have companion bridges; the partition citation is
correctly numbered Lemma2.32. The author-approved R029 citation clarification is now applied and R029 is
fully resolved; the updated PDF extract shows printed pages16–17. No source
approval is pending.

Final §2 integration is complete in the numbered scopes of COVERAGE.md.
`corollary_2_30_disc_names` in `NamedFinitaryPartition.lean` closes the last tracked
finite-DC-ground extension: original-base partition, uniform good-code
formula, both compactness steps and full tagged branch graphs are proved.
The DC wrapper makes infinite saturation cardinality explicit. The nine
accepted cited interfaces remain replaceable; no multivariable 2.25, 2.29
or 2.30 is assumed. The final verifier passes 850/378 and records the
approved unchanged manuscript hash. No source approval is pending.
