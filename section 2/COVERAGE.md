# Current §2 implementation coverage

The project entry point builds with Lean 4.35.0. The latest complete audit
(November 18) passes **970 public section theorem declarations and 378 selected reuse
declarations**. Counts include supporting results. Exact types and their
logical principles are in [the audit](verification/headline-audit.txt);
[the machine record](verification/status.json) fixes the source state.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The refreshed
audit in `.scratch/section-2-final-disc-ground-verification.log` records the approved
current manuscript hash.

“Checked” below means the statement in the listed formal scope. It does not
assert one universal imaginary-parameter transport theorem for the entire
section. Canonical encodings, characteristic, genuine saturation, smallness,
compatible valuations and generation hypotheses remain explicit in the
individual theorem types. The nine cited interfaces are
[recorded separately](verification/CITED-INPUTS.md) and are replaceable.
The results of [18, §3] now have [proved upstream source links](verification/UPSTREAM-LINKS.md).
All nine are now discharged (November 18). The eight numbered [18, §3]
interfaces have checked constructors, and
`section 3/Section2CitedInputsDischarged.lean` restates the 20 statements that
still took them without those arguments (2.27, 2.28, 2.30 and 2.32 already
had `integration_*` wrappers in section 3). The Γ rational-affine input
`GammaPiecewiseRationalAffineInput` is proved
(`Section5.GammaQE.gamma_piecewise_rational_affine`, from RV quantifier
elimination), and `section 3/Section2GammaLinearityDischarged.lean` gives
`_discharged` versions of 2.41, 2.47 and 2.53. The original §2 statements
still carry the inputs as parameters.

| Main text | Implementation | Scope and result |
|---|---|---|
| 2.1–2.7 | `Conventions`, `RVHull`, `Continuity`, `Bases` | Existing ACVF-QE VF/RV/Gamma sorts, fixed real/Gamma bases, singleton zero RV fibre, retained labels, hull and labelled composition. |
| 2.8 | `GammaJacobian` | Actual finite RV/Gamma labels, arbitrary source/target arities; agrees with the companion RV Jacobian. |
| 2.9 | Existing ACVF-QE syntax and normalization | The language/top-term convention is reused; no new global formula-normalization result is asserted. |
| 2.10 | `Discs` | Uniform finite open-radius codes and closed codes including singleton infinity; approved companion correction retained. |
| 2.11 | `Henselianity`, `AlgebraicEnvelope` | Checked henselianity equivalence for a VF-generated real substructure with nontrivial value group. |
| 2.12–2.13 | `FiniteSets`, `FiniteSetsGammaNames` | Finite VF sets coded in nonzero RV; VF algebraicity descent from RV names. `lemma_2_12_gammaNames`: 2.12 over a real base with Γ names. |
| 2.14–2.15 | `Exchange`, `ExchangeGeneral`, `FiniteFibres` | Scalar exchange and the finitary unary-source assertions, with the original base retained. `lemma_2_14_vf_general` and `lemma_2_15_vf_general` remove the `VFFieldBase S` premise of the VF versions (any small base `S`). |
| 2.16–2.17 | `Dimension` | Interior/projection dimension, empty value −∞, full-dimensional open-polydisc criterion including zero arity. |
| 2.18 | `PolydiscAlgebraicity` | Algebraicity descent over actual finite-radius open/closed disc tuples; full invariant relation and generic-centre elimination. |
| 2.19–2.21 | `DiscPoints`, `GeneralDiscPoints`, `section 3/Lemma220SmallBase` | Real/Gamma ground-base disc points; the generation and temporary-closure size conditions of the general-centre bridge are explicit. `lemma_2_20_algebraic_small`, `lemma_2_20_definable_small` assume only `#S < κ`, `#G < κ` with `ℵ₀ < κ`. |
| 2.22 | `Atomic`, `DiscGroundBridge` | Complete-type generation and atomicity; fixed ground definability is retained. |
| 2.23 | `AtomicBaseChange`, `CitedDiscAtomicity` | Integration of accepted [18, Lemma 3.3], including existing finite disc prefixes. Input-free `_discharged` versions in section 3. |
| 2.24 | `AtomicPolydiscs`, `AtomicDiscGroundChange`, `AtomicImaginaryGround` | All finite source arities; proved real/Gamma case, and finite-DC-prefix case relative to unary [18, Lemma 3.9]. Finite RV tuples and singleton ground names included. Input-free `_discharged` versions in section 3. |
| 2.25 | `NamedPolydiscAtomicity`, `PolydiscAtomicity`, `PrefixedPolydiscCharts` | Full open and closed Γ∞ radius tuples, arbitrary singleton coordinates and zero arity; existing finite DC ground names retained, relative to the accepted unary/Gamma inputs. Input-free `_discharged` versions in section 3 (saturation stated where the atomicity constructor needs it). |
| 2.26 | `RVImage`, `AtomicImages`, `NamedRVConstancy` | RV-image constancy over real/Gamma bases and existing finite DC ground names, including empty and zero-tag branches. Input-free `lemma_2_26_disc_names_discharged` in section 3. |
| 2.27–2.28 | `CitedUnaryImages`, `CitedDiscRVImages` | Integration of accepted unary [18, Lemmas 3.8 and 3.13]; the unary scope is retained. |
| 2.29 | `PolydiscImages`, `TaggedPolydiscImages`, `NamedTaggedImages` | Finite branch decomposition, original-base image atomicity and proved coordinate-chain geometry; existing finite DC ground names, constant zero branches and empty tag families included. Input-free `_discharged` versions in section 3. |
| 2.30 | `FinitaryPolydiscPartition`, `NamedFinitaryPartition` | Full finite disjoint partition over the original small real base plus any fixed finite DC ground tuple. Uniform good-code formula, type-local atomicity, both compactness steps and full branch graphs proved. The DC extension makes the infinite saturation cardinal explicit; branches add only their actual polydisc names and RV tag. |
| 2.31–2.32 | `DiscToDisc` | Definition 2.31 and accepted disc-to-disc partition Lemma 2.32; input/output RV labels retained. The Lean export is correctly numbered `lemma_2_32`; `Section3.integration_lemma_2_32` supplies the input. |
| 2.33–2.35 | `RVDimension`, `BoundaryDimension`, `BoundaryCoordinates` | Empty value −∞, boundary definability and full multivariate strict dimension bound, including zero-coordinate faces. Input-free `lemma_2_35_discharged`, `lemma_2_35_vf_discharged` in section 3. |
| 2.36 | `AlmostContinuity` | Integration of checked [17, Lemma 8.7], with the original-base closed exceptional set and manuscript dimension. |
| 2.37–2.38 | `Differentiation`, `Jacobian` | Mixed VF Jacobian, equal VF arities, generic RV-label constancy, lower-dimensional exceptions and zero-dimensional determinant 1. |
| 2.39 | `Boundedness` | Coordinatewise `valim`, finite existential bounds and the distinction from minimum tuple valuation. |
| 2.40 | `Contractions` | Quotient descent, uniqueness and actual mixed RV contraction retaining labels; definable companion map reused. Generic coordinate-map version supplies residue/valuation formulations on their domains. |
| 2.41 | `RVGammaBounds`, `RVBoundCoordinates`, `RVBoundedImages` | Full RV- and Gamma-valued conclusions in every arity. Proves the author's supremum induction. The Gamma piecewise-linearity parameter is discharged in `lemma_2_41_discharged`, `lemma_2_41_gamma_discharged` (section 3). The Γ-ground statement is `Section3.lemma_2_41_gammaGround` (and `_discharged`). |
| 2.42–2.43 | `Limits` | Approved local limit definition, equivalence with the redundant subfamily formulation, and checked cited uniqueness up to closure. |
| 2.44 | `FinitaryContinuity` | Actual finite-valued almost-everywhere continuity, positive source dimension, including empty finite values. |
| 2.45 | `FiniteLimits` | Finite minimal limits for bounded finite correspondences on the punctured valuation ideal. |
| 2.46 | `CurveSelection` | Full projective curve selection, including infinite target coordinates and zero target arity, with the approved local VF-generation hypothesis. |
| 2.47 | `GammaCurveSelectionFailure` | `remark_2_47`, `remark_2_47_no_approach`: no definable curve in `Γ × (0, ∞)` approaches `(∞, 0)`. Γ-linearity discharged in `remark_2_47_discharged`, `remark_2_47_no_approach_discharged` (section 3). `remark_2_47_diagonal` only records that the diagonal has points near `(0, 0)` and `(∞, ∞)`. The diagonal case is illustrative and was not pursued further (author-approved triage). |
| 2.48–2.49 | `ClosedBoundedImages`, `ClosedBoundedHomeomorphism` | Closed bounded image and actual homeomorphism, constructing a temporary small VF-generated base internally. |
| 2.50 | `ClosedGraph`, `BoundedClosedGraph` | Actual projective closed-graph criterion and its bounded affine version. |
| 2.51 | `WeakConcentricity` | Full unary weak concentricity; the specified-centre power law and inverse neighbourhood control are proved from checked prequel results. |
| 2.52–2.53 | `OpenDiscPartitions`, `PartitionBoundedMixed` | Full mixed partition bound; fibre bounds and the original-base endpoint-bound graph are constructed, then 2.41 supplies uniformity. Γ-linearity discharged in `lemma_2_53_discharged`, `lemma_2_53_image_bounds_discharged` (section 3). |
| 2.54 | `FibrewiseOpenness` | Open and closed cases over a fixed unary base, allowing empty fibres and zero tail arity. |
| 2.55 | `FibrewiseContinuity` | Full finite original-base exception and joint continuity via the two projective graph charts, including zero tail arity. |

Also proved (unnumbered): `gamma_stably_embedded` (`GammaStableEmbedding`):
Γ is stably embedded, with the induced structure of a divisible ordered
abelian group. Not pursued, by the author-approved triage of November 18
(see [GAP-REPAIRS.md](GAP-REPAIRS.md)): the diagonal case of Remark 2.47, the
unnumbered HK fact after Definition 2.16 (VF-dimension equals Zariski
dimension), and Γ-ground 2.41 when Γ is nontrivial only through names.
Convention 2.9 is a syntax convention with no export.

## Approved source clarification

The author approved the green clarification in Lemma 2.24's proof. It is now
applied to the working manuscript, and R029 is fully resolved with a brief
explanation. Previously named disc parameters use accepted [18, Lemma 3.9];
the existing real/Gamma proof and product induction are retained. This does
not extend Corollary 2.21 beyond its stated hypotheses. See printed pages
16–17 of [the updated extract](reference/disc-ground-base-resolved-review.pdf).
The original unapplied proposal is retained as review history. The updated
extract is queued in the right panel; visibility is unconfirmed. No source
approval is pending.

All tracked numbered §2 targets are now implemented in the scopes above.
The final disc-ground extensions of 2.25, 2.26, 2.29 and 2.30 have passed
the complete entry-point/type/principle audit. The finite disc-name
infrastructure proves parameter promotion, complete-type fibres and
original-DC compactness. See [the proof review](verification/DISC-GROUND-REVIEW.md). A general-purpose package for arbitrary sets of DC
ground names, or a bridge for every extra improper library code, has not
been asserted. Individual formal scopes above remain the completion boundary;
future sections should use the stated interfaces rather than silently
strengthening their parameter hypotheses.

The original upload is preserved, and the 30-file approved finite-open-radius
companion patch and all existing uncommitted work are retained. Nothing has
been committed or pushed.
