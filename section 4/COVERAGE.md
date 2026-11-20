# Section 4 coverage

All corrected main-text obligations are proved, and both T001 adapters are
constructed from finalized Section 3. The linked retraction propositions take
no T001 input. The manuscript review is resolved; no author decision is pending.
The current extract is printed pp. 40–48; stable labels identify passages
independently of pagination.

| Passage | Stable label | Checked implementation |
| --- | --- | --- |
| Definition 4.1 | `df:res` | `RVMeasuredCharts`, measured/ordinary RES rings, full gradings, and dimension-free point localization. The graded RES[*] rings have finite-union presentation equivalences (`RESDisjointPresentation`, `RESOrdinaryDisjointPresentation`, `RESDisjointGrading`). The dimension-free ring is `RESDimensionFreeRing.Ring`: the ordinary RES ring modulo underlying-bijection relations across degrees, whose ideal is `([1] - 1)` (`degreeIdeal_eq_pointIdeal`, `normalizationEquiv`). The dimension-free category itself is built in `RESDimensionFreeCategory`: objects `Object` (definable RV sets with finite value support, i.e. RES[*] objects with the label forgotten), morphisms `Iso` (all definable bijections), and its Grothendieck ring `RESDimensionFreeCategory.Ring` presented by bijections, the empty object, the unit, cartesian products (`product`) and tagged disjoint unions (`sum`, domain `taggedSet`). Every object underlies a RES[k] object (`exists_label`, label `unzero` coordinatewise). `definition_4_1_identification` gives a ring isomorphism `RESDimensionFreeCategory.equivalence` onto `RESDimensionFreeRing.Ring` sending `[U]` to the class of any RES[k] object `(U, f)` and commuting with the forgetful maps from the graded ordinary and measured RES rings (`equivalence_forgetLabel`, `equivalence_forgetMeasured`). The provider module docstring's "separate obligation" is discharged there. |
| Remark 4.2 | Euler characteristics | `GammaContinuousDecomposition.exists_decomposition`, `.geometric_sum`, `.sum_independent`; actual integration, bijection invariance, Fubini and stabilization in the Gamma integration modules. These take the multivariate rational-affine normal form `Section3GammaAffineInput.Input` as a parameter; it is proved over every base by `Section3GammaAffineDischarge.input` (RV quantifier elimination, ACVF only). `Section4GammaAffineDischarged`: `GammaContinuousDecomposition.exists_decomposition_discharged`, `.constructed_geometric_sum_discharged`, `.geometric_sum_discharged`, `.euler_characteristic_discharged` (existence, Euler sum and independence together), `.pieces_nonempty_discharged`, `.dimensions_bounded_discharged`, and `GammaContinuousPartitions.exists_partition_discharged`, `.exists_common_discharged`. `.geometric_sum` and `.sum_independent` quantify over given decompositions and never took the input. |
| Notation 4.3 | `res:note` | Actual fibre/affine reductions, homogeneous ideals and unchanged degree-zero subrings in `RESMeasuredReduction`, `RESOrdinaryReduction`, `RESReductionGradings`, `ReductionDegreeZero`. |
| Ordinary construction | `kill:gamma`, `eg:isp:van`, `EB` | `RVT001OrdinaryDescent`, `RVT001OrdinaryNormalization`, `RVT001OrdinaryRanges`: actual ordinary Euler descent, normalization, stated ranges and RES restrictions. |
| Remark 4.4 | `eb:no:eg` | `RESAffineNonsurjective.remark_4_4`: affine comparison is not surjective; point localization is an isomorphism via `RESPointLocalization`; normalized maps are distinct via `RVT001NormalizedDistinct`. `Section4LinkedRemarks`: `boundedRetraction_res`, `boundedRetraction_surjective`, `geometricRetraction_range`, `normalized_retractions_distinct`, instantiated with `Section3T001Integration.ordinary` and the discharged Γ-linearity input (no T001 presentation argument). The colimit description and the "[A] = 1 equalizes" part were not pursued (triage). |
| Notation 4.5 | `gam:equ:cons` | `GammaFunctionRing`, `GammaFunctionPolynomial`, `GammaPointAlgebra`: actual function rings, convolution, restricted polynomial source and degree-zero coefficients. |
| Remark 4.6 | `int:Gam` | Actual weighted profiles, original-base definability, multiplicativity and graded evaluations in `GammaMeasuredProfileInvariance`, `GammaProfileProducts`, `GammaEulerPolynomialMaps`. The isomorphism K μΓ[0] ≅ ℤ[Γ_def] was not pursued (triage). |
| Measured psi | `Gam:ass` | `RESUnboundedPsi`, `RESAllFiniteBalancing`, `GammaUnboundedSpecialization`: assignments, entire finite-Gamma balancing and grading. |
| Proposition 4.7 | `prop:eu:retr:k` | `Section3LinkedRetractionStatements.proposition_4_7`: all clauses, including distinctness using `RESPointNonvanishing.point_ne_zero_acvf00`. Corrected geometric h value is +[1]. `proposition_4_7_discharged` (`Section4GammaLinearityDischarged`) drops the unary Γ rational-affine argument. |
| Remark 4.8 | `res:forget` | `RVT001AlternativeDescent`, `RESAlternativeRawQuotient`, `RESAlternativeCompatibility`: enlarged quotient, actual alternative descent, grading and forgetful compatibility. |
| Definition 4.9 | `db:RV` | `RVMeasuredBounds`, `RVBoundedRing`, `RVBoundedDisjointPresentation`: actual doubly bounded objects, products, ring and grading. Lean's bound leaves `iRVZero` (∞) coordinates unconstrained; `RVStrictBoundedComparison.equivalence : StrictRing B ≃+* RVBoundedRing.Ring B` shows the ring on ∞-free charts (the paper's doubly bounded objects) is isomorphic to it (author decision, November 18). |
| Remark 4.10 | `tensor:bd` | Positive level: `RVBoundedPositiveTensor.comparison` (`K₊ μRES ⊗ K₊ μΓ^db → K₊ μRV^db`, also `comparisonNat` over ℕ) on the chart presentations of `PositiveChartPresentation`; ring level: `RVBoundedTensorComparison`, `RVBoundedBalancedTensor.comparison`, compatible by `comparison_toRing`. No bounded comparison injectivity or bounded tensor-kernel input. The first sentence (a restatement of Lemma 2.41) was not pursued (triage). |
| Notation 4.11 | `db:generator` | `EulerIntervalProducts`, `GammaBoundedFunctions`: all signs and endpoints, actual convolution, original-base point/interval generation. |
| Notation 4.12 | `db:gam:fn` | `GammaBoundedComparison`, `GammaBoundedProfileRange`, `GammaBoxStabilization`: bounded theories agree, bounded polynomial profiles and stabilization. |
| Notation 4.13 | `pgammabis` | `GammaRVLifts`, `RVRadiusGenerators`, `RVRadiusQuotient`, `RVBalancedRadiusChoices`: admissible nonnegative radii, lift independence, separate zero-radius identity, homogeneous radius ideal and quotient. The unmeasured RV^db[k] ring and the inequality were not pursued (triage). |
| Remark 4.14 | `db:gam:res`, `Gam:ass:bd` | `GammaBoundedQuotient`, `RESBoundedPsi`, `RESAllBoundedFiniteBalancing`: exact bounded function quotient, assignments, grading, coefficient balancing and volume forgetting. |
| Proposition 4.15 | `prop:eu:retr:k:db` | `Section3LinkedRetractionStatements.proposition_4_15`: actual bounded retraction, all radius relations, grading and RES restriction from the full ordinary compiled Section 3 presentation. `proposition_4_15_discharged` drops the unary Γ rational-affine argument. |
| Diagram (4.8) | `edb:eb:com` | Bounded commuting square in `Section3LinkedRetractionStatements.proposition_4_15`, with normalized square in `RVT001OrdinaryNormalization.bounded_radius_square`; stated as `Section4LinkedRemarks.diagram_edb_eb_com`. |
| Remark 4.16 | `eb:not:eg` | `RVT001NormalizedDistinct.normalized_maps_distinct`: the geometric point value is inverse affine class and differs from bounded value 1; also `Section4LinkedRemarks.normalized_retractions_distinct`. The second paragraph (an alternative the paper rejects) was not pursued (triage). |
| Notation 4.17 | annular generators | `AnnularBlowup`, `BlowupChart`, `BlowupRelation` (moved from section 7); `RelativeAnnularGenerators`: `AnnularDatum`, `generator`, `manuscriptIdeal` (J_var). `RelativeAnnularConverse.ideal_eq_manuscriptIdeal`: the implemented `FunctionalApertureCompatibility.ideal` is exactly J_var. `RelativeAnnularScalar.pGamma_eq_generator`, `radiusIdeal_le_manuscriptIdeal`: the last sentence, (P_Γ) ⊆ J_var. |
| Lemma 4.18 | generator identification | `RelativeAnnularGenerators`: `manuscriptIdeal_homogeneous`, `manuscriptIdeal_le_forget_kernel`, `manuscript_quotient_injective_on_degree_zero`, `manuscriptIdeal_maps_into_p`, `manuscript_section4_compatibility`, `AnnularDatum.generator_eq_relation`. |

The modular `ApprovedT001Presentation.Ordinary` and `.Measured` interfaces
are constructed by `Section3T001Integration` through actual categorical-to-chart
factor and tensor equivalences, commuting squares and coefficient-pair ideal
transport. The unary rational-affine input
(`GammaPiecewiseRationalAffineInput`) is now proved
(`Section5.GammaQE.gamma_piecewise_rational_affine`), and
`Section4GammaLinearityDischarged` gives input-free 4.7 and 4.15; the original
statements still take it as a parameter. The multivariate
`Section3GammaAffineInput.Input` (used by Remark 4.2) is proved by
`Section3GammaAffineDischarge.input`: the Γ names of the base are abstracted
to free variables, the predicate gets a flat RV literal normal form
(`GammaQEFlatNormalFormArity`), an output perturbation forces an equal-value
pair of monomials with different output slopes (`GammaQEOutputSlopes`), and
the branch constant is named over the base (`GammaQECoefficientNames`).
`Section4GammaAffineDischarged` gives the input-free Remark 4.2 forms; the
original statements are unchanged. Literature: van den Dries, *Tame Topology
and O-minimal Structures*, Ch. 1 §7, with stable embeddedness of Γ in ACVF
(Haskell–Hrushovski–Macpherson); no pinned Lean dependency provides DOAG QE
or piecewise linearity, so the proof uses the pinned RV quantifier
elimination. These inputs supply structural branch
equations, not Euler or localization conclusions. Exact hypotheses and logical dependencies appear in the full audit.

Also hosted here (recorded under `section 3/GAP-REPAIRS.md`): the
Proposition 3.18 kernel witness `GermJumps`, `GammaEndpointInvariant`,
`Proposition318Witness.proposition_3_18_unmeasured_kernel_nontrivial` and
`Proposition318CubeRoots.proposition_3_18_kernel_nontrivial_of_noncube`,
relative to the Reichstein–Youssin input of Remark 3.15. Not pursued, by the
author-approved triage of November 18, are the explanatory items noted in the
table; see [GAP-REPAIRS.md](GAP-REPAIRS.md).

The nonsurjectivity proof introduces no new theorem input. Coordinate
pieces bound actual RES domains; finite-field specialization proves the
growth separation after all relations and localization denominators.
Neither affine-comparison injectivity nor the referee's example varieties
are premises. The original parameter base, approved nontrivial Gamma
convention and distinction between Gamma names and RV lifts are retained.

Older incomplete milestones are archived in `verification/history/` and
are superseded by this inventory.
