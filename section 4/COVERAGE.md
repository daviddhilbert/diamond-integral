# Section 4 coverage

All corrected main-text obligations are proved, and both T001 adapters are
constructed from finalized Section 3. The linked retraction propositions take
no T001 input. The manuscript review is resolved; no author decision is pending.
The current extract is printed pp. 40–48; stable labels identify passages
independently of pagination.

| Passage | Stable label | Checked implementation |
| --- | --- | --- |
| Definition 4.1 | `df:res` | `RVMeasuredCharts`, measured/ordinary RES rings, full gradings, finite-union presentation equivalences and dimension-free point localization. |
| Remark 4.2 | Euler characteristics | `GammaContinuousDecomposition.exists_decomposition`, `.geometric_sum`, `.sum_independent`; actual integration, bijection invariance, Fubini and stabilization in the Gamma integration modules. |
| Notation 4.3 | `res:note` | Actual fibre/affine reductions, homogeneous ideals and unchanged degree-zero subrings in `RESMeasuredReduction`, `RESOrdinaryReduction`, `RESReductionGradings`, `ReductionDegreeZero`. |
| Ordinary construction | `kill:gamma`, `eg:isp:van`, `EB` | `RVT001OrdinaryDescent`, `RVT001OrdinaryNormalization`, `RVT001OrdinaryRanges`: actual ordinary Euler descent, normalization, stated ranges and RES restrictions. |
| Remark 4.4 | `eb:no:eg` | `RESAffineNonsurjective.remark_4_4`: affine comparison is not surjective; point localization is an isomorphism via `RESPointLocalization`; normalized maps are distinct via `RVT001NormalizedDistinct`. |
| Notation 4.5 | `gam:equ:cons` | `GammaFunctionRing`, `GammaFunctionPolynomial`, `GammaPointAlgebra`: actual function rings, convolution, restricted polynomial source and degree-zero coefficients. |
| Remark 4.6 | `int:Gam` | Actual weighted profiles, original-base definability, multiplicativity and graded evaluations in `GammaMeasuredProfileInvariance`, `GammaProfileProducts`, `GammaEulerPolynomialMaps`. |
| Measured psi | `Gam:ass` | `RESUnboundedPsi`, `RESAllFiniteBalancing`, `GammaUnboundedSpecialization`: assignments, entire finite-Gamma balancing and grading. |
| Proposition 4.7 | `prop:eu:retr:k` | `Section3LinkedRetractionStatements.proposition_4_7`: all clauses, including distinctness using `RESPointNonvanishing.point_ne_zero_acvf00`. Corrected geometric h value is +[1]. |
| Remark 4.8 | `res:forget` | `RVT001AlternativeDescent`, `RESAlternativeRawQuotient`, `RESAlternativeCompatibility`: enlarged quotient, actual alternative descent, grading and forgetful compatibility. |
| Definition 4.9 | `db:RV` | `RVMeasuredBounds`, `RVBoundedRing`, `RVBoundedDisjointPresentation`: actual doubly bounded objects, products, ring and grading. |
| Remark 4.10 | `tensor:bd` | `RVBoundedTensorComparison` and the bounded restriction construction; no bounded comparison injectivity or bounded tensor-kernel input. |
| Notation 4.11 | `db:generator` | `EulerIntervalProducts`, `GammaBoundedFunctions`: all signs and endpoints, actual convolution, original-base point/interval generation. |
| Notation 4.12 | `db:gam:fn` | `GammaBoundedComparison`, `GammaBoundedProfileRange`, `GammaBoxStabilization`: bounded theories agree, bounded polynomial profiles and stabilization. |
| Notation 4.13 | `pgammabis` | `GammaRVLifts`, `RVRadiusGenerators`, `RVRadiusQuotient`, `RVBalancedRadiusChoices`: admissible nonnegative radii, lift independence, separate zero-radius identity, homogeneous radius ideal and quotient. |
| Remark 4.14 | `db:gam:res`, `Gam:ass:bd` | `GammaBoundedQuotient`, `RESBoundedPsi`, `RESAllBoundedFiniteBalancing`: exact bounded function quotient, assignments, grading, coefficient balancing and volume forgetting. |
| Proposition 4.15 | `prop:eu:retr:k:db` | `Section3LinkedRetractionStatements.proposition_4_15`: actual bounded retraction, all radius relations, grading and RES restriction from the full ordinary compiled Section 3 presentation. |
| Diagram (4.8) | `edb:eb:com` | Bounded commuting square in `Section3LinkedRetractionStatements.proposition_4_15`, with normalized square in `RVT001OrdinaryNormalization.bounded_radius_square`. |
| Remark 4.16 | `eb:not:eg` | `RVT001NormalizedDistinct.normalized_maps_distinct`: the geometric point value is inverse affine class and differs from bounded value 1. |

The modular `ApprovedT001Presentation.Ordinary` and `.Measured` interfaces
are constructed by `Section3T001Integration` through actual categorical-to-chart
factor and tensor equivalences, commuting squares and coefficient-pair ideal
transport. `Section3GammaAffineInput.Input` and the earlier authorized unary
rational-affine background remain explicit. They supply structural branch
equations, not Euler or localization conclusions. Exact hypotheses and logical
dependencies appear in the full audit.

The nonsurjectivity proof introduces no new theorem input. Coordinate
pieces bound actual RES domains; finite-field specialization proves the
growth separation after all relations and localization denominators.
Neither affine-comparison injectivity nor the referee's example varieties
are premises. The original parameter base, approved nontrivial Gamma
convention and distinction between Gamma names and RV lifts are retained.

Older incomplete milestones are archived in `verification/history/` and
are superseded by this inventory.
