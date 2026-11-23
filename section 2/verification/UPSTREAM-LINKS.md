# Links to the completed Integration in ACVF results

Author update, November 11, 2026: Sections 1–3 of
[Integration in ACVF](https://github.com/daviddhilbert/integration-in-ACVF)
are formalized. Source inspection was fixed at revision
`7675d31332f20421c803ea16af84964ed74cd51f`; on November 23 the links were moved to the
pinned revision `7238c3863ef7ea65ab3c21bcb0982be4cac9728f`, where every linked declaration is at
the same file and line. Lean 4.35.0, Mathlib and ACVF-QE pins match this project;
both projects currently pin the same Special transformations revision.
Section 1 is introductory; the numbered sources below belong to Section 3.

| Downstream cited interface | Upstream result and exact exported declaration |
|---|---|
| `AtomicGammaBaseChangeInput` | [3.3: `FullGammaAtomicity.lemma_3_3`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/FullGammaAtomicity.lean#L127) |
| `AtomicDiscGammaBaseChangeInput` | [3.3: `FullGammaAtomicity.lemma_3_3_one_unary`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/FullGammaAtomicity.lean#L134) |
| `UnaryDiscAtomicityInput` | [3.4: `CompleteTypeBallAtomicity.lemma_3_4`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/CompleteTypeBallAtomicity.lean#L60) |
| `PrimitiveImageInput` | [3.8: `PrimitiveImages.lemma_3_8`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/PrimitiveImages.lean#L34) |
| `UnaryOpenDiscRVBaseChangeInput` | [3.9: `OpenBallConstancy.lemma_3_9_open`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/OpenBallConstancy.lean#L182) |
| `OpenDiscImageInput` | [3.13: `OpenImages.lemma_3_13`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/OpenImages.lean#L43) |
| `OpenDiscNamesImageInput` | [3.13: `OpenImages.lemma_3_13`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/OpenImages.lean#L43) |
| `DiscToDiscPartitionInput` | [3.19/3.21: `CoordinatePartitions.proposition_3_21`](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/CoordinatePartitions.lean#L20) |

All declaration names in the table have prefix
`IntegrationInACVF.Section3ACVF`. For the unary partition underlying
3.21, see [FullOpenToOpenPartition.proposition_3_19](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/IntegrationSection3ACVF/FullOpenToOpenPartition.lean#L93).
The upstream [status](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/STATUS.md)
and [verification record](https://github.com/daviddhilbert/integration-in-ACVF/blob/7238c3863ef7ea65ab3c21bcb0982be4cac9728f/section%203/VERIFICATION.json)
record their compiled scopes and standard logical principles.

## Scope checks before importing these results

These are exact source links, not a claim that the downstream interfaces have
already been discharged by Lean imports. The existing explicit inputs remain
in theorem types. No dependency pin or manuscript statement is changed here.

The upstream base is `FullBaseAtomicity.Base`, with arbitrary real, Gamma and
ball names. This project's `ParameterBase` and invariant finite-disc relations
need definability and atomicity equivalences with that interface. A chosen
centre or Gamma representative must not be added to the final ground base.

* 3.3 starts with a definable atomic finite tuple set and preserves atomicity
  after naming Gamma values. It retains ACVF00 and a ground-definable actual
  Gamma value δ with 1 < δ. This project's two-distinct-values witness needs
  the corresponding definable nontrivial-value conversion.
* 3.4 treats potentially undefinable complete-type ambients, arbitrary ball
  radii, singletons and VF. Its full-base theorem explicitly requires genuine
  κ-saturation, aleph0 ≤ κ and smallness of the original real base. Those
  hypotheses are not present in the unrestricted standalone input interfaces
  currently used here, so replacing them requires suitably scoped wrappers.
* 3.8 retains the one-primitive-component hypothesis; the primitive-shape
  predicates require a bridge. 3.13 returns a constant or atomic open image.
  Upstream open balls also allow VF; proper open-disc conclusions here need
  the existing exclusion of the whole-field image, rather than identifying
  the two predicates without proof.
* 3.9 proves set-valued RV constancy in every finite RV arity. Its use as
  atomicity after adjoining an RV name needs the formula-fibre conversion;
  the original imaginary ground names must be retained.
* 3.19 and 3.21 explicitly retain genuine saturation, an infinite cardinal,
  small real base, ACVF00 and the definable nontrivial value. 3.21 gives
  uniform coordinatewise partitions for actual mixed finite tuple injections;
  compare its coordinate slicing and OpenToOpen predicates with our exact
  disc-to-disc and inverse formulations before using it as a producer.

`GammaPiecewiseRationalAffineInput` was the separately accepted QE/value-
group background. Neither the statement of RV-linearity 3.18 nor piecewise
monotonicity alone is the rational-affine power-law interface used here, and
no exact upstream producer was identified. It is now proved locally
(November 18): `Section5.GammaQE.gamma_piecewise_rational_affine`, from RV
quantifier elimination, with input-free 2.41/2.47/2.53 in
`section 3/Section2GammaLinearityDischarged.lean`.

The machine-readable map is [UPSTREAM-LINKS.json](UPSTREAM-LINKS.json).
Eight numbered-result interfaces now have precise proved upstream sources.
(This paragraph predates the compiled bridges; see the refreshes below.)
No new mathematical input is introduced.


## November 12 refresh

The dependency now pins 7238c3863ef7ea65ab3c21bcb0982be4cac9728f.
The previously reviewed section 2–3 source files are unchanged at this
revision. All eight legacy numbered-result interfaces now have compiled
constructors in the section 3 reuse inventory; earlier notes about missing
adapters are historical. The independent Gamma rational-affine background
remains an explicit input. The new section 6 sources retain the unfinished
section 5.8 premise; measured section 7 is not implemented.

## November 18 refresh

The pins are unchanged: integration-in-ACVF
`7238c3863ef7ea65ab3c21bcb0982be4cac9728f`, Special transformations
`25852c85a31c67069b148bd31348128318303510`. The eight numbered interfaces are
discharged: `section 3/Section2CitedInputsDischarged.lean` restates the 20
statements that still took them without the input arguments. The Gamma
rational-affine input is proved (`Section5.GammaQE.gamma_piecewise_rational_affine`)
and discharged in `section 3/Section2GammaLinearityDischarged.lean`. The
legacy interfaces remain parameters of the original §2 statements. The
section 5.8 premise mentioned above is no longer unfinished: the pinned
upstream contains the completed Section 5
(`IntegrationInACVF.Section5.lemma_5_8_finite`), and this project's
`Section5.completed_section5_input` instantiates `Section5TwoOrderInputAll`
from it (via `completed_relative_corollary_5_8`).
