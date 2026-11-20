# Lemma 7.14 (`isp:VF:fiberwise:contract`): proof plan

Session: "Lemma 7.14 proof", branch `claude/lemma-7-14-a45a03`, started 2026-11-19
from the Section 7 commit 1143e290. This plan covers only the discharge of the
input `DiamondIntegral.Section7.FiberwiseInput.Lemma714 M G`
(`section 7/FiberwiseInput.lean`). New code goes only into
`section 7/Lemma714*.lean`. The input statement is not edited here.

## 0. The target

`Lemma714 M G` says, over a substructure `T` with support data
`V ⊆ T ⊆ acl V`, saturated `M`, small `T`, and nontrivial `Γ(T)`:

- `A' ⊆ VF^(n+1) × RV^r'` and `A'' ⊆ VF^(n+1) × RV^r''` are `T`-definable and
  proper invariant, with Γ-forms `ω'`, `ω''` and the same VF projection;
- `π'`, `π''` are head-start labels, finite-to-one (`hFin`) and nonzero (`hNZ`);
- for every VF point `a` of the projection, the fibres
  `fibreObject T A' ω' a π'` and `fibreObject T A'' ω'' a π''` are doubly
  bounded, and their classes over `adjoin T a` satisfy `IspRel` in degree `k`.

The conclusion: for normalized measured contractions `F'`, `F''` in the same
order `e`, the head-start objects satisfy `IspRel` in degree `(n+1)+k` over
`T`.

`IspRel` in degree `m` is equality of classes if `m = 0`, and `MuIsp` otherwise.
`MuIsp x y := Common Step x y` (`BlowupCongruence`) holds on classes of
`Cls (BT T) (1+k)`. `Step` replaces finitely many summands `[D_i.source]` by
`[D_i.annularObject]` (`ElementaryBlowups`).

Review of the statement (2026-11-19): it matches the printed lemma under the
reading recorded in GAP-REPAIRS 9–10. I found no mismatch. The fibre
hypothesis is needed only at points of the VF projection, and the degree-0 case
`k = 0` is class equality over `S⟨a⟩`, as in the paper. Two points to confirm
during the proof:
1. the projection `A_VF` is proper invariant (needed to freeze on `A_VF`);
2. the contraction of `A'` along the frozen VF map is related to `F'` by a
   relatively unary isomorphism of lifts (step 4).

## 1. The paper's proof

**Reduction to one VF coordinate.** Write `n + 1` VF coordinates and
`i = σ(1)`. For `b` in `pr_{~i}(A)`, the first stage of `T̂_σ`, `R̂_σ`
restricts to standard contractions of the fibres over `S⟨b⟩`. The unary case
over `S⟨b⟩` gives `IspRel` of the fibres of the first-stage contractions, in
degree `1 + k`. The remaining stages are standard contractions of the
first-stage contractions, which have `n` VF coordinates. The inductive
hypothesis with head start `k + 1` then gives the claim.

**Unary case** (`A ⊆ VF`):
1. *Uniform witnesses.* A witness at `a` is the whole blowup data over `S⟨a⟩`:
   both chains, all loci, structural maps, apertures and intermediate
   objects, and the final isomorphism. For a fixed tuple of formulas and fixed
   fibre-size bounds, "is a witness at `a`" is first order in `a`. By
   compactness finitely many codes cover `A`.
2. *Freezing.* Prepare `A` against the complete witness data with
   Lemma 6.16, and apply FMT on the finitely many discs of a common invariance
   radius. The result is a special covariant bijection `F` on `A` such that on
   each fibre of `rv ∘ F` the whole witness row, the fibres `A'_a`, `A''_a`
   and the forms are constant. On a frozen disc the witness at the chosen
   centre is used.
3. *Descent.* The rows glue over the RV codes into `S`-definable blowup data.
   Validity holds fibrewise. The added coordinate `rv(F(a))` is the same on
   both sides. Aperture bounds come from Remark 7.4. Hence `μIsp` holds over
   `S` for the contractions `F̂'(A')`, `F̂''(A'')` induced by `F`.
4. *Comparison.* `F ∘ T_σ⁻¹` is relatively unary in the VF coordinate and keeps
   the labels. By Lemma 6.38 (`simul:special:dim:1`) and Lemma 7.11
   (`special:to:blowup:coa`), as in Lemma 7.13, `[T̂_σ(A')]` and `[F̂'(A')]` are
   `μIsp`-related. The same holds on the other side. Conclude by Lemma 7.10
   (transitivity).

## 2. What exists and can be reused

### Upstream integration-in-ACVF (pinned 5a69a5e, importable)

The template is `IntegrationInACVF.Section6.FiniteRV.lemma_6_14_ordered`
(`section 6/IntegrationSection6/OrderedFibrewiseContractions.lean`), for
ordinary blowups. Its uniformisation core is about 2.6k lines. The 25k-line
figure in the scope note counts all of upstream Section 6 that it imports.

Reused as is (generic over `DefinableOverBase B sn`; about 670 lines upstream):
- `gamma_finite_witnesses` (`GammaWitnessUniformity`): compactness over an
  arbitrary index type of schemata, needing only that each validity locus is
  definable. The existence of a witness never has to be definable.
- `gamma_tuple_parameter_promotion` (`GammaTuplePromotion`) and
  `promote_definable_tuple_fibre` (special-transformations `GammaBaseTools`):
  data over `B.real ∪ range a` become fibres at `a` of `B`-definable sets.
- `definable_termClosure_iff` (upstream `Integration7/TermClosureDefinability`):
  definability over `adjoin T a` is definability over `T ∪ range a`.
- Validity combinators: `finiteMapRowValid` and
  `gamma_finite_map_validity_definable` (function with fibres of size `≤ N`),
  `bijectiveMapRowValid` and `gamma_bijection_validity_definable`,
  `gamma_equal_rows_definable`.
- `gammaRawObjectVolume_uniform_bound` (`GammaNativeFiniteBounds`), the pattern
  by which saturation over the small base `B.real ∪ range a` turns finite fibres
  into a natural-number bound.

Adapted (the architecture is copied, not the theorem):
- object, isomorphism and blowup schemata (`GammaFiniteRVSchema`,
  `GammaFiniteRVIsoSchema`, `GammaFiniteBlowupSchema`, `GammaFiniteChainSchema`,
  `GammaFiniteCommonSchema`), and the volume-weighted Section 7 copies
  (`Integration7/GammaVolumeBlowupSchemata`, `GammaVolumeChainSchemata`);
- pointwise promotion (`gamma_sorted_finite_*_promotion`), indexed realization
  (`*IndexedRealization`), and the Finset-induction gluing
  (`gamma_common_finite_indexed_glue`).

Not reused: upstream freezing (`gamma_prepare_finite_rv_families`). It gives
ordinary special bijections, not special covariant ones. Local Section 6
replaces it.

### Local Section 6

- Templates and promotion: `RVSetParameterTemplate`,
  `exists_promoted_rv_set_template`, `MixedSetParameterTemplate`,
  `exists_promoted_mixed_set_template`; the promote-then-compact pattern in
  `exists_finite_measured_centripetal_programs`.
- Freezing:
  - `MeasuredUnaryRVTemplateFreezeCertificate` and
    `measured_frozen_unary_rv_template_preparation`, for a unary proper
    invariant, VF-doubly-bounded RV-pullback with protected pieces and a form;
  - `FrozenRVWitnessDescent`: `descendedWitnessRelation` (definable), its value
    at each point, and `complete_witness_validity`. That last lemma transports
    an arbitrary, not necessarily first-order, validity predicate to the
    descended row. This is the "witness at the chosen centre" argument.
- Preparation before freezing: `proposition_6_19_vfGenerated` and
  `remark_6_20_unary` (making `A_VF` a doubly bounded RV-pullback), and
  `lemma_6_16`.
- Head starts: `rvHeadStartBundle`, `headStartSourceObject`, `remark_6_28`
  (head-start form).

### Local Section 7

- `MuIsp`, `muIsp_trans` (via `ElementaryComparison.elementaryDiamond`) and
  `muIsp_add`; `BaseExtension` (`clsExt`, `muIsp_ext`); `remark_7_4_named`.
- `KernelBaseChange`: `adjoin` and its support data, and
  `lift_iso_muIsp_of_support` (Lemma 7.13, core form, degree 1).
- `lemma_7_11_measured` (`MeasuredLift`): a relative aperture chain on the full
  lift of a degree-`1+k` object gives blowups of its class. This is the
  head-start form of 7.11 that step 4 needs.
- `FibreObjects`: `fibreObject`, `fibreDomain`, `fibreForm_apply`.

## 3. What is genuinely new

1. **Witness normal form.** `MuIsp (cls X) (cls Y)` holds iff there are
   single-datum blowup chains with explicit objects and isomorphisms:
   `X_j ≅ Z_j ⊎ D_j.source`, `X_{j+1} = Z_j ⊎ D_j.annularObject`, and a final
   `X_m ≅ Y_n`. This is pure algebra on classes and needs no definability.
2. **Annular schemata.** Uniform families of Section 4 charts over a sorted
   parameter tuple: domain, structural map with a fibre bound, Γ-volume graph,
   and domain bound. Also uniform aperture data (coordinate, aperture graph,
   inactive-fibre bound) and uniform isomorphisms with corrected-weight
   preservation.
   - Validity loci are definable. New combinators are needed for the Γ-volume,
     the corrected weight `volume · ∏ codeValue`, the domain bound and the
     aperture bounds.
   - Fibre lemmas show that the parametric coproduct and annular object have
     the coproduct and annular object of the rows as fibres.
3. **Promotion.** A Lean witness over `BT (adjoin T a)` is the row at `a` of a
   `T`-definable schema, with natural-number bounds from saturation over the
   small base `adjoin T a`.
4. **Compactness and packaging.** Use `gamma_finite_witnesses`, then the
   definable partition of `A` by the first valid code. Different arities and
   lengths are handled piecewise. Pieces are combined at the end by `muIsp_add`
   and the class partition, so no padding is needed.
5. **Freezing pipeline.**
   - Prepare `A_VF` to a doubly bounded RV-pullback (6.19).
   - Transport the schemata along the preparation.
   - Freeze all rows and the partition with one template certificate.
   - Compose the chains into one special covariant map `F` on `A_VF`, then act by
     `F × id` on `A'` and `A''`.
6. **Indexed realization and descent.** A schema valid at every key of an
   `S`-definable RV key set gives a chart over `BT T` of degree `1+k`. The
   designated key coordinate is the new structural coordinate; the other keys
   are tags. Datums, isomorphisms, coproducts and annular objects realize
   compatibly, up to explicit isomorphisms. Uniform domain and aperture bounds
   come from Lemma 2.41 and Remark 7.4 on the doubly bounded key set. Result:
   `MuIsp` over `T` of the descended objects.
7. **Identification and comparison.**
   - The descended `X'_0` is the contraction of `(F × id)(A')`.
   - Its full lift and that of `F'`'s head-start object are related by a
     relatively unary isomorphism that keeps the head-start labels.
   - The head-start Lemma 7.13 (6.38 for relatively unary isomorphisms of full
     lifts in grade `1+k`, then `lemma_7_11_measured`) gives `MuIsp`.
   - **Coordination:** the Section 7 plan lists "7.13 with head start" as
     to do. I have asked the Section 7 session who builds it and in which form;
     if nobody does, it goes into `Lemma714Compare.lean`.
8. **Reduction from `n+1` to `1` VF coordinates.** Fibres over `S⟨b⟩` of the
   first-stage contraction, induction with head start `k+1`. This needs the
   fibre of a normalized measured contraction to be a normalized measured
   contraction of the fibre over `adjoin T b`, with support data
   (`adjoin_support` in its `V`-form).

## 4. Module layout (all new, `section 7/Lemma714*.lean`)

| Module | Content | Estimate |
|---|---|---|
| `Lemma714Witness` | witness normal form for `MuIsp`/`IspRel` | 0.3k |
| `Lemma714Schema` | parametric charts, data, isos; fibres; validity | 1.5k |
| `Lemma714Validity` | definability of all validity loci | 1.0k |
| `Lemma714Promote` | Lean witness over `adjoin T a` ↦ schema row | 1.2k |
| `Lemma714Cover` | compactness, first-valid-code partition | 0.4k |
| `Lemma714Freeze` | preparation + template freezing on `A_VF`, `F × id` | 1.5k |
| `Lemma714Indexed` | indexed realization over RV keys, compatibility | 1.5k |
| `Lemma714Descent` | descended witness ⇒ `MuIsp` over `T` | 0.8k |
| `Lemma714Compare` | identification with contractions, comparison | 1.5k (+1.5k if head-start 7.13 is mine) |
| `Lemma714Reduce` | `n+1 → 1` induction | 1.0k |
| `Lemma714` | `theorem lemma714 : Lemma714 M G` | 0.1k |

The total is roughly 10–13k lines, consistent with the scope note.

## 5. Order of work and checkpoints

1. `Lemma714Witness` (independent; it fixes the witness shape).
2. `Lemma714Schema`, `Lemma714Validity`, `Lemma714Promote`, `Lemma714Cover`:
   the conclusion "finitely many valid schemata cover `A_VF`".
3. `Lemma714Indexed`, `Lemma714Descent`: "a schema valid at all keys gives
   `MuIsp` over `T`".
4. `Lemma714Freeze`, joining 2 and 3.
5. `Lemma714Compare`, `Lemma714Reduce`, `Lemma714`.

Each module is committed when it builds, with no `sorry` and no new axioms.
The audit checks `#print axioms` of the final theorem (only `propext`,
`Classical.choice`, `Quot.sound`). No HK result is used.

## 6. Risks

- **Validity definability is the largest mechanical block.** Following upstream,
  it is a fixed conjunction proved by `.inter` chaining. The Γ-volume and
  corrected-weight combinators are new.
- **Freezing needs a doubly bounded RV-pullback.** `A_VF` is first prepared. The
  witness schemata must be transported along the preparation, which is
  standard: the preparation is `T`-definable and bijective.
- **Comparison depends on head-start 7.13.** If the relatively unary isomorphism
  of lifts cannot be produced directly, the fallback is Lemma 6.38 over support
  data applied to the composite map, as in `lift_iso_muIsp_of_support`.
- **Reduction step:** fibres of normalized contractions over `adjoin T b`.
  This may need a Section 6 fibre lemma that does not yet exist.

## 7. Status (2026-11-19, evening)

Proved, no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`:

- **The one-coordinate case of the input**, word for word with `n = 0`:
  `Lemma714Frozen.lemma714_one` (`Lemma714OneVar`).
- Behind it, the unary case for abstract unary contraction data
  (`Lemma714Unary.unary_pos`, `unary_zero`; `Lemma714UnaryContr.UnaryContr`):
  witness cover, freezing (`Lemma714FrozenExists.exists_frozen`), keys and row
  constancy (`Lemma714Keys`), descent (`Lemma714Descent`), identification of the
  descended objects with head-start classes of the frozen sets
  (`Lemma714IdentFr.cls_ind_eq_clsH`), and comparison with the contractions by the
  head-start Lemma 7.13 (`Lemma714CompareFr.muIsp_compare`).

Remaining: the reduction `n + 1 → 1`.

- First stage and rest: the Section 7 session's `FirstStage` (branch
  `claude/section-7-64d3f7`).
- Fibre hypothesis for the first-stage sets: at good points, slices of the first
  stages are unary contraction data over `S⟨b⟩` (`FibreRestriction`), and the
  unary case applies; at other points, nearby good points with the same fibre
  classes (`FibreInvariance`, `FibreComparison`), transferred through `dcl`
  (`BaseExtension.Transfer.ofDcl`).
- GAP-REPAIRS 11 inside the proof: the induction is stated for contraction data
  "shift by base-definable centres, then a normalized contraction", so that the
  first-stage sets of `F'`, `F''` can be pulled back to the common VF projection.
