# Section 8 formalization plan

Status 2026-11-20. See `LEAN-INTERFACE.md` for the inherited declarations.

## Stage A: algebra (Mathlib only)

- A1 `PuiseuxPolynomials.lean`: Notation 8.1, the natural subring, the algebraic part of Lemma 8.3. **Done.**
- A2 `RationalSeries.lean`: `R[T]†` as a predicate on power series (`daggerDenominators`,
  `IsDagger`), the limit at infinity `HasLimit A φ c` (degree ≤ 0 and limit `c`), uniqueness and
  additivity. **Done.** The Hadamard product (Hrushovski–Loeser Lemma 8.4.1) is not needed.
- A3 Lattice-point series (Hrushovski–Loeser Lemma 8.5.2), proved directly (author's decision of
  2026-11-20; see `reference/HL-LEMMA-8-5-2.md` and `reference/lemma-8-5-2-direct-proof/`).
  - A3b `LatticeCone.lean`, `SimplexSeries.lean`: the series of a cone with unique decompositions
    `p + Σ n_j v_j`; the series of an open rational simplex has limit `(−1)^(dim+1)`
    (`hasLimit_openSimplex`); additivity over a finite disjoint union. **Done.**
  - A3a `HeightChains.lean`, `PrismSimplices.lean`, `PrismTriangulation.lean`, `Triangulation.lean`:
    the prism lemma, elementary refinement of chains, triangulation of `[−N, N]ⁿ` adapted to
    finitely many affine functions (`exists_adapted_triangulation`), independence of
    `Σ (−1)^dim` from the triangulation (`eulerChar_eq`), and the lemma over `ℚ`
    (`hasLimit_latticeSeries`). **Done.** All seven files use Mathlib only.
  - A3c Bridge to the value group of the ambient model. **Done 2026-11-20.**
    - `LinearTransfer.lean` (Mathlib only): transfer of sign patterns from an ordered `ℚ`-vector
      space to `ℚⁿ` (`exists_rat_signs`, Fourier–Motzkin); interpolation on cylindrical simplices;
      `VCell`; `exists_vcell_partition`. `PrismTriangulation`/`Triangulation` now record that every
      simplex is cylindrical (`IsCyl`, `Triangulation.Cyl`).
    - `GammaCells.lean`: `ι : Γ → DivisibleHull (Additive Γ)`, `qpow`, `gfun`, `real`;
      `cell_real` (a realized `VCell` is a library `Cell`); `euler_real`.
    - `GammaHalfspaces.lean`: `saturated_of_halfspaceBoolean`, `codeSet_definable`,
      `euler_eq_eulerChar`, `constructible_ratTrace`, `hasLimit_gamma` (Lemma 8.9 over Γ for a base
      `⟨R, ∅⟩` whose substructure values are rational powers of a definable `π > 1`).
    - `PuiseuxUniformizer.lean`: `uniformizerValue P` (value of the image of `t`),
      `uniformizerValue_definable`, `one_lt_uniformizerValue`, `substructureValues_rational`, and
      `lemma_8_9` (Lemma 8.9 in the Puiseux ambient). Axioms: propext, Classical.choice, Quot.sound.
    The lattice-point series is stated for the rational trace `ratTrace π X`
    (coordinates reversed); Stage C translates the sum over `X ∩ (m⁻¹ℤ)ⁿ` into it.

## Stage B: the piecewise retraction on the RV side

Setting: `P : PuiseuxAmbient`, base `PuiseuxValues.base P = ⟨G.real, ∅⟩`, `π = uniformizerValue P`,
target `PuiseuxPolynomial EquivariantVariety.ModifiedRing`.

- B0 `GammaBounds.lean`, `PuiseuxBase.lean`: definable points of Γ are rational powers of π; a
  definable set bounded by some β ∈ Γ (the library's `DomainBounded`) is bounded by a power of π;
  every `qpow π q` is definable. **Done.**
- B1 `ValueMaps.lean`, `HmLattice.lean`: definable Γ-valued maps (preimages, images, coordinate
  values, corrected weight); the lattice part of a bounded chart is definable; the weight takes
  finitely many values on it (orthogonality, `residue_gamma_tuple_finite_columns`), each a definable
  rational power of π. **Done.**
- B2–B3 `HmCharts.lean`: the lattice part of weight `w` as an RES chart (`fibreChart`), `theta`
  (the library's `ambientPuiseuxComparisonEquiv`), `hmValue a m = Σ_w Θ([U^{(m)}_w]) T^{-m w}`.
  **Done.**
- B4 Invariance and the ring homomorphism. **Done.**
  - `GaloisLattice.lean`, `IsoLattice.lean`: isomorphisms preserve lattice parts (`iso_lattice`):
    transfer of nonemptiness along `e` and the action of `levelRoots m = W^m` on the concrete model.
    The paper's argument (functional closure of ℂ((t^{1/m}))) does not apply verbatim in the
    ambient, whose residue field is larger than ℂ.
  - `HmIso.lean` (`hmValue_iso`), `RESPieces.lean`, `HmFields.lean` (disjoint unions, one-point
    charts, unit, grade casts), `HmProduct.lean` (`hmValue_product`), `HmRing.lean`
    (`hmValue_coproduct`, `hmInvariant`, `hm P m`, `hm_objectClass`).
- B5 Lemma 8.3: the image of an annular generator is in the principal ideal of `𝕃 T⁻¹ − 1`
  (endpoint in the trace, shell slices, `annular_mem_span`), hence `etaNatural_eq_zero` applies to
  `manuscriptIdeal`. **Done** (`HmAnnularPieces`, `HmAnnularEndpoint`, `HmAnnularShell`,
  `HmAnnular`: `hm_generator`, `hmLoc_generator_mem`, `lemma_8_3`). Remark 8.4 (Z descends to
  `QRV`) is `Theorem811.annular_kills` / `zetaQ`.

## Stage C: Theorem 8.11 on the RV side — done

The monomial route (C1 via Lemma 5.12) was replaced by the library's bounded decomposition
`RVBoundedDecomposition.bounded_value`: every doubly bounded class is a sum of products `[g♯ × V]`.

- `GraphSeries.lean`: the zeta series of the graph of a definable `E : Γ^ℓ → Γ^{k+1}` over a bounded
  definable `I` has limit `−χ(I)` (`graph_hasLimit`, from `lemma_8_9`).
- `ZetaPieces.lean`: `hm_sharp` (`[{vrv = δ}] = [G_m]^ℓ` from the library's finite balancing).
- `ZetaRES.lean`: `hm_res`, `res_class` (pieces of fixed value tuple and weight).
- `Theorem811RV.lean`: `zeta`, `Ediamond`, `zeta_prod`, `hasLimit_prod`, `theorem_8_11_rv`.
- `Theorem811.lean`: `theorem_8_11_rv_ring` (all of `K(μRV^db[*])`), `theorem_8_11_quotient`
  (on `K(μRV^db[*])/J_var`), `theorem_8_11_vf` (composed with ∫^◇ of Theorem 7.26, with the
  Section 7 valuation parameters).
- `RationalWeights.lean`: Lemma 8.9 with rational weight coefficients (not used by the above).

The hypothesis `l ∈ ℤ` is not needed: the zeta series uses the integer part of `h_m`, and η of
the integer part kills all of `J_var`.

- C3 `VolComparison.lean`: Remark 8.14, `Θ 𝔼^◇ ∫^◇ = Vol` (`remark_8_14`), from Corollary 7.27 and
  `theta_bounded_forget` (`Θ ∘ E_b ∘ (forget, base change) = Θ ∘ 𝔼^◇` on `K(μRV^db[*])`). **Done.**
- C4 `MilnorFiber.lean`: `𝒳_f` for `f ∈ ℂ[x₁,…,x_d]` (`X = 𝔸^d`, chart = identity) as an object of
  `μVF^◇[d]` (`milnorObject`), Theorem 8.11 for it (`theorem_8_11_milnor`: `𝒮_f = Θ 𝔼^◇ ∫^◇[𝒳_f]`,
  with `Z_f` as in (def:zeta)), and `milnor_fiber_vol` (`𝒮_f = Vol([𝒳_f])`). **Done.**

## Stages D–E: truncations, Lemma 8.6, jets, Remark 8.15 — done (2026-11-21)

- D1 Points rational over ℂ((t^{1/m})) of a proper invariant set; truncations `A[m;β]` as RES
  objects (coefficient lines `L_γ`); Lemma 8.5.
- D2 One centripetal step induces a bijection of truncations for compatible cutoffs; Lemma 8.6. **Done 2026-11-21** (see the D2 progress list; `chain_teq`, `lift_class`, `milnor_zeta_coeff`).
- E1 The object `𝒳_f` (étale chart, Hensel), the jet varieties `𝒳_m` with their μ_m actions and
  classes in `K^μ̂ Var_ℂ`, (z:coeff:change).
- E2 `𝒮_f = Θ 𝔼^◇ ∫^◇ [𝒳_f]`: done for `X = 𝔸^d` (C4) and for smooth affine `X` with the étale
  chart as an explicit hypothesis (`MilnorSmooth.lean`: `EtaleChart`, `milnorObjectX`,
  `theorem_8_11_smooth`, `milnor_fiber_vol_smooth`).
- E1 first equality of (z:coeff:change): **done 2026-11-21**, `Lemma86.milnor_zeta_coeff`, `z_coeff_change` (`X = 𝔸^d`, `d ≥ 1`; standard axioms).
- E1 (z:coeff:change) for smooth affine `X`: **done 2026-11-21**, `MilnorSmoothJets.z_coeff_change_smooth`,
  with the étale coordinates `EtaleCoords` as an explicit hypothesis (Hensel's lemma); supporting
  `Lemma86.zeta_coeff_of_form_one`, `TruncPairsGen` (correspondences of truncations in different
  dimensions), `TruncAmbientGen` (concrete images under maps between sets of different dimensions).
- E3 Remark 8.15 (`Vol([𝒳_f]) = Vol([𝒳_t])`): **done 2026-11-21**, `Remark815.remark_8_15`
  (`X(𝔪)` cut out by any equations `g`), `remark_8_15_integral` (`∫[𝒳_f] = [1] ∫[𝒳_t]`),
  `remark_8_15_affine` and `remark_8_15_milnor` (`X = 𝔸^d`), `remark_8_15_smooth` and
  `remark_8_15_milnor_smooth` (smooth affine `X`, étale chart hypothesis). Supporting `SameType`
  (same type of `t'` over `ℂ ∪ RV` from the ACVF quantifier elimination; parameter extraction;
  definability of the set of parameters giving a bijection). Follows the manuscript's repaired
  argument (R157, batch B09). Standard axioms only.

Inputs found on 2026-11-21 for D1–E1 (author's instruction: standard results as explicit
hypotheses, see special-transformations `AGENTS.md`):
- the chain `A → 𝕃U`: Section 6 `MeasuredRVLiftData.special : SpecialCovariantChain` (constructors
  `identity`, `regularize`, `centripetal`, `zeroCentered`, `comp`), from `lemma_6_21_vfGenerated`;
- functional closedness of henselian substructures: special-transformations
  `Section6.Paper.lemma_6_2` (Engler–Prestel 4.1.3 as explicit input); for ℂ((t^{1/m})) inside the
  concrete model the Galois action of `levelRoots m` already used in `GaloisLattice` also works;
- constructibility of truncations: Hrushovski–Loeser §4.2 as cited by the manuscript, or
  special-transformations `Section6.Paper.corollary_6_5` (Denef–Pas elimination);
- truncation sets and jets as `DiagonalConstructible.Object`s (weights `γ`), no jet schemes.
Order of work: D1 truncation sets and classes, Lemma 8.5; D2 induction over the chain (Lemma 8.6);
E1 jets and (z:coeff:change).

- D1a `Truncation.lean`: in the concrete model, `IsRational m`, `IsIntegral`, residue lines `Line γ`,
  `truncPoint`, `truncSet m b A` (= `A[m;β]`, `β_i = b_i/m`), and `lemma_8_5_sets`:
  `A[m;β'] = A[m;β] × ∏ L_γ` for `β`-invariant `A`. **Done 2026-11-21.**
- D1b truncations are definable. **Done 2026-11-21** (about 1600 lines, standard axioms):
  - `TruncNormalForm.lean` (any ACVF model): `definable_agree`, membership in a definable set
    depends only on the RV slots and on `rv P(x)` for finitely many polynomials `P`.
  - `TruncCoefficients.lean`: `ratSubring m` = ℂ((t^{1/m})), `fam_poly` (a polynomial at a polynomial
    point has coefficients polynomial in the parameter), `exists_bound` (Hilbert's basis theorem),
    `rvOfField_eq_linePoint`.
  - `RingDefinable.lean`: constructible sets (`RDef`), `rdef_preimage_poly`.
  - `TruncConstructible.lean`: `isPiecewise_fam`, `rdef_piecewise`.
  - `TruncDefinable.lean`: `coefficient_constructible`, for a set definable over any parameter set
    with `m`-rational field elements.
  - `TruncObjects.lean`: `coefficient_invariant` (Galois action), `coeffObject`
    (`DiagonalConstructible.Object`).
  - `TruncSets.lean`: `truncSet_pattern_eq`, `truncObject`, `truncation_definable`.
- E1 jets ((z:coeff:change), second equality). **Done 2026-11-21**: `JetSeries.lean`, `Jets.lean`
  (`rawMilnor f` = concrete `𝒳_f`, definable over ℂ((t)); `milnor_invariant_conc` for `β = 1`;
  `IsJet` = truncated arcs at 0 with `f(φ) ≡ s^m`; `milnor_coeffSet`, `milnor_trunc_eq`),
  `TruncClasses.lean` (`dcClass`, `theta_diagonalRESClass`, `truncClass`, `jetObject` with
  weights `k/m`, `jetClass`, `z_coeff_change_jets`: `Θ(𝒳̃_f[m]) = [𝒳_m][𝔸]^{-md}`).
- D1c `TruncTransfer.lean` (trace of an ambient base-definable mixed set on the concrete model,
  `traceRaw_definableOver`, `mem_mixedSet_trace`), `DiagonalClasses.lean` (`dcClass_product`,
  `dcClass_iso`, `dcClass_affineSpace`, `reindexIso`), `TruncLemma85.lean` (**Lemma 8.5 for
  classes**, `lemma_8_5`). **Done 2026-11-21.**
- D2 Lemma 8.6, plan (2026-11-21):
  1. valuations: concrete `ordS` vs ambient `vfValue` through `e`;
  2. concrete images of ambient definable maps (graph transfer by elementarity; `m`-rationality by
     the Galois action `levelRoots m`, `raw_original_definable_invariant`);
  3. the full truncation RES set (union over label patterns) and its normalized class;
  4. bounded sets: scale by `t^L` into `𝒪` (the lift `𝕃U` and zero-centred steps leave `𝒪`);
  5. general invariance: a definable map respecting truncations both ways gives a definable bijection
     of truncation sets (truncation of the thickened graph), hence equal classes;
  6. the steps of `SpecialCovariantChain`: regularize (cutoffs above the VF bound), centripetal (cutoff
     of the moved coordinate first, then the others from `CentripetalData.uniform_named_erased_covariance`),
     zero-centred (cutoffs above `v(center)`); uniform invariance radii from
     `properInvariant_uniform_named_radius`;
  7. the lift: `T_m(𝕃U) = η h_m [U]` (lattice parts, coefficient lines);
  8. assembly: `∫^◇[A] = [U]` for the lift data of `lemma_6_21_vfGenerated` (`exists_isomorphic_lift`).
- D2 progress (2026-11-21, all compiled, standard axioms):
  - step 1 `TruncAmbient.lean`: `lt_value_eVF_iff` (`π^β < v(e y) ↔ β < ordS y`), `fixed_iff_rational`,
    `labelFixed_iff`;
  - step 2 `TraceProjection.lean` (`trace_exists`: traces commute with projections),
    `TruncAmbient.lean` (`exists_concrete_image`, `concrete_image_rational`, `ePoint_injective`);
  - step 3 `TruncFull.lean` (`fullTruncSet`, `Covers`, `fullTruncSet_definable`,
    `fullTruncSet_finite_values`, `fullClass`);
  - step 5 `TruncInvariance.lean` (`fullClass_eq_of_correspondence`: a bijection of rational
    integral points respecting truncations, with a definable relation on truncations, preserves
    `fullClass`).
  - `TruncGraph.lean` (concrete congruence set, `truncOf_eq_iff`), `TruncPairs.lean`
    (`pairTrunc_relation_definable`, `fullClass_eq_of_thickened`): the relation on truncations
    induced by a definable set of pairs is definable.
  - step 4 `TruncScale.lean`: `scaleRaw L X = t^L X`, `fullClass_scale`
    (`[(t^L X)[m;β+L]]𝕃^{-mΣ(β+L)} = [X[m;β]]𝕃^{-mΣβ}𝕃^{-mnL}`, extension-by-zero isomorphism
    `zeroExtIso` of diagonal constructible objects).
  - `TruncStep.lean`: `fullClass_eq_of_ambient` — an ambient bijection `F : A → B` such that `F` and
    `F⁻¹` respect congruence at the radii `π^{b_i/m − L}` gives equal classes of the scaled traces
    (induced map `phiPt`, thickened graph from the trace of the graph of `F`, `invMap`).
  - `TruncGood.lean`: for proper invariant ambient sets, by elementarity: rational lower bound of
    valuations of concrete points (`vf_lower_bound`), bounded nonzero labels and finitely many label
    patterns (`label_bounds`, `covers_strace`), rational invariance radius (`amb_invariant`).
  - `TruncChain.lean`: `TEq` (equality of normalized classes at all admissible `L, b`), `teq_trans`
    (change of scale and cutoffs), `teq_of_step` (cofinal compatible cutoffs).
  - step 6 `TruncSteps.lean`: `regularize_compat`, `zeroCentered_compat`, `centripetal_compat`
    (anisotropic cutoffs: `β_j` above `v(cλ)`, then `β_i` from the uniform focus covariance for the
    radius `π^{β_j}`; the moved point `(x̂', x_j)` lies in the source by invariance, so no RV-pullback
    hypothesis is needed — this answers referee remark R173), `chain_teq`: **every special covariant
    chain preserves the normalized truncation class.**
  - next, step 7 (lift): for `U` doubly bounded with form `1`, value map `f`, the truncation set of
    `t^L 𝕃U` is `⊔_γ U^{rat}_γ × ∏_i ∏_{j > m(γ_i+L)} Line(j/m)` (fixed leading coefficient
    `f_i(u)·rv(t)^L`, zeros below); classes via `resSetClass_finite_partition`,
    `resSetClass_product`, `resSetClass_bijection`, `[Line] ↦ 𝕃`. Bridge to `h_m`:
    `Θ_amb[fibreChart w]` is `Θ` of the concrete trace (`elementaryRESReducedRestriction_class`),
    the trace of the lattice fibre of weight `w` is `⊔_{Σγ = w} U^{rat}_γ`.
    Done for step 7 so far: `ThetaBridge.lean` (`ambient_chart_class`: `Θ_amb[C] = Θ_conc[D]`,
    `x ∈ D ↔ e∘x ∈ C.domain`), `TruncLift.lean` part 1 (`exists_concrete_rv_image`).
    Refined plan for step 7: pieces `C_{w,z}` = restriction of `fibreChart w` to
    `codeValue(coordinate u i) = π^{z_i/m}` (`ValueMaps.preimage_definable`,
    `chart_coordinate_volume`), ambient partition (`RESPieces.classOn_biUnion`), bridge each to a
    concrete `D_{w,z}`; truncation pieces `T_{w,z} = T ∩ {labels ∈ D_{w,z}}`;
    `resSetClass_reindex` (to write: `r ↦ r ∘ π` bijective `A → B` gives equal classes) for
    `T_{w,z} ≅ D_{w,z} × Lines_z`, `Lines_z = rationalDescendedSet wt univ` (class
    `dcClass (affineSpace wt) = 𝕃^N`); surjectivity by the explicit point
    `x_i = c_i t^{(z_i+mL)/m} + Σ_{j free} lineCoeff(w_{ij}) t^{j/m}`; `etaTerm` exponent
    `−m·ratValue w = −Σz` on nonempty pieces (form `1`).
    Progress (2026-11-21): `LiftHm.lean` done — `zetaCoeff_chart`, `theta_classOn`,
    `chart_point`, `chart_weight`, **`zetaCoeff_U`** (`η h_m[U] = Σ_{w∈W} Σ_{z∈Z} Θ[D_{w,z}] 𝕃^{-Σz}`
    given a finite pattern set `Z` covering the concrete values, `hZ`); `LiftTrunc.lean` started
    (`rv_coeffs`, `rv_of_coeffs`, `lead`, `cf_lift`). Remaining for step 7: `T_{w,z}`, `Lines_z`,
    reindex bijection, partition, units algebra; value bounds for `hZ` (VF bounds of the lift).
    Step 8: `∫^◇[A] = [objOf U]` from `exists_isomorphic_lift`'s lift data `L` (iso invariance of
    `intQ`, `intQ_lift`), `chain_teq L.special`, and for `𝒳_f`: trace of `milnorObject` = `rawMilnor`,
    `fullClass_strace_shift` from `L = 0`.
- D1c (old note) the trace on the concrete model of a set definable over the base in the ambient
  (mixed sorts; `IsoLattice.trace_definable` is the RV case), the finite union over label patterns,
  the class `[A[m;β]]` and Lemma 8.5 for classes; induced bijections are definable (apply
  `coefficient_constructible` to the invariant set `{(x,y) | y ≡ F(x) mod 𝔪_β}`).
- Assessment of 2026-11-21: the definability input can be proved, and Denef–Pas elimination is not
  needed. For a β-invariant `A`, `A[m;β]` is the frame image of the coefficient set
  `C = {c | (Σ_j c_ij t^{j/m}, u) ∈ A}`, so no quantifier over ℂ((t^{1/m})) occurs. Route:
  (1) ACVF elimination (`Section3.DefinableOver.quantifier_free`, `rvOnly_correct`) gives
  `A = {(x,u) | (rv P_1(x), …, rv P_k(x), u) ∈ Ψ}` with polynomials `P_i` over the base and an RV
  set `Ψ` (induction over quantifier-free formulas); (2) `P_i(Σ c t^{j/m})` has coefficients
  polynomial in `c` (`MvPolynomial.induction_on`, `HahnSeries.coeff_mul_single_add`);
  (3) Hilbert's basis theorem bounds the leading index, so `rv P_i` is piecewise `rv(Q(c) t^{r/m})`;
  (4) `framedRVSet_pure_definable` (library) makes `{d | frame d ∈ Ψ}` constructible, and
  `rationalDescendedSet` with `rationalDescent_mem_image` turns the invariant constructible `C` back
  into a definable RES set. Induced bijections: apply the same to the invariant set
  `{(x,y) | y ≡ F(x) mod 𝔪_β}`. Estimated 1200–1800 lines.
