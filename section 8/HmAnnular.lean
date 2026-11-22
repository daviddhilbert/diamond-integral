import «section 8».HmAnnularShell

/-! Lemma 8.3: `η ∘ h_m` vanishes on `J_var ∩ K^♮_m μRV^db[*]`.

For an annular datum `D` with source `U`, let `W` be the weights of the lattice part of `U`, `G`
the aperture values on it, and `pc w g` the class of the piece of weight `w` and aperture value
`g = π^{M/m}` (`M = level g`). Then

* the lattice part of the endpoint of weight `w'` is the union of the graphs over the pieces with
  `w g = w'` (`endpoint_fibre`), so `h_m([endpoint]) = Σ_{w,g} T^{-m r(w) - M} Θ(pc w g)`;
* the lattice part of the shell of weight `w'` is the union of the slices at `π^{i/m}`,
  `1 ≤ i ≤ M`, over the pieces with `w π^{i/m} = w'` (`shell_fibre`), each of class
  `pc w g · [G_m]`, so `h_m([shell]) = Σ_{w,g} Σ_{i=1}^{M} T^{-m r(w) - i} Θ(pc w g) (𝕃 - 1)`;
* `h_m([U]) = Σ_{w,g} T^{-m r(w)} Θ(pc w g)` (`class_source`).

Hence `h_m(generator) = Σ_{w,g} T^{-m r(w)} Θ(pc w g) · a_M(𝕃, T⁻¹)` (`hm_generator`), with
`a_M(L, q) = (L - 1) Σ_{i<M} q^{i+1} + q^M - 1 = (L q - 1) Σ_{i<M} q^i` the annular factor of
Section 6. After inverting `𝕃` each term is a multiple of `𝕃 T⁻¹ - 1`, so `η ∘ h_m` kills the
manuscript ideal on the natural subring (`lemma_8_3`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.ValueMaps
open DiamondIntegral.Section8.RESPieces
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators

/-! ### The annular factor in `R[T^ℚ]` -/

section Algebra

variable {R : Type*} [CommRing R]

/-- The annular factor `(L - 1) Σ_{i<n} T^{-(i+1)} + T^{-n} - 1` in `R[T^ℚ]`. -/
def annPoly (L : R) (n : ℕ) : PuiseuxPolynomial R :=
  (AddMonoidAlgebra.single 0 L - 1) * ∑ i ∈ Finset.range n, AddMonoidAlgebra.single (-((i : ℚ) + 1)) 1 +
    AddMonoidAlgebra.single (-(n : ℚ)) 1 - 1

theorem ofLaurent_annularFactor (L : R) (n : ℕ) :
    PuiseuxPolynomial.ofLaurent R
        (Section6.ApertureSpecializationTest.annularFactor (LaurentPolynomial.C L) (LaurentPolynomial.T (-1)) n) =
      annPoly L n := by
  have hC : PuiseuxPolynomial.ofLaurent R (LaurentPolynomial.C L) = AddMonoidAlgebra.single 0 L := by
    rw [← LaurentPolynomial.single_eq_C, PuiseuxPolynomial.ofLaurent_single, Int.cast_zero]
  have hT : ∀ j : ℕ, PuiseuxPolynomial.ofLaurent R (LaurentPolynomial.T (-1) ^ j) =
      AddMonoidAlgebra.single (-(j : ℚ)) 1 := by
    intro j
    rw [LaurentPolynomial.T_pow, LaurentPolynomial.T, PuiseuxPolynomial.ofLaurent_single]
    congr 1
    push_cast; ring
  simp only [Section6.ApertureSpecializationTest.annularFactor, map_sub, map_add, map_mul, map_sum, map_one,
    hC, hT, annPoly]
  push_cast
  rfl

theorem annPoly_map {S : Type*} [CommRing S] (f : R →+* S) (L : R) (n : ℕ) :
    AddMonoidAlgebra.mapRingHom ℚ f (annPoly L n) = annPoly (f L) n := by
  simp [annPoly, map_sub, map_add, map_mul, map_sum, map_one, AddMonoidAlgebra.mapRingHom_single]

theorem single_mul_annPoly (q : ℚ) (x L : R) (n : ℕ) :
    AddMonoidAlgebra.single q x * annPoly L n =
      ∑ i ∈ Finset.range n, AddMonoidAlgebra.single (q - ((i : ℚ) + 1)) (x * (L - 1)) +
        AddMonoidAlgebra.single (q - n) x - AddMonoidAlgebra.single q x := by
  have h1 : (AddMonoidAlgebra.single 0 L - 1 : PuiseuxPolynomial R) = AddMonoidAlgebra.single 0 (L - 1) := by
    rw [AddMonoidAlgebra.single_sub, AddMonoidAlgebra.one_def]
  rw [annPoly, h1, mul_sub, mul_add, Finset.mul_sum, Finset.mul_sum, mul_one]
  congr 2
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, mul_one]
    congr 1
    ring
  · rw [AddMonoidAlgebra.single_mul_single, mul_one, sub_eq_add_neg]

end Algebra

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-! ### The torus class -/

theorem nativeRESChartClass_fibre (α : Γ) (hα : GammaDefinableClosureAtBase (base P) α) :
    nativeRESChartClass (RESFibreObjects.fibre (base P) α 1 hα (GammaGroupNames.one_definable_base _)) =
      nativeTorusClass (base P) := by
  rw [nativeRESChartClass, ← RESDimensionFreeReduction.fromGradedReduced_raw,
    RESOrdinaryReduction.fibre_class]
  rfl

theorem theta_torus : theta P (nativeTorusClass (base P)) = modifiedTorusClass := by
  rw [theta, ambientPuiseuxComparisonEquiv_apply]
  exact ambientPuiseuxComparison_nativeTorusClass P.hc P.e (base P) P.hB _

/-! ### `h_m` from a decomposition of the lattice parts -/

/-- If the class of the lattice part of each weight `w'` is the sum of the `c t` with
`wt t = w'`, then `h_m` is the sum of the `T^{-m r(wt t)} Θ(c t)`. -/
theorem hmValue_decomp {kk : ℕ} (a : Chart (base P) kk) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) {ι : Type*} (T : Finset ι) (wt : ι → Γ) (c : ι → RESDimensionFreeReduction.Ring (base P))
    (hfib : ∀ w', nativeRESChartClass (fibreChart P a ha m w') =
      ∑ t ∈ T.filter (fun t => wt t = w'), c t)
    (hsupp : ∀ w' ∈ weights P a ha m, ∃ t ∈ T, wt t = w') :
    hmValue P a ha m =
      ∑ t ∈ T, AddMonoidAlgebra.single (-(m : ℚ) * ratValue π (wt t)) (theta P (c t)) := by
  rw [hmValue_eq_sum P a ha m (T.image wt) fun w' hw' => by
      obtain ⟨t, ht, rfl⟩ := hsupp w' hw'
      exact Finset.mem_image_of_mem wt ht,
    ← Finset.sum_fiberwise_of_maps_to (g := wt) (t := T.image wt)
      (fun t ht => Finset.mem_image_of_mem wt ht)]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [hmTerm, hfib, map_sum]
  refine (map_sum (AddMonoidAlgebra.singleAddHom (-(m : ℚ) * ratValue π w'))
    (fun t => theta P (c t)) (T.filter (fun t => wt t = w'))).trans
    (Finset.sum_congr rfl fun t ht => ?_)
  rw [(Finset.mem_filter.mp ht).2]
  rfl

variable {k : ℕ} (D : AnnularDatum (base P) k) (m : ℕ+)

/-! ### Rational values of the weights -/

theorem exponent_qpow {w : Γ} (hw : w ∈ weights P D.chart D.bounded m) (n : ℕ) :
    -(m : ℚ) * ratValue π (w * qpow π ((n : ℚ) / (m : ℕ))) = -(m : ℚ) * ratValue π w - n := by
  have hπ := one_lt_uniformizerValue P
  rw [ratValue_mul hπ (weight_rational P D.chart D.bounded m hw) (isRationalValue_qpow π _), ratValue_qpow hπ]
  have hmq : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.ne_zero
  have : ((m : ℕ+) : ℚ) = ((m : ℕ) : ℚ) := rfl
  rw [this]
  field_simp
  ring

/-! ### The source -/

theorem hm_source :
    hmValue P D.chart D.bounded m =
      ∑ p ∈ weights P D.chart D.bounded m ×ˢ apValues P D m,
        AddMonoidAlgebra.single (-(m : ℚ) * ratValue π p.1) (theta P (pieceClass P D m p.1 p.2)) := by
  rw [hmValue, Finset.sum_product]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hmTerm, class_source, map_sum]
  exact map_sum (AddMonoidAlgebra.singleAddHom (-(m : ℚ) * ratValue π w)) _ _

/-! ### The endpoint -/

theorem endpoint_class (w' : Γ) :
    nativeRESChartClass (fibreChart P (endC P D) (endC_bounded P D) m w') =
      ∑ p ∈ (weights P D.chart D.bounded m ×ˢ apValues P D m).filter (fun p => p.1 * p.2 = w'),
        pieceClass P D m p.1 p.2 := by
  rw [← classOn_domain, fibreChart_domain, endpoint_fibre,
    classOn_biUnion _ _ _
      (fun p hp => endPiece_definable P D m p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
      (fun p hp => fun u hu => by
        rw [fibreChart_domain, ← (Finset.mem_filter.mp hp).2]
        exact endPiece_subset P D m hu)
      (endPieces_disjoint P D m w')]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hT, hw⟩ := Finset.mem_filter.mp hp
  rw [← hw]
  exact endpoint_pieceClass P D m (Finset.mem_product.mp hT).2

theorem hm_endpoint :
    hmValue P (endC P D) (endC_bounded P D) m =
      ∑ p ∈ weights P D.chart D.bounded m ×ˢ apValues P D m,
        AddMonoidAlgebra.single (-(m : ℚ) * ratValue π p.1 - level P m p.2)
          (theta P (pieceClass P D m p.1 p.2)) := by
  have hfib : ∀ w', nativeRESChartClass (fibreChart P (endC P D) (endC_bounded P D) m w') =
      ∑ p ∈ (weights P D.chart D.bounded m ×ˢ apValues P D m).filter
        (fun p : Γ × Γ => (fun p : Γ × Γ => p.1 * p.2) p = w'),
        (fun p : Γ × Γ => pieceClass P D m p.1 p.2) p := endpoint_class P D m
  rw [hmValue_decomp P (endC P D) (endC_bounded P D) m (weights P D.chart D.bounded m ×ˢ apValues P D m)
    (fun p : Γ × Γ => p.1 * p.2) (fun p : Γ × Γ => pieceClass P D m p.1 p.2) hfib fun w' hw' => ?_]
  · refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    congr 1
    conv_lhs => rw [apValue_eq_level P D m h2]
    exact exponent_qpow P D m h1 _
  · obtain ⟨u, hu⟩ := (mem_weights P _ (endC_bounded P D) m w').mp hw'
    rw [endpoint_fibre] at hu
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter] at hu
    obtain ⟨p, ⟨hp, hpw⟩, -⟩ := hu
    exact ⟨p, hp, hpw⟩

/-! ### The shell -/

/-- Indices of the shell slices: a piece `(w, g)` and `i < M`, for the slice at `π^{(i+1)/m}`. -/
def shellIdx : Finset (Σ _ : Γ × Γ, ℕ) :=
  (weights P D.chart D.bounded m ×ˢ apValues P D m).sigma fun p => Finset.range (level P m p.2)

/-- The weight of a shell slice. -/
def shellWt (t : Σ _ : Γ × Γ, ℕ) : Γ := t.1.1 * qpow π (((t.2 + 1 : ℕ) : ℚ) / (m : ℕ))

theorem mem_shellIdx (t : Σ _ : Γ × Γ, ℕ) : t ∈ shellIdx P D m ↔
    t.1.1 ∈ weights P D.chart D.bounded m ∧ t.1.2 ∈ apValues P D m ∧ t.2 < level P m t.1.2 := by
  simp [shellIdx, Finset.mem_sigma, Finset.mem_product, and_assoc]

theorem shell_fibre (w' : Γ) :
    latticeFibre P (shC P D) m w' =
      ⋃ t ∈ (shellIdx P D m).filter (fun t => shellWt P m t = w'),
        shellPiece P D m t.1.1 t.1.2 (t.2 + 1) := by
  ext u
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter]
  constructor
  · rintro ⟨hl, hw⟩
    obtain ⟨hu, hx, hs⟩ := (shell_lattice P D m u).mp hl
    obtain ⟨z, hz⟩ := eq_qpow_of_inLattice m.ne_zero hs
    obtain ⟨-, -, h1, h2⟩ := shell_mem D.chart D.aperture hu
    have hap := shell_aperture P D hu
    have hg : gam P D (u ∘ xIdx D.chart) ∈ apValues P D m :=
      (mem_apValues P D m _).mpr ⟨_, hx, rfl⟩
    have hmq : (0 : ℚ) < (m : ℕ) := by exact_mod_cast m.pos
    have hz1 : 0 < z := by
      rw [hz, ← qpow_zero' P, qpow_lt_iff] at h1
      have h := (div_pos_iff_of_pos_right hmq).mp h1
      exact_mod_cast h
    have hz2 : z ≤ level P m (gam P D (u ∘ xIdx D.chart)) := by
      rw [hap, hz] at h2
      change qpow π _ ≤ gam P D (u ∘ xIdx D.chart) at h2
      rw [apValue_eq_level P D m hg, qpow_le_iff] at h2
      have h := (div_le_div_iff_of_pos_right hmq).mp h2
      exact_mod_cast h
    have hzi : (((z.toNat - 1 + 1 : ℕ) : ℤ)) = z := by omega
    have hzq : (((z.toNat - 1 + 1 : ℕ)) : ℚ) = (z : ℚ) := by exact_mod_cast hzi
    refine ⟨⟨(D.chart.correctedWeight (u ∘ xIdx D.chart), gam P D (u ∘ xIdx D.chart)), z.toNat - 1⟩,
      ⟨(mem_shellIdx P D m _).mpr ⟨(mem_weights P _ D.bounded m _).mpr ⟨_, hx, rfl⟩, hg, ?_⟩, ?_⟩,
      hu, ⟨hx, rfl, rfl⟩, ?_⟩
    · change z.toNat - 1 < level P m (gam P D (u ∘ xIdx D.chart))
      omega
    · change D.chart.correctedWeight (u ∘ xIdx D.chart) * qpow π ((((z.toNat - 1 + 1 : ℕ)) : ℚ) / (m : ℕ)) = w'
      rw [hzq, ← hz, ← hw]
      exact (shell_weight D.chart D.coordinate D.finite D.aperture u hu).symm
    · change codeValue (u (sIdx D.chart)) = qpow π ((((z.toNat - 1 + 1 : ℕ)) : ℚ) / (m : ℕ))
      rw [hzq, hz]
  · rintro ⟨t, ⟨-, ht⟩, hu⟩
    rw [← ht]
    exact shellPiece_subset P D m (t.2 + 1) hu

theorem shellPieces_disjoint (w' : Γ) :
    (((shellIdx P D m).filter (fun t => shellWt P m t = w') : Finset _) :
      Set (Σ _ : Γ × Γ, ℕ)).PairwiseDisjoint (fun t => shellPiece P D m t.1.1 t.1.2 (t.2 + 1)) := by
  intro t _ t' _ htt
  rw [Function.onFun, Set.disjoint_left]
  rintro u ⟨-, ⟨-, h1, h2⟩, h3⟩ ⟨-, ⟨-, h1', h2'⟩, h3'⟩
  apply htt
  have hi : t.2 = t'.2 := by
    have h := h3.symm.trans h3'
    have hq := le_antisymm ((qpow_le_iff P).mp h.le) ((qpow_le_iff P).mp h.ge)
    have hmq : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.ne_zero
    rw [div_left_inj' hmq] at hq
    have : t.2 + 1 = t'.2 + 1 := by exact_mod_cast hq
    omega
  exact Sigma.ext (Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')) (heq_of_eq hi)

theorem shell_class (w' : Γ) :
    nativeRESChartClass (fibreChart P (shC P D) (shC_bounded P D) m w') =
      ∑ t ∈ (shellIdx P D m).filter (fun t => shellWt P m t = w'),
        pieceClass P D m t.1.1 t.1.2 * nativeTorusClass (base P) := by
  rw [← classOn_domain, fibreChart_domain, shell_fibre,
    classOn_biUnion _ _ _
      (fun t ht => shellPiece_definable P D m t.1.1
        ((mem_shellIdx P D m t).mp (Finset.mem_filter.mp ht).1).2.1 (t.2 + 1))
      (fun t ht => fun u hu => by
        rw [fibreChart_domain, ← (Finset.mem_filter.mp ht).2]
        exact shellPiece_subset P D m (t.2 + 1) hu)
      (shellPieces_disjoint P D m w')]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨hT, hw⟩ := Finset.mem_filter.mp ht
  obtain ⟨-, hg, hi⟩ := (mem_shellIdx P D m t).mp hT
  rw [← hw]
  have h := shell_pieceClass P D m (w := t.1.1) hg (Nat.le_add_left 1 t.2) hi
  rw [nativeRESChartClass_fibre] at h
  exact h

theorem hm_shell :
    hmValue P (shC P D) (shC_bounded P D) m =
      ∑ p ∈ weights P D.chart D.bounded m ×ˢ apValues P D m, ∑ i ∈ Finset.range (level P m p.2),
        AddMonoidAlgebra.single (-(m : ℚ) * ratValue π p.1 - ((i : ℚ) + 1))
          (theta P (pieceClass P D m p.1 p.2) * modifiedTorusClass) := by
  rw [hmValue_decomp P (shC P D) (shC_bounded P D) m (shellIdx P D m) (shellWt P m)
    (fun t => pieceClass P D m t.1.1 t.1.2 * nativeTorusClass (base P)) (shell_class P D m)
    fun w' hw' => ?_, shellIdx, Finset.sum_sigma]
  · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, theta_torus]
    congr 1
    rw [shellWt, exponent_qpow P D m (Finset.mem_product.mp hp).1]
    push_cast; ring
  · obtain ⟨u, hu⟩ := (mem_weights P _ (shC_bounded P D) m w').mp hw'
    rw [shell_fibre] at hu
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter] at hu
    obtain ⟨t, ⟨ht, htw⟩, -⟩ := hu
    exact ⟨t, ht, htw⟩

/-! ### Lemma 8.3 -/

/-- **`h_m` of an annular generator.** -/
theorem hm_generator :
    hm P m D.generator =
      ∑ p ∈ weights P D.chart D.bounded m ×ˢ apValues P D m,
        AddMonoidAlgebra.single (-(m : ℚ) * ratValue π p.1) (theta P (pieceClass P D m p.1 p.2)) *
          annPoly modifiedAffineLineClass (level P m p.2) := by
  rw [AnnularDatum.generator_eq, map_sub, map_add, hm_objectClass, hm_objectClass, hm_objectClass]
  change hmValue P (shC P D) (shC_bounded P D) m + hmValue P (endC P D) (endC_bounded P D) m -
    hmValue P D.chart D.bounded m = _
  rw [hm_shell, hm_endpoint, hm_source, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [single_mul_annPoly]
  rfl

theorem hmLoc_generator_mem :
    hmLoc P m D.generator ∈
      Ideal.span {PuiseuxPolynomial.ofLaurent Rloc (PuiseuxPolynomial.annularElement Lunit)} := by
  rw [hmLoc, RingHom.comp_apply, hm_generator, map_sum]
  refine Ideal.sum_mem _ fun p _ => ?_
  rw [map_mul, toLoc_single, toLoc, annPoly_map, ← Lunit_val, ← ofLaurent_annularFactor]
  exact PuiseuxPolynomial.annular_mem_span Lunit _ _ _

/-- **Lemma 8.3.** `η ∘ h_m` vanishes on `J_var ∩ K^♮_m μRV^db[*]`. -/
theorem lemma_8_3 (x : naturalRing P m) (hx : (x : RVBoundedRing.Ring (base P)) ∈ manuscriptIdeal (base P)) :
    etaHm P m x = 0 := by
  refine PuiseuxPolynomial.etaNatural_eq_zero (hmLoc P m) Lunit _ ?_ x hx
  rintro g ⟨kk, D, rfl⟩
  exact hmLoc_generator_mem P D m

end DiamondIntegral.Section8.Hm
