import «section 8».ValueMaps
import «section 8».PuiseuxBase
import FubiniTheorems.Prerequisites.Grothendieck.ResidueGammaTupleColumns
import FubiniTheorems.Prerequisites.Grothendieck.IntegrationGammaParameters
import FubiniTheorems.Prerequisites.Euler.RVBoundedRing

/-! The lattice part of a chart, the first step towards `h_m`.

In the Puiseux ambient `P` with base `⟨G.real, ∅⟩` and `π` the value of `t`, let `a` be a bounded
chart with domain `U`. Its lattice part at level `m ≥ 1` is
`latticeDomain a m = {u ∈ U | every codeValue (u i) is in π^{m⁻¹ℤ}}` (the RV zero has `codeValue`
`1`, a lattice point). We show:

* `chart_pow_bound`: the nonzero coordinates of `U` are bounded by a power of `π`;
* `latticeDomain_definable`;
* `latticeWeights_finite`: the corrected weight takes finitely many values on the lattice part
  (residue–value-group orthogonality, `residue_gamma_tuple_finite_columns`);
* `latticeWeight_definable`, `latticeWeight_rational`: these values are definable, hence rational
  powers of `π`;
* `latticeFibre_definable`: the lattice part with a given weight is definable. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues
open DiamondIntegral.Section8.ValueMaps DiamondIntegral.Section5.PuiseuxOriginal
open IntegrationInACVF.Section3ACVF

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-! ### Lattice boxes -/

/-- The lattice points of `Γ` at level `m` between `π^{-N}` and `π^N`. -/
def latticeBox (m N : ℕ) : Set Γ :=
  {γ | InLattice π m γ ∧ π ^ (-(N : ℤ)) ≤ γ ∧ γ ≤ π ^ (N : ℤ)}

theorem latticeBox_finite {m : ℕ} (hm : m ≠ 0) (N : ℕ) : (latticeBox P m N).Finite :=
  finite_lattice_Icc (one_lt_uniformizerValue P) hm _ _

theorem one_mem_latticeBox (m N : ℕ) : (1 : Γ) ∈ latticeBox P m N := by
  have hmono := (zpow_right_strictMono (one_lt_uniformizerValue P)).monotone
  refine ⟨inLattice_one _ _, ?_, ?_⟩
  · simpa using hmono (show -(N : ℤ) ≤ 0 by omega)
  · simpa using hmono (show (0 : ℤ) ≤ N by omega)

theorem latticeBox_definable {m : ℕ} (hm : m ≠ 0) (N : ℕ) :
    GammaDefinableOverBase (base P) (latticeBox P m N) := by
  have hfin := latticeBox_finite P hm N
  have he : latticeBox P m N = ⋃ γ ∈ hfin.toFinset, ({γ} : Set Γ) := by
    ext γ; simp
  rw [he]
  refine GammaOrderLogic.finite_union_definable_base (base P) _ _ fun γ hγ => ?_
  obtain ⟨z, rfl⟩ := eq_qpow_of_inLattice hm ((hfin.mem_toFinset.mp hγ).1)
  exact qpow_definable P _

/-! ### Bounds on charts -/

theorem nonzero_coord_definable {n : ℕ} {I : Set (Fin n → P.N)}
    (hI : DefinableOverBase (base P) (fun _ : Fin n => .rv) I) (i : Fin n) :
    DefinableOverBase (base P) (fun _ : Fin n => .rv) {u | u ∈ I ∧ NonzeroRV (u i)} := by
  have h := DefinableOverBase.inter hI ((GammaOrderLogic.proper_definable_base (base P) 1).preimage_real
    (fun _ : Fin n => .rv) (fun _ : Fin 1 => i))
  convert h using 1
  refine Set.ext fun u => ⟨fun ⟨hu, h0⟩ => ⟨hu, fun _ => h0, fun j => hI.proper u hu j⟩,
    fun ⟨hu, h0, _⟩ => ⟨hu, h0 0⟩⟩

/-- The nonzero coordinates of a bounded chart lie between powers of `π`. -/
theorem chart_pow_bound {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) :
    ∃ N : ℕ, ∀ u ∈ a.domain, ∀ i, NonzeroRV (u i) →
      π ^ (-(N : ℤ)) ≤ codeValue (u i) ∧ codeValue (u i) ≤ π ^ (N : ℤ) := by
  obtain ⟨β, hβ⟩ := a.domain_bounded
  have hi : ∀ i : Fin a.arity, ∃ N : ℕ, ∀ u ∈ a.domain, NonzeroRV (u i) →
      π ^ (-(N : ℤ)) ≤ codeValue (u i) ∧ codeValue (u i) ≤ π ^ (N : ℤ) := by
    intro i
    have hI := nonzero_coord_definable P a.domain_definable i
    have himg := image_definable (base P) (volume_restrict (base P)
      (coord_volume_definable (base P) a.domain_definable i) hI (fun _ h => h.1))
    have hY := (GammaOrderLogic.unary_definable_iff (base P) _).mpr himg
    obtain ⟨N, hN⟩ := PuiseuxValues.exists_pow_bound P _ hY β (by
      rintro y ⟨u, ⟨hu, h0⟩, huy⟩ j
      rw [Subsingleton.elim j 0, ← huy]
      exact hβ u hu i h0)
    exact ⟨N, fun u hu h0 => hN (fun _ => codeValue (u i)) ⟨u, ⟨hu, h0⟩, rfl⟩ 0⟩
  choose N hN using hi
  refine ⟨Finset.univ.sup N, fun u hu i h0 => ?_⟩
  have hle : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨h1, h2⟩ := hN i u hu h0
  have hmono := (zpow_right_strictMono (one_lt_uniformizerValue P)).monotone
  exact ⟨le_trans (hmono (by omega)) h1, le_trans h2 (hmono (by omega))⟩

/-! ### The lattice part of a chart -/

/-- The points of the domain all of whose coordinates have values in the lattice `π^{m⁻¹ℤ}`. -/
def latticeDomain {k : ℕ} (a : Chart (base P) k) (m : ℕ) : Set (Fin a.arity → P.N) :=
  {u | u ∈ a.domain ∧ ∀ i, InLattice π m (codeValue (u i))}

theorem latticeDomain_subset {k : ℕ} (a : Chart (base P) k) (m : ℕ) :
    latticeDomain P a m ⊆ a.domain := fun _ h => h.1

theorem latticeDomain_eq_box {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) (m N : ℕ)
    (hN : ∀ u ∈ a.domain, ∀ i, NonzeroRV (u i) →
      π ^ (-(N : ℤ)) ≤ codeValue (u i) ∧ codeValue (u i) ≤ π ^ (N : ℤ)) :
    latticeDomain P a.toChart m = {u | u ∈ a.domain ∧ ∀ i, codeValue (u i) ∈ latticeBox P m N} := by
  refine Set.ext fun u => ⟨fun ⟨hu, hl⟩ => ⟨hu, fun i => ?_⟩, fun ⟨hu, hl⟩ => ⟨hu, fun i => (hl i).1⟩⟩
  by_cases h0 : NonzeroRV (u i)
  · exact ⟨hl i, hN u hu i h0⟩
  · have : codeValue (u i) = 1 := by simp only [codeValue, h0, ↓reduceDIte]
    rw [this]; exact one_mem_latticeBox P m N

theorem forall_coord_definable {n : ℕ} {I : Set (Fin n → P.N)}
    (hI : DefinableOverBase (base P) (fun _ : Fin n => .rv) I) {Λ : Set Γ}
    (hΛ : GammaDefinableOverBase (base P) Λ) (s : Finset (Fin n)) :
    DefinableOverBase (base P) (fun _ : Fin n => .rv)
      {u | u ∈ I ∧ ∀ i ∈ s, codeValue (u i) ∈ Λ} := by
  induction s using Finset.induction_on with
  | empty => simpa using hI
  | insert j s hj ih =>
    have h := DefinableOverBase.inter ih (preimage_definable (base P) hI
      (coord_volume_definable (base P) hI j) hΛ)
    convert h using 1
    refine Set.ext fun u => ⟨fun ⟨hu, hl⟩ => ⟨⟨hu, fun i hi => hl i (Finset.mem_insert_of_mem hi)⟩,
      hu, hl j (Finset.mem_insert_self j s)⟩, fun ⟨⟨hu, hl⟩, _, hj'⟩ => ⟨hu, fun i hi => ?_⟩⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hj'
    · exact hl i hi

theorem latticeDomain_definable {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) {m : ℕ}
    (hm : m ≠ 0) : DefinableOverBase (base P) (fun _ : Fin a.arity => .rv)
      (latticeDomain P a.toChart m) := by
  obtain ⟨N, hN⟩ := chart_pow_bound P a
  rw [latticeDomain_eq_box P a m N hN]
  simpa using forall_coord_definable P a.domain_definable (latticeBox_definable P hm N) Finset.univ

/-! ### Weights on the lattice part -/

theorem base_nontrivial : Section2.NontrivialDefinableGamma (base P) :=
  ⟨π, 1, uniformizerValue_definable P, GammaGroupNames.one_definable_base _,
    (one_lt_uniformizerValue P).ne'⟩

/-- **Finitely many weights.** The corrected weight takes finitely many values on the lattice
part of a bounded chart. -/
theorem latticeWeights_finite {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) {m : ℕ}
    (hm : m ≠ 0) : (a.correctedWeight '' latticeDomain P a.toChart m).Finite := by
  obtain ⟨N, hN⟩ := chart_pow_bound P a
  have hL := latticeDomain_definable P a hm
  have hV : VolumeDefinable (base P) (latticeDomain P a.toChart m) a.correctedWeight :=
    volume_restrict (base P) (weight_volume_definable (base P) a.toChart) hL
      (latticeDomain_subset P a.toChart m)
  let R : (Fin a.arity → P.N) → (Fin 1 → Γ) → Prop := fun u γ =>
    u ∈ latticeDomain P a.toChart m ∧ γ 0 = a.correctedWeight u
  let σ : Fin (a.arity + 1) → Fin a.arity ⊕ Fin 1 := Fin.cons (Sum.inr 0) Sum.inl
  have hR : mixedGammaTupleDefinable (base P) R := by
    have h := FullRawDefinable.reindex (P := fun w : Fin (a.arity + 1) → P.N =>
      w ∈ volumeGraph (latticeDomain P a.toChart m) a.correctedWeight) (integrationGammaDefinable hV) σ
    refine FullBaseAtomicity.OverBase.congr h fun z => ?_
    change (z ∘ σ) ∈ volumeGraph _ _ ↔ _
    have htail : Fin.tail (z ∘ σ) = z ∘ Sum.inl := funext fun i => rfl
    have h0 : (z ∘ σ) 0 = z (Sum.inr 0) := rfl
    rw [mem_volumeGraph, htail, h0]
    change _ ↔ (∀ i : Fin 1, NonzeroRV (z (Sum.inr i))) ∧ z ∘ Sum.inl ∈ latticeDomain P a.toChart m ∧
      codeValue (z (Sum.inr 0)) = a.correctedWeight (z ∘ Sum.inl)
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨fun i => by rw [Subsingleton.elim i 0]; exact h2, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1 0, h3⟩
  let D : Fin a.arity → Set P.N := fun _ => {x | iRV x ∧ codeValue x ∈ latticeBox P m N}
  have hD : ∀ i, DefinableAtBase (base P) .rv (D i) := by
    intro i
    have hU := BlowupChart.rv_universe_definable (base P) 1
    have h := preimage_definable (base P) hU (coord_volume_definable (base P) hU 0)
      (latticeBox_definable P hm N)
    show DefinableOverBase (base P) (fun _ : Fin 1 => .rv) {z | z 0 ∈ D i}
    convert h using 1
    refine Set.ext fun z => ?_
    change (iRV (z 0) ∧ codeValue (z 0) ∈ latticeBox P m N) ↔
      (z ∈ sortedUniverse (fun _ : Fin 1 => SortTag.rv) ∧ codeValue (z 0) ∈ latticeBox P m N)
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun j => by rw [Subsingleton.elim j 0]; exact h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1 0, h2⟩⟩
  have hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort P.N | t.val ∈ D i}).Finite := by
    intro i
    refine ((((latticeBox_finite P hm N).image Subtype.val).insert Values.infinity)).subset ?_
    rintro x ⟨t, ht, rfl⟩
    by_cases h0 : t.val = iRVZero
    · exact Or.inl ((Values.vrv_eq_infinity_iff t).mpr h0)
    · right
      refine ⟨codeValue t.val, ht.2, ?_⟩
      have hf := RVMeasuredBounds.finiteValue_vrv t
      have hne : Values.vrv t ≠ Values.infinity := fun h => h0 ((Values.vrv_eq_infinity_iff t).mp h)
      rw [← hf]
      simp only [RVMeasuredBounds.finiteValue, hne, ne_eq, not_false_eq_true, ↓reduceDIte]
  have hsub : ∀ u ∈ latticeDomain P a.toChart m, ∀ i, u i ∈ D i := by
    intro u hu i
    rw [latticeDomain_eq_box P a m N hN] at hu
    exact ⟨a.domain_definable.proper u hu.1 i, hu.2 i⟩
  have hcols := residue_gamma_tuple_finite_columns P.G.uncountable.le P.G.saturated P.G.model00
    (base P) P.G.small_real (by simpa using Cardinal.aleph0_pos.trans P.G.uncountable)
    (base_nontrivial P) R hR (fun u _ h i => a.domain_definable.proper u h.1.1 i)
    (latticeDomain P a.toChart m) hL D hD hvalues hsub
  refine (hcols.biUnion (t := fun S => (fun γ : Fin 1 → Γ => γ 0) '' S) fun S hS => ?_).subset ?_
  · obtain ⟨u, hu, rfl⟩ := hS
    refine (Set.finite_singleton (a.correctedWeight u)).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    exact hγ.2
  · rintro _ ⟨u, hu, rfl⟩
    refine Set.mem_biUnion (x := relationColumn (fun γ u => R u γ) u) ⟨u, hu, rfl⟩ ?_
    exact ⟨fun _ => a.correctedWeight u, ⟨hu, rfl⟩, rfl⟩

theorem latticeWeights_definable {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) {m : ℕ}
    (hm : m ≠ 0) : GammaDefinableOverBase (base P) (a.correctedWeight '' latticeDomain P a.toChart m) :=
  image_definable (base P) (volume_restrict (base P) (weight_volume_definable (base P) a.toChart)
    (latticeDomain_definable P a hm) (latticeDomain_subset P a.toChart m))

theorem latticeWeight_definable {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) {m : ℕ}
    (hm : m ≠ 0) {w : Γ} (hw : w ∈ a.correctedWeight '' latticeDomain P a.toChart m) :
    GammaDefinableClosureAtBase (base P) w := by
  have hfin := latticeWeights_finite P a hm
  refine gamma_finset_element_definable_base (base P) hfin.toFinset ?_ w (hfin.mem_toFinset.mpr hw)
  rw [hfin.coe_toFinset]
  exact latticeWeights_definable P a hm

theorem latticeWeight_rational {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) {m : ℕ}
    (hm : m ≠ 0) {w : Γ} (hw : w ∈ a.correctedWeight '' latticeDomain P a.toChart m) :
    ∃ q : ℚ, w = qpow π q :=
  PuiseuxValues.definable_point_rational P (latticeWeight_definable P a hm hw)

/-- The lattice part with a given weight is definable (empty unless the weight occurs). -/
theorem latticeFibre_definable {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) {m : ℕ}
    (hm : m ≠ 0) (w : Γ) : DefinableOverBase (base P) (fun _ : Fin a.arity => .rv)
      {u | u ∈ latticeDomain P a.toChart m ∧ a.correctedWeight u = w} := by
  have hL := latticeDomain_definable P a hm
  by_cases hw : w ∈ a.correctedWeight '' latticeDomain P a.toChart m
  · exact preimage_definable (base P) hL (volume_restrict (base P)
      (weight_volume_definable (base P) a.toChart) hL (latticeDomain_subset P a.toChart m))
      (latticeWeight_definable P a hm hw)
  · have he : {u | u ∈ latticeDomain P a.toChart m ∧ a.correctedWeight u = w} = ∅ :=
      Set.eq_empty_of_forall_notMem fun u hu => hw ⟨u, hu.1, hu.2⟩
    rw [he]
    have h := (BlowupChart.rv_universe_definable (base P) a.arity).compl
    simpa using h

end DiamondIntegral.Section8.Hm
