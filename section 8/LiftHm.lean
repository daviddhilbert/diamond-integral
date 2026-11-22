import «section 8».TruncLift
import «section 8».Theorem811RV
import «section 7».ChartOfMeasured

/-! `η ∘ h_m` on a chart, split into value-pattern pieces with concrete classes.

* `zetaCoeff_chart`: `η h_m [a] = Σ_w ηterm(−m w) Θ([a^{(m)}_w])`;
* `theta_fibre_split`: `Θ([a^{(m)}_w])` is the sum of the concrete classes of the pieces where the
  structural coordinates have the values `π^{z_i/m}` (`z ∈ Z`), plus the concrete class of the rest. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm DiamondIntegral.Section8.ValueMaps DiamondIntegral.Section8.RESPieces
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells

local instance liftHmStructure : LRV.Structure Carrier := canonicalInterpret
local instance liftHmModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-- **`η h_m` on a chart.** -/
theorem zetaCoeff_chart {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) (m : ℕ+) :
    zetaCoeff P (RVBoundedRing.objectClass a) m =
      ∑ w ∈ weights P a.toChart a.domain_bounded m, etaTerm Lunit (-(m : ℚ) * ratValue π w)
        (algebraMap _ Rloc (theta P (nativeRESChartClass (fibreChart P a.toChart a.domain_bounded m w)))) := by
  unfold zetaCoeff
  rw [dite_eq_right_of_eq_false (eq_false m.ne_zero)]
  have hm : (⟨(m : ℕ), Nat.pos_of_ne_zero m.ne_zero⟩ : ℕ+) = m := PNat.eq rfl
  rw [hm]
  unfold hmLoc
  rw [RingHom.comp_apply, hm_objectClass, hmValue, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hmTerm, toLoc_single, eta_integerPart_single]

/-- Points of a set whose structural coordinates have prescribed values. -/
theorem coord_values_definable {k : ℕ} (a : Chart (base P) k) {I : Set (Fin a.arity → P.N)}
    (hI : DefinableOverBase (base P) (fun _ : Fin a.arity => .rv) I) (hIs : I ⊆ a.domain)
    (Λ : Fin k → Γ) (hΛ : ∀ i, GammaDefinableClosureAtBase (base P) (Λ i)) (s : Finset (Fin k)) :
    DefinableOverBase (base P) (fun _ : Fin a.arity => .rv)
      {u | u ∈ I ∧ ∀ i ∈ s, codeValue (a.coordinate u i) = Λ i} := by
  induction s using Finset.induction_on with
  | empty => simpa using hI
  | insert j s hj ih =>
    have hv : VolumeDefinable (base P) I (fun x => codeValue (a.coordinate x j)) :=
      volume_restrict (base P) (chart_coordinate_volume (base P) a j) hI hIs
    have h := DefinableOverBase.inter ih (preimage_definable (base P) hI hv (hΛ j))
    convert h using 1
    refine Set.ext fun u => ⟨fun ⟨hu, hl⟩ => ⟨⟨hu, fun i hi => hl i (Finset.mem_insert_of_mem hi)⟩,
      hu, hl j (Finset.mem_insert_self j s)⟩, fun ⟨⟨hu, hl⟩, _, hj'⟩ => ⟨hu, fun i hi => ?_⟩⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hj'
    · exact hl i hi

/-- `Θ` of a piece of an RES chart, as the class of its concrete trace. -/
theorem theta_classOn {k : ℕ} (C : RESChart (base P) k) (I : Set (Fin C.arity → P.N))
    (hI : DefinableOverBase (base P) (fun _ : Fin C.arity => .rv) I) (hs : I ⊆ C.domain) :
    ∃ (D : DefSet (rawRVSpace (M := Carrier) C.arity) {c | baseCarrier c})
      (hD : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite),
      (∀ x, x ∈ D.carrier ↔ (fun i => P.e (x i).val) ∈ I) ∧
      theta P (classOn C I) = theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
        (resSetClass canonicalInterpret_isCanonical D hD)) := by
  rw [classOn_eq C I hI hs]
  obtain ⟨D, hD, hmem, heq⟩ := ambient_chart_class P.hc P.e (base P) P.hB
    (fun _ h => absurd h (Set.notMem_empty _)) (Section3RESChartCuts.restrict C I hI hs)
  exact ⟨D, hD, hmem, heq⟩

/-! ### The chart of a measured RV object -/

section ChartU

open DiamondIntegral.Section7.ChartOfMeasured

variable {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := P.N) (P.G.real : Set P.N) n)

theorem e_tag (x : Fin n → CanonicalRV.RVSort Carrier) :
    (fun i => P.e (x i).val) = rvValues (eRVs P (fun j => taggedRVEquiv (x j))) := by
  funext i
  change P.e (x i).val = P.e (Sum.inr (rvPart (x i).val))
  rw [rvSort_tag]

/-- **Concrete points of the chart of `U`.** -/
theorem chart_point {x : Fin U.object.arity → CanonicalRV.RVSort Carrier}
    (hx : (fun i => P.e (x i).val) ∈ (chartOf P.hc U).domain) :
    ∃ ht : eRVs P (fun j => taggedRVEquiv (x j)) ∈ U.object.domain.carrier,
      (chartOf P.hc U).coordinate (fun i => P.e (x i).val) = rvValues (eRVs P (fcv P U _ ht)) ∧
      (chartOf P.hc U).volume (fun i => P.e (x i).val) = DiamondIntegral.Section6.gammaMapValue U.form ⟨_, ht⟩ := by
  rw [e_tag] at hx ⊢
  obtain ⟨u, hu, hue⟩ := hx
  have hut : u = eRVs P (fun j => taggedRVEquiv (x j)) := rvValues_injective hue
  subst hut
  refine ⟨hu, ?_, ?_⟩
  · change rawCoord U (rvValues (eRVs P (fun j => taggedRVEquiv (x j)))) = _
    rw [rawCoord_of U ⟨_, hu⟩, fcv_spec]
  · change rawVol U (rvValues (eRVs P (fun j => taggedRVEquiv (x j)))) = _
    rw [rawVol_of U ⟨_, hu⟩]

/-- Lattice labels are rational. -/
theorem label_rational_of_lattice (m : ℕ+) {r : CanonicalRV.RVSort Carrier}
    (hl : InLattice π m (codeValue (P.e r.val))) : LabelRational m (taggedRVEquiv r) := by
  have hrv : iRV (P.e r.val) := by
    have h := P.e.map_rel Rel.memRV ![r.val]
    have ht : (P.e ∘ (![r.val] : Fin 1 → Carrier)) = ![P.e r.val] := by funext i; fin_cases i; rfl
    rw [ht] at h
    exact h.mpr r.property
  have hfix := fixed_of_lattice P m hrv hl
  rw [← rvSort_tag r, PuiseuxOriginal.carrierAction_inr] at hfix
  exact (labelFixed_iff m _).mp (Sum.inr_injective hfix)

theorem fcv_ne_none (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier) (i : Fin n) :
    fcv P U t ht i ≠ none := by
  intro h
  have h1 := U.nonzero ⟨eRVs P t, ht⟩ i
  rw [fcv_spec] at h1
  apply h1
  change P.e (Sum.inr (fcv P U t ht i)) = iRVZero
  rw [h, ← e_iRVZero]
  rfl

/-- The value of a concrete RV element (`0` at `rv 0`). -/
def rvq : RV → ℚ
  | some u => Multiplicative.toAdd u.1
  | none => 0

theorem qpow_sum {ι : Type*} (s : Finset ι) (q : ι → ℚ) :
    qpow π (∑ i ∈ s, q i) = ∏ i ∈ s, qpow π (q i) := by
  apply ι_injective
  rw [ι_prod, ι_qpow, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => (ι_qpow _ _).symm

theorem ratValue_qpow (q : ℚ) : ratValue π (qpow π q) = q := by
  rw [ratValue_eq (one_lt_uniformizerValue P) q.den_ne_zero (z := q.num) (qpow_pow_den π q)]
  exact Rat.num_div_den q

theorem codeValue_fcv (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier) (i : Fin n) :
    codeValue (P.e (Sum.inr (fcv P U t ht i))) = qpow π (rvq (fcv P U t ht i)) := by
  rcases h : fcv P U t ht i with _ | u
  · exact absurd h (fcv_ne_none P U t ht i)
  · exact Galois.codeValue_rv_some P u

/-- The weight of a concrete point of the chart of `U` (with the form `1`). -/
theorem chart_weight (hform : ∀ u, DiamondIntegral.Section6.gammaMapValue U.form u = 1)
    {x : Fin U.object.arity → CanonicalRV.RVSort Carrier}
    (hx : (fun i => P.e (x i).val) ∈ (chartOf P.hc U).domain) :
    ∃ ht : eRVs P (fun j => taggedRVEquiv (x j)) ∈ U.object.domain.carrier,
      (chartOf P.hc U).correctedWeight (fun i => P.e (x i).val) =
        qpow π (∑ i, rvq (fcv P U _ ht i)) ∧
      ∀ i, codeValue ((chartOf P.hc U).coordinate (fun i => P.e (x i).val) i) =
        qpow π (rvq (fcv P U _ ht i)) := by
  obtain ⟨ht, hc, hv⟩ := chart_point P U hx
  have hci : ∀ i, codeValue ((chartOf P.hc U).coordinate (fun i => P.e (x i).val) i) =
      qpow π (rvq (fcv P U _ ht i)) := by
    intro i
    rw [hc]
    exact codeValue_fcv P U _ ht i
  refine ⟨ht, ?_, hci⟩
  unfold Chart.correctedWeight
  rw [hv, hform, one_mul, qpow_sum]
  exact Finset.prod_congr rfl fun i _ => hci i

theorem etaTerm_add {R : Type*} [CommRing R] (L : Rˣ) (q : ℚ) (x y : R) :
    etaTerm L q (x + y) = etaTerm L q x + etaTerm L q y := by
  unfold etaTerm
  split_ifs <;> ring

theorem etaTerm_sum {R : Type*} [CommRing R] {ι : Type*} (L : Rˣ) (q : ℚ) (s : Finset ι) (f : ι → R) :
    etaTerm L q (∑ i ∈ s, f i) = ∑ i ∈ s, etaTerm L q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold etaTerm; split_ifs <;> simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, etaTerm_add, ih]

theorem etaTerm_int {R : Type*} [CommRing R] (L : Rˣ) (z : ℤ) (x : R) :
    etaTerm L (z : ℚ) x = x * ((L ^ z : Rˣ) : R) := by
  unfold etaTerm
  have h : ∃ z' : ℤ, (z' : ℚ) = z := ⟨z, rfl⟩
  rw [dif_pos h]
  have hz : h.choose = z := by exact_mod_cast h.choose_spec
  rw [hz]

theorem etaTerm_zero' {R : Type*} [CommRing R] (L : Rˣ) (q : ℚ) : etaTerm L q (0 : R) = 0 := by
  unfold etaTerm
  split_ifs <;> simp

theorem biUnion_definable' {K : ℕ} {ι : Type*} (T : Finset ι) (S : ι → Set (Fin K → P.N))
    (hS : ∀ i ∈ T, DefinableOverBase (base P) (fun _ : Fin K => .rv) (S i)) :
    DefinableOverBase (base P) (fun _ : Fin K => .rv) (⋃ i ∈ T, S i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using (BlowupChart.rv_universe_definable (base P) K).compl
  | insert j T hj ih =>
    rw [Finset.set_biUnion_insert]
    exact (hS j (Finset.mem_insert_self j T)).union (ih fun i hi => hS i (Finset.mem_insert_of_mem hi))

theorem qpow_injective {a c : ℚ} (h : qpow π a = qpow π c) : a = c :=
  le_antisymm ((Hm.qpow_le_iff P).mp h.le) ((Hm.qpow_le_iff P).mp h.ge)

/-- **`η h_m [U]` as a sum of concrete classes.** -/
theorem zetaCoeff_U (hU : U.doublyBounded)
    (hform : ∀ u, DiamondIntegral.Section6.gammaMapValue U.form u = 1) (m : ℕ+) (Z : Finset (Fin n → ℤ))
    (hZ : ∀ (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier),
      (∀ j, LabelRational m (t j)) → ∃ z ∈ Z, ∀ i, rvq (fcv P U t ht i) = (z i : ℚ) / (m : ℕ)) :
    ∃ (D : Γ → (Fin n → ℤ) → DefSet (rawRVSpace (M := Carrier) U.object.arity) {c | baseCarrier c})
      (hD : ∀ w z, (Set.range (fun u : D w z => fun i => Values.vrv (u.val i))).Finite),
      (∀ w z x, x ∈ (D w z).carrier ↔ (fun i => P.e (x i).val) ∈ latticeFibre P (chartOf P.hc U) m w ∧
        ∀ i, codeValue ((chartOf P.hc U).coordinate (fun i => P.e (x i).val) i) = qpow π ((z i : ℚ) / (m : ℕ))) ∧
      zetaCoeff P (RVBoundedRing.objectClass (objOf P.hc P.G.real U hU)) m =
        ∑ w ∈ weights P (chartOf P.hc U) (chartOf_bounded P.hc U hU) m, ∑ z ∈ Z,
          algebraMap _ Rloc (theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
            (resSetClass canonicalInterpret_isCanonical (D w z) (hD w z)))) *
            ((Lunit ^ (-(∑ i, z i)) : Rlocˣ) : Rloc) := by
  let a := chartOf P.hc U
  let ha := chartOf_bounded P.hc U hU
  let I : Γ → (Fin n → ℤ) → Set (Fin a.arity → P.N) := fun w z =>
    {u | u ∈ latticeFibre P a m w ∧ ∀ i ∈ Finset.univ, codeValue (a.coordinate u i) = qpow π ((z i : ℚ) / (m : ℕ))}
  have hIdef : ∀ w z, DefinableOverBase (base P) (fun _ : Fin a.arity => .rv) (I w z) := fun w z =>
    coord_values_definable P a (latticeFibre_definable' P a ha m w) (fun u hu => hu.1.1) _
      (fun i => qpow_definable P _) Finset.univ
  have hIs : ∀ w z, I w z ⊆ (fibreChart P a ha m w).domain := fun w z u hu => hu.1
  have hex : ∀ w z, ∃ (D : DefSet (rawRVSpace (M := Carrier) (fibreChart P a ha m w).arity) {c | baseCarrier c})
      (hD : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite),
      (∀ x, x ∈ D.carrier ↔ (fun i => P.e (x i).val) ∈ I w z) ∧
      theta P (classOn (fibreChart P a ha m w) (I w z)) = theta_5_14_concrete
        (RESDimensionFreeReduction.quotient originalPuiseuxGround (resSetClass canonicalInterpret_isCanonical D hD)) :=
    fun w z => theta_classOn P (fibreChart P a ha m w) (I w z) (hIdef w z) (hIs w z)
  choose D hD hDmem hDθ using hex
  refine ⟨D, hD, fun w z x => ?_, ?_⟩
  · rw [hDmem]
    simp only [I, Finset.mem_univ, true_implies]
    rfl
  rw [zetaCoeff_chart P (objOf P.hc P.G.real U hU) m]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hI'def := biUnion_definable' P Z (I w) (fun z _ => hIdef w z)
  have hI's : (⋃ z ∈ Z, I w z) ⊆ (fibreChart P a ha m w).domain := Set.iUnion₂_subset fun z _ => hIs w z
  have hdisj : (Z : Set (Fin n → ℤ)).PairwiseDisjoint (I w) := by
    intro z _ z' _ hzz'
    refine Set.disjoint_left.mpr fun u hu hu' => hzz' ?_
    funext i
    have h1 := hu.2 i (Finset.mem_univ i)
    have h2 := hu'.2 i (Finset.mem_univ i)
    have h3 := qpow_injective P (h1.symm.trans h2)
    have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
    field_simp at h3
    exact_mod_cast h3
  have hcut := nativeRESChartClass_cut (fibreChart P a ha m w) _ hI'def hI's
  rw [fibreChart_domain] at hI's
  obtain ⟨DR, hDR, hDRmem, hDRθ⟩ := ambient_chart_class P.hc P.e (base P) P.hB
    (fun _ h => absurd h (Set.notMem_empty _)) (Section3RESChartCuts.outside (fibreChart P a ha m w) _ hI'def)
  have hDRempty : DR.carrier = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    rw [hDRmem] at hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨ht, -, hci⟩ := chart_weight P U hform hxF.1.1
    have hrat : ∀ j, LabelRational m (taggedRVEquiv (x j)) := fun j =>
      label_rational_of_lattice P m (hxF.1.2 j)
    obtain ⟨z, hz, hzv⟩ := hZ _ ht hrat
    apply hxI
    refine Set.mem_biUnion hz ⟨hxF, fun i _ => ?_⟩
    exact (hci i).trans (congrArg (qpow π) (hzv i))
  have hout : theta P (nativeRESChartClass (Section3RESChartCuts.outside (fibreChart P a ha m w) _ hI'def)) = 0 := by
    change ambientPuiseuxComparison P.hc P.e (base P) P.hB _ _ = 0
    rw [hDRθ, resSetClass_empty _ _ _ hDRempty, map_zero, map_zero]
  have hθ : theta P (nativeRESChartClass (fibreChart P a ha m w)) =
      ∑ z ∈ Z, theta P (classOn (fibreChart P a ha m w) (I w z)) := by
    have hb := classOn_biUnion (fibreChart P a ha m w) Z
      (fun z => (I w z : Set (Fin (fibreChart P a ha m w).arity → P.N))) (fun z _ => hIdef w z)
      (fun z _ => hIs w z) hdisj
    rw [← hcut, ← classOn_eq _ _ hI'def (Set.iUnion₂_subset fun z _ => hIs w z),
      show classOn (fibreChart P a ha m w) (⋃ i ∈ Z, I w i) =
        ∑ z ∈ Z, classOn (fibreChart P a ha m w) (I w z) from hb, map_add, hout, add_zero, map_sum]
  change etaTerm Lunit (-((m : ℕ) : ℚ) * ratValue π w)
    (algebraMap _ Rloc (theta P (nativeRESChartClass (fibreChart P a ha m w)))) = _
  rw [hθ, map_sum, etaTerm_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [hDθ w z]
  by_cases hne : (D w z).carrier.Nonempty
  · obtain ⟨x, hx⟩ := hne
    rw [hDmem] at hx
    obtain ⟨ht, hwt, hci⟩ := chart_weight P U hform hx.1.1.1
    have hzi : ∀ i, rvq (fcv P U _ ht i) = (z i : ℚ) / (m : ℕ) := fun i =>
      qpow_injective P ((hci i).symm.trans (hx.2 i (Finset.mem_univ i)))
    have hw' : w = qpow π (((∑ i, z i : ℤ) : ℚ) / (m : ℕ)) := by
      have h1 : w = (chartOf P.hc U).correctedWeight (fun i => P.e (x i).val) := hx.1.2.symm
      rw [h1, hwt]
      congr 1
      rw [Finset.sum_congr rfl fun i _ => hzi i, ← Finset.sum_div]
      push_cast
      rfl
    rw [hw', ratValue_qpow]
    have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
    have he : -((m : ℕ) : ℚ) * (((∑ i, z i : ℤ) : ℚ) / (m : ℕ)) = ((-(∑ i, z i) : ℤ) : ℚ) := by
      field_simp
      push_cast
      ring
    rw [he, etaTerm_int]
  · have hempty : (D w z).carrier = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [resSetClass_empty _ _ _ hempty, map_zero, map_zero, map_zero, zero_mul, etaTerm_zero']

end ChartU

end DiamondIntegral.Section8.Truncation
