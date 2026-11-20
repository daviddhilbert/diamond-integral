import «section 7».Lemma714Descent
import «section 6».RVIndexedRowBounds

/-! Lemma 7.14, part 18: uniform bounds on doubly bounded key sets.

Step 3 of the proof names the aperture bounds after descent (Remark 7.4 in
the paper). Here: on a key set inside a definable, doubly bounded set of
nonzero RV tuples, the rows of every chart schema valid at all keys and the
apertures of every datum schema valid at all keys are uniformly bounded
(`allBounds`). The proof applies Lemma 2.41 for RV-indexed Γ-families (Section 6
`rv_indexed_bounded_gamma_rows_bounded`) to the Γ-family of the values of
the row coordinates, resp. of the apertures; pointwise boundedness is part of
validity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6
open DiamondIntegral.Section2 DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {q : ℕ}

/-! ### Γ-family graphs over keys -/

section Graphs

include hc in
/-- A Γ-family graph given in the layout `(x, c)`, definable over the base, is
definable in the raw layout of Lemma 2.41. -/
theorem rawGraph_of_append (D : Set (Fin q → M)) (P : (Fin q → M) → Set (Values.Gamma (M := M)))
    (G : Set (Fin (q + 1) → M)) (hG : DefinableOverBase (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs (q + 1)) G)
    (hGeq : ∀ w, w ∈ G ↔ (w ∘ Fin.castAdd 1 ∈ D ∧ NonzeroRV (w (Fin.natAdd q 0)) ∧
      codeValue (w (Fin.natAdd q 0)) ∈ P (w ∘ Fin.castAdd 1))) :
    (T : Set M).Definable LRV (rawGammaFamilyGraph D P) := by
  have hraw := ((real_base_iff hc).mp hG).1
  convert hraw.preimage_comp (finSumFinEquiv.symm : Fin (q + 1) → Fin q ⊕ Fin 1) using 1
  ext z
  simp only [rawGammaFamilyGraph, Set.mem_setOf_eq, Set.mem_preimage, hGeq]
  have h1 : (z ∘ (finSumFinEquiv.symm : Fin (q + 1) → Fin q ⊕ Fin 1)) ∘ Fin.castAdd 1 = z ∘ Sum.inl := by
    funext i
    simp [finSumFinEquiv_symm_apply_castAdd]
  have h2 : (z ∘ (finSumFinEquiv.symm : Fin (q + 1) → Fin q ⊕ Fin 1)) (Fin.natAdd q 0) = z (Sum.inr 0) := by
    simp [finSumFinEquiv_symm_apply_natAdd]
  rw [h1, h2]

variable (Q : KeySet (⟨(T : Set M), ∅⟩ : Base (M := M)) q)

/-- The values of the nonzero row coordinates of a chart schema at `x`. -/
def rowValues {d : ℕ} (W : ChartSchema (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs q) d) (x : Fin q → M) :
    Set (Values.Gamma (M := M)) :=
  {γ | ∃ u ∈ W.row x, ∃ i, NonzeroRV (u i) ∧ codeValue (u i) = γ}

/-- The values of the apertures of a datum schema at `x`. -/
def apValues {k : ℕ} (D : DatumSchema (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs q) k) (x : Fin q → M) :
    Set (Values.Gamma (M := M)) :=
  {γ | ∃ u t, D.apRow x u t ∧ NonzeroRV t ∧ codeValue t = γ}

/-- The equality-of-values set on pairs of codes. -/
abbrev eqSet : Set (Fin 2 → M) := {z | Proper z ∧ codeValue (z 0) = codeValue (z 1)}

theorem rowGraph_definable {d : ℕ} (W : ChartSchema (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs q) d) :
    DefinableOverBase (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs (q + 1))
      {w | w ∘ Fin.castAdd 1 ∈ Q.carrier ∧ NonzeroRV (w (Fin.natAdd q 0)) ∧
        codeValue (w (Fin.natAdd q 0)) ∈ rowValues W (w ∘ Fin.castAdd 1)} := by
  let a := W.arity
  let st := Fin.append (Fin.append (rvs q) (rvs 1)) (rvs a)
  let ιXU : Fin (q + a) → Fin ((q + 1) + a) :=
    Fin.append (fun i => Fin.castAdd a (Fin.castAdd 1 i)) (fun j => Fin.natAdd (q + 1) j)
  let ιX : Fin q → Fin ((q + 1) + a) := fun i => Fin.castAdd a (Fin.castAdd 1 i)
  let Z : Set (Fin ((q + 1) + a) → M) :=
    {v | v ∘ ιXU ∈ W.domain ∧ v ∈ sortedUniverse st} ∩
      ({v | v ∘ ιX ∈ Q.carrier ∧ v ∈ sortedUniverse st} ∩
        ⋃ i ∈ (Finset.univ : Finset (Fin a)),
          {v | v ∘ ![Fin.natAdd (q + 1) i, Fin.castAdd a (Fin.natAdd q 0)] ∈ eqSet ∧ v ∈ sortedUniverse st})
  have hZ : DefinableOverBase (⟨(T : Set M), ∅⟩ : Base (M := M)) st Z := by
    refine (W.domain_definable.preimage_real st ιXU).inter ((Q.definable.preimage_real st ιX).inter ?_)
    exact DefinableOverBase.finite_iUnion Finset.univ _
      (fun i _ => (VariableApertureMeasuredComparison.value_equality_definable _).preimage_real st _)
  have hR := gamma_family_row_exists_definable (Fin.append (rvs q) (rvs 1)) (rvs a) hZ
  rw [rvs_append] at hR
  convert hR using 1
  ext w
  have hA (u : Fin a → M) : Fin.append w u ∘ ιXU = Fin.append (w ∘ Fin.castAdd 1) u := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ιXU]
  have hB (u : Fin a → M) : Fin.append w u ∘ ιX = w ∘ Fin.castAdd 1 := by
    funext i
    simp [ιX]
  have hC (u : Fin a → M) (i : Fin a) :
      Fin.append w u ∘ ![Fin.natAdd (q + 1) i, Fin.castAdd a (Fin.natAdd q 0)] = ![u i, w (Fin.natAdd q 0)] := by
    funext j
    fin_cases j <;> simp
  constructor
  · rintro ⟨hk, hc0, u, hu, i, hi, he⟩
    have hsw : ∀ j, sortEval (rvs (q + 1) j) (w j) := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · have := Q.definable.proper _ hk l
        simpa using this
      · fin_cases l
        exact hc0.1
    have hsu : ∀ j, sortEval (rvs a j) (u j) := by
      intro j
      have := W.domain_definable.proper _ hu (Fin.natAdd q j)
      simpa using this
    have hs : Fin.append w u ∈ sortedUniverse st := by
      have := sorted_append (sa := rvs (q + 1)) (sb := rvs a) hsw hsu
      rwa [← rvs_append] at this
    refine ⟨u, ⟨⟨by rw [hA]; exact hu, hs⟩, ⟨by rw [hB]; exact hk, hs⟩, Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, ?_, hs⟩⟩⟩
    rw [hC]
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · exact hi
      · exact hc0
    · simpa using he
  · rintro ⟨u, ⟨hu, hs⟩, ⟨hk, -⟩, hU⟩
    obtain ⟨i, -, he, -⟩ := Set.mem_iUnion₂.mp hU
    rw [hA] at hu
    rw [hB] at hk
    rw [hC] at he
    refine ⟨hk, he.1 1, u, hu, i, he.1 0, ?_⟩
    simpa using he.2

theorem apGraph_definable {k : ℕ} (D : DatumSchema (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs q) k) :
    DefinableOverBase (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs (q + 1))
      {w | w ∘ Fin.castAdd 1 ∈ Q.carrier ∧ NonzeroRV (w (Fin.natAdd q 0)) ∧
        codeValue (w (Fin.natAdd q 0)) ∈ apValues D (w ∘ Fin.castAdd 1)} := by
  let a := D.chart.arity
  let st := Fin.append (Fin.append (rvs q) (rvs 1)) (rvs (a + 1))
  let ιA : Fin ((q + a) + 1) → Fin ((q + 1) + (a + 1)) :=
    Fin.append (Fin.append (fun i => Fin.castAdd (a + 1) (Fin.castAdd 1 i))
      (fun j => Fin.natAdd (q + 1) (Fin.castAdd 1 j))) (fun _ => Fin.natAdd (q + 1) (Fin.natAdd a 0))
  let ιX : Fin q → Fin ((q + 1) + (a + 1)) := fun i => Fin.castAdd (a + 1) (Fin.castAdd 1 i)
  let Z : Set (Fin ((q + 1) + (a + 1)) → M) :=
    {v | v ∘ ιA ∈ D.aperture ∧ v ∈ sortedUniverse st} ∩
      ({v | v ∘ ιX ∈ Q.carrier ∧ v ∈ sortedUniverse st} ∩
        {v | v ∘ ![Fin.natAdd (q + 1) (Fin.natAdd a 0), Fin.castAdd (a + 1) (Fin.natAdd q 0)] ∈ eqSet ∧
          v ∈ sortedUniverse st})
  have hZ : DefinableOverBase (⟨(T : Set M), ∅⟩ : Base (M := M)) st Z :=
    (D.aperture_definable.preimage_real st ιA).inter ((Q.definable.preimage_real st ιX).inter
      ((VariableApertureMeasuredComparison.value_equality_definable _).preimage_real st _))
  have hR := gamma_family_row_exists_definable (Fin.append (rvs q) (rvs 1)) (rvs (a + 1)) hZ
  rw [rvs_append] at hR
  convert hR using 1
  ext w
  have hA (u : Fin a → M) (t : M) :
      Fin.append w (Fin.append u (fun _ : Fin 1 => t)) ∘ ιA =
        Fin.append (Fin.append (w ∘ Fin.castAdd 1) u) (fun _ : Fin 1 => t) := by
    funext j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [ιA]
    · simp [ιA]
  have hB (v : Fin (a + 1) → M) : Fin.append w v ∘ ιX = w ∘ Fin.castAdd 1 := by
    funext i
    simp [ιX]
  have hC (u : Fin a → M) (t : M) :
      Fin.append w (Fin.append u (fun _ : Fin 1 => t)) ∘
        ![Fin.natAdd (q + 1) (Fin.natAdd a 0), Fin.castAdd (a + 1) (Fin.natAdd q 0)] = ![t, w (Fin.natAdd q 0)] := by
    funext j
    fin_cases j <;> simp
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hk, hc0, u, t, hap, ht, he⟩
    have hsw : ∀ j, sortEval (rvs (q + 1) j) (w j) := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · have := Q.definable.proper _ hk l
        simpa using this
      · fin_cases l
        exact hc0.1
    have hsv : ∀ j, sortEval (rvs (a + 1) j) (Fin.append u (fun _ : Fin 1 => t) j) := by
      intro j
      have := D.aperture_definable.proper _ hap
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · have h' := this (Fin.castAdd 1 (Fin.natAdd q l))
        simpa using h'
      · have h' := this (Fin.natAdd (q + D.chart.arity) l)
        rw [Fin.append_right, Fin.append_right] at h'
        have e : Fin.append u (fun _ : Fin 1 => t) (Fin.natAdd D.chart.arity l) = t := Fin.append_right _ _ _
        show sortEval SortTag.rv (Fin.append u (fun _ : Fin 1 => t) (Fin.natAdd D.chart.arity l))
        rw [e]
        exact h'
    have hs : Fin.append w (Fin.append u (fun _ : Fin 1 => t)) ∈ sortedUniverse st := by
      have := sorted_append (sa := rvs (q + 1)) (sb := rvs (a + 1)) hsw hsv
      rwa [← rvs_append] at this
    refine ⟨Fin.append u (fun _ : Fin 1 => t), ⟨by rw [hA]; exact hap, hs⟩, ⟨by rw [hB]; exact hk, hs⟩, ?_, hs⟩
    rw [hC]
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · exact ht
      · exact hc0
    · simpa using he
  · rintro ⟨v, ⟨hv, hs⟩, ⟨hk, -⟩, he, -⟩
    rw [Lemma714Schema.DatumSchema.append_decomp_one v] at hv he
    rw [hA] at hv
    rw [hB] at hk
    rw [hC] at he
    refine ⟨hk, he.1 1, _, _, hv, he.1 0, ?_⟩
    simpa using he.2

end Graphs

/-! ### Uniform bounds -/

section Main
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include hc h00 hκ hs hsmall hΓ in
/-- **Uniform bounds on a doubly bounded key set** (Lemma 2.41 / Remark 7.4).
Every key set inside a definable key set of nonzero, doubly bounded RV tuples
has uniformly bounded keys, rows and apertures. -/
theorem allBounds (Q : KeySet (⟨(T : Set M), ∅⟩ : Base (M := M)) q)
    (hNZ : ∀ x ∈ Q.carrier, ∀ i, NonzeroRV (x i)) (hDB : RVCodeDoublyBounded Q.carrier) : Q.AllBounds := by
  intro Q' hQ'
  have hD : (T : Set M).Definable LRV Q'.carrier := ((real_base_iff hc).mp Q'.definable).1
  have hNZ' : ∀ x ∈ Q'.carrier, ∀ i, NonzeroRV (x i) := fun x hx => hNZ x (hQ' hx)
  have hDB' : RVCodeDoublyBounded Q'.carrier := by
    obtain ⟨β, h⟩ := hDB
    exact ⟨β, fun x hx => h x (hQ' hx)⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨β, hβ⟩ := hDB'
    exact ⟨β, fun x hx i _ => hβ x hx i⟩
  · intro d W hW
    have hraw := rawGraph_of_append hc Q'.carrier (rowValues W) _ (rowGraph_definable Q' W) (fun w => Iff.rfl)
    obtain ⟨γ, hγ⟩ := DiamondIntegral.Section6.rv_indexed_bounded_gamma_rows_bounded hc h00
      DiamondIntegral.Section7.LiftClasses.lin hκ.le hs hsmall hΓ Q'.carrier hD hNZ' hDB'
      (fun x => insert 1 (rowValues W x))
      (DiamondIntegral.Section6.gammaRows_with_unit_definable hc Q'.carrier hD _ hraw)
      (fun x _ => ⟨1, Set.mem_insert _ _⟩) (fun x hx => by
        obtain ⟨lo, hi, hb⟩ := (hW x hx).bounded
        refine ⟨max (max hi lo⁻¹) 1, fun a ha => ?_⟩
        have h1 : (1 : Values.Gamma (M := M)) ≤ max (max hi lo⁻¹) 1 := le_max_right _ _
        rcases ha with rfl | ⟨u, hu, i, hi0, rfl⟩
        · exact ⟨inv_le_one'.mpr h1, h1⟩
        · obtain ⟨hl, hh⟩ := hb u hu i hi0
          refine ⟨?_, hh.trans ((le_max_left _ _).trans (le_max_left _ _))⟩
          have h2 : lo⁻¹ ≤ max (max hi lo⁻¹) 1 := (le_max_right _ _).trans (le_max_left _ _)
          exact (inv_le'.mp h2).trans hl)
    exact ⟨γ, fun x hx u hu i hi => hγ x hx _ (Set.mem_insert_of_mem _ ⟨u, hu, i, hi, rfl⟩)⟩
  · intro k D hD'
    have hraw := rawGraph_of_append hc Q'.carrier (apValues D) _ (apGraph_definable Q' D) (fun w => Iff.rfl)
    obtain ⟨γ, hγ⟩ := DiamondIntegral.Section6.rv_indexed_bounded_gamma_rows_bounded hc h00
      DiamondIntegral.Section7.LiftClasses.lin hκ.le hs hsmall hΓ Q'.carrier hD hNZ' hDB'
      (fun x => insert 1 (apValues D x))
      (DiamondIntegral.Section6.gammaRows_with_unit_definable hc Q'.carrier hD _ hraw)
      (fun x _ => ⟨1, Set.mem_insert _ _⟩) (fun x hx => by
        obtain ⟨Δ, hΔ⟩ := (hD' x hx).ap_bounded
        refine ⟨max Δ 1, fun a ha => ?_⟩
        have h1 : (1 : Values.Gamma (M := M)) ≤ max Δ 1 := le_max_right _ _
        rcases ha with rfl | ⟨u, t, hap, -, rfl⟩
        · exact ⟨inv_le_one'.mpr h1, h1⟩
        · exact ⟨(inv_le_one'.mpr h1).trans ((hD' x hx).ap_value u t hap).2,
            (hΔ u t hap).trans (le_max_left _ _)⟩)
    exact ⟨γ, fun x hx u t hap => (hγ x hx _ (Set.mem_insert_of_mem _
      ⟨u, t, hap, ((hD' x hx).ap_value u t hap).1, rfl⟩)).2⟩

end Main

end DiamondIntegral.Section7.Lemma714Schema
