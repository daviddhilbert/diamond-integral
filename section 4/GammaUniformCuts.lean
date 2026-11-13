import «section 4».GammaFormulaLogic
import «section 4».GammaFamilySlices
import «section 4».GammaDefinableEuler
import Section3.NormalizationSaturation

/-! Uniform finite cut bounds for unary fibres of actual Gamma relations.
The cut-bound condition is first order over the original base. Saturation
and smallness will be used explicitly to pass from pointwise bounds to a
single bound for the family. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUniformCuts
open GammaFormulaLogic GammaOrderLogic

def Controls {α : Type} [LT α] {N : ℕ} (a : Fin N → α) (D : Set α) : Prop :=
  ∀ x x', (∀ i, (x < a i ↔ x' < a i) ∧ (a i < x ↔ a i < x')) → (x ∈ D ↔ x' ∈ D)

def controlsFormula (N n : ℕ) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (N + n) :=
  let π : Fin (n + 1) → Fin (N + n + 2) := Fin.cases 0 (fun j => (Fin.natAdd N j).succ.succ)
  let π' : Fin (n + 1) → Fin (N + n + 2) := Fin.cases 1 (fun j => (Fin.natAdd N j).succ.succ)
  let lt (i j : Fin (N + n + 2)) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (N + n + 2) :=
    .lt i j
  let atom (π : Fin (n + 1) → Fin (N + n + 2)) :
      GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (N + n + 2) := .pred () π
  let cut (i : Fin N) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (N + n + 2) :=
    let j := (Fin.castAdd n i).succ.succ
    .and ((lt 0 j).iff (lt 1 j)) ((lt j 0).iff (lt j 1))
  ((GammaFormulaLogic.Formula.allOf (List.ofFn cut)).imp ((atom π).iff (atom π'))).all.all

theorem controlsFormula_realize {α : Type} [LT α] (N n : ℕ)
    (R : Set (Fin (n + 1) → α)) (z : Fin (N + n) → α) :
    (controlsFormula N n).Realize (fun _ => R) z ↔
      Controls (fun i => z (Fin.castAdd n i))
        {x | Fin.cons x (fun j => z (Fin.natAdd N j)) ∈ R} := by
  simp only [controlsFormula, GammaFormulaLogic.Formula.all_realize,
    GammaFormulaLogic.Formula.imp_realize, GammaFormulaLogic.Formula.iff_realize,
    GammaFormulaLogic.Formula.allOf_realize, List.forall_mem_ofFn_iff,
    GammaFormulaLogic.Formula.Realize, Fin.cons_zero, Fin.cons_succ]
  change (∀ x' x, (∀ i, (x < z (Fin.castAdd n i) ↔ x' < z (Fin.castAdd n i)) ∧
      (z (Fin.castAdd n i) < x ↔ z (Fin.castAdd n i) < x')) →
    ((Fin.cons x (Fin.cons x' z) ∘ Fin.cases 0 (fun j => (Fin.natAdd N j).succ.succ)) ∈ R ↔
      (Fin.cons x (Fin.cons x' z) ∘ Fin.cases 1 (fun j => (Fin.natAdd N j).succ.succ)) ∈ R)) ↔ _
  have he (x x' : α) (j : Fin (n + 1)) :
      (Fin.cons x (Fin.cons x' z) ∘ Fin.cases 0 (fun j => (Fin.natAdd N j).succ.succ)) j =
        (Fin.cons x (fun j => z (Fin.natAdd N j)) : Fin (n + 1) → α) j := by
    exact Fin.cases rfl (fun _ => rfl) j
  have he' (x x' : α) (j : Fin (n + 1)) :
      (Fin.cons x (Fin.cons x' z) ∘ Fin.cases 1 (fun j => (Fin.natAdd N j).succ.succ)) j =
        (Fin.cons x' (fun j => z (Fin.natAdd N j)) : Fin (n + 1) → α) j := by
    exact Fin.cases rfl (fun _ => rfl) j
  simp_rw [funext (he _ _), funext (he' _ _)]
  exact forall_comm

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def CutBound {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (N : ℕ) :
    Set (Fin n → Values.Gamma (M := M)) :=
  {y | ∃ a : Fin N → Values.Gamma (M := M), Controls a {x | Fin.cons x y ∈ R}}

theorem cutBound_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ) :
    GammaDefinable B (CutBound R N) := by
  have h := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (controlsFormula N n)
  have hi := GammaQuantifierLogic.image_definable_base B _ h (Fin.natAdd N)
    (Fin.natAdd_injective n N)
  convert hi using 1
  ext y
  change (∃ a : Fin N → Values.Gamma (M := M), Controls a {x | Fin.cons x y ∈ R}) ↔
    ∃ z, ((controlsFormula N n).Realize (fun _ => R) z) ∧ z ∘ Fin.natAdd N = y
  simp_rw [controlsFormula_realize]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Fin.append a y, ?_, ?_⟩
    · simpa only [Fin.append_left, Fin.append_right] using ha
    · funext j
      exact Fin.append_right a y j
  · rintro ⟨z, hz, he⟩
    refine ⟨(fun i => z (Fin.castAdd n i)), ?_⟩
    change (fun j => z (Fin.natAdd N j)) = y at he
    simpa only [he] using hz

theorem exists_cutBound (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (y : Fin n → Values.Gamma (M := M)) : ∃ N, y ∈ CutBound R N := by
  have hD := GammaFamilySlices.slice_definable_base B R hR y
  obtain ⟨E, hE⟩ := gamma_definable_finite_thresholds h00 _ _ hD
  let e := (Finset.equivFin E).symm
  refine ⟨E.card, (fun i => (e i).val), ?_⟩
  intro x x' hxx
  apply hE x x'
  intro c hc
  have h := hxx (e.symm ⟨c, hc⟩)
  simpa only [Equiv.apply_symm_apply] using h

theorem cutBound_mono {n N K : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hNK : N ≤ K) :
    CutBound R N ⊆ CutBound R K := by
  rintro y ⟨a, ha⟩
  let a' : Fin K → Values.Gamma (M := M) :=
    fun i => if h : i.val < N then a ⟨i.val, h⟩ else 1
  refine ⟨a', ?_⟩
  intro x x' hxx
  apply ha x x'
  intro i
  have hi : i.val < K := lt_of_lt_of_le i.isLt hNK
  have h := hxx ⟨i.val, hi⟩
  simpa only [a', dite_eq_left i.isLt] using h

theorem uniform_cutBound (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    ∃ N, ∀ y : Fin n → Values.Gamma (M := M), y ∈ CutBound R N := by
  let S := commonRealNames B
  let U (N : ℕ) : Set (Fin n → M) :=
    {z | Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ CutBound R N}
  have hU (N : ℕ) : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
      (Fin n) (U N) :=
    GammaBaseExtension.to_common_real_syntax B _ (cutBound_definable_base B R hR N)
  have hcov : ∀ z ∈ {z : Fin n → M | Proper z}, ∃ c ∈ Set.range U, z ∈ c := by
    intro z hz
    obtain ⟨N, hN⟩ := exists_cutBound h00 B R hR (fun i => codeValue (M := M) (z i))
    exact ⟨U N, Set.mem_range_self N, hz, hN⟩
  have hc := @Saturated.definable_finite_subcover_tuple M (CanonicalStructure.normalize (M := M))
    κ hs.normalize S (commonRealNames_small hκ B hr hγ) n
    {z : Fin n → M | Proper z} (proper_normalized_definable S) (Set.range U)
    (by rintro _ ⟨N, rfl⟩; exact hU N) hcov
  obtain ⟨C, hC, hsub, hcover⟩ := hc
  let _ := hC.fintype
  have hindex (c : C) : ∃ N, U N = c.val := hsub c.property
  let index (c : C) := Classical.choose (hindex c)
  have hindex_eq (c : C) : U (index c) = c.val := Classical.choose_spec (hindex c)
  refine ⟨∑ c : C, index c, ?_⟩
  intro y
  choose z hz hzy using fun i => EndpointLogic.codeValue_surjective (y i)
  obtain ⟨c, hc, hzc⟩ := hcover z hz
  let c' : C := ⟨c, hc⟩
  have hzU : z ∈ U (index c') := by rw [hindex_eq]; exact hzc
  have hy : y ∈ CutBound R (index c') := by
    convert hzU.2 using 1
    exact (funext hzy).symm
  exact cutBound_mono R
    (Finset.single_le_sum (fun c _ => Nat.zero_le (index c)) (Finset.mem_univ c')) hy

end DiamondIntegral.Section4.GammaUniformCuts
