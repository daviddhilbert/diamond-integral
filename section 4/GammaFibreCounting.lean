import «section 4».GammaQuantifierLogic
import «section 4».EulerFiniteSets
import «section 4».GammaDefinableFunctions

/-! First-order bounded counting in actual Gamma fibres. Witnesses are
distinct Gamma values, rather than distinct RV representatives. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFibreCounting
open GammaOrderLogic GammaRelationLogic GammaQuantifierLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem univ_definable_base (B : Base (M := M)) (n : ℕ) :
    GammaDefinable B (Set.univ : Set (Fin n → Values.Gamma (M := M))) := by
  simpa only [GammaDefinable, Set.mem_univ, and_true] using proper_definable_base B n

theorem ne_definable_base (B : Base (M := M)) {n : ℕ} (i j : Fin n) :
    GammaDefinable B {z : Fin n → Values.Gamma (M := M) | z i ≠ z j} := by
  let φ : Formula Unit n := .not (.and (.not (.lt i j)) (.not (.lt j i)))
  have h := formula_definable_base B (fun _ : Unit => Set.univ)
    (fun _ => (unary_definable_iff B Set.univ).mp (univ_definable_base B 1)) φ
  convert h using 1
  ext z
  change (z i ≠ z j) ↔ ¬ (¬ z i < z j ∧ ¬ z j < z i)
  simp only [not_and_or, not_not]
  exact ⟨lt_or_gt_of_ne, fun h => h.elim ne_of_lt ne_of_gt⟩

def AtLeast (R : Set (Fin 2 → Values.Gamma (M := M))) (N : ℕ)
    (y : Values.Gamma (M := M)) : Prop :=
  ∃ u : Fin N → Values.Gamma (M := M), Function.Injective u ∧ ∀ i, ![u i, y] ∈ R

theorem atLeast_definable_base (B : Base (M := M))
    (R : Set (Fin 2 → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ) :
    GammaDefinableOverBase B {y | AtLeast R N y} := by
  let A : Set (Fin (N + 1) → Values.Gamma (M := M)) :=
    {z | ∀ i : Fin N, ![z i.succ, z 0] ∈ R}
  have hA : GammaDefinable B A := by
    have h := finite_iInter_definable_base B
      (fun i : Fin N => {z : Fin (N + 1) → Values.Gamma (M := M) | ![z i.succ, z 0] ∈ R})
      (fun i => by
        have h := preimage_definable_base B R hR ![i.succ, 0]
        convert h using 1
        ext z
        have he : z ∘ ![i.succ, 0] = ![z i.succ, z 0] := by
          funext j
          fin_cases j <;> rfl
        change (![z i.succ, z 0] ∈ R) ↔ z ∘ ![i.succ, 0] ∈ R
        rw [he])
    simpa only [A, Set.iInter_ofPred] using h
  let J (i j : Fin N) : Set (Fin (N + 1) → Values.Gamma (M := M)) :=
    if i = j then Set.univ else {z | z i.succ ≠ z j.succ}
  have hJ (i j : Fin N) : GammaDefinable B (J i j) := by
    by_cases h : i = j
    · simpa only [J, ite_eq_left h] using univ_definable_base B (N + 1)
    · simpa only [J, ite_eq_right h] using ne_definable_base B i.succ j.succ
  have hI := finite_iInter_definable_base B (fun i => ⋂ j, J i j)
    (fun i => finite_iInter_definable_base B (J i) (hJ i))
  have hAI := inter_definable_base B A (⋂ i, ⋂ j, J i j) hA hI
  have h := image_definable_base B _ hAI (fun _ : Fin 1 => (0 : Fin (N + 1)))
    (fun i j _ => Subsingleton.elim i j)
  apply (unary_definable_iff B _).mp
  convert h using 1
  ext y
  change AtLeast R N (y 0) ↔ ∃ z ∈ A ∩ (⋂ i, ⋂ j, J i j), z ∘ (fun _ => 0) = y
  constructor
  · rintro ⟨u, hu, hR⟩
    refine ⟨Fin.cons (y 0) u, ⟨?_, ?_⟩, ?_⟩
    · exact hR
    · simp only [Set.mem_iInter]
      intro i j
      change Fin.cons (y 0) u ∈ J i j
      by_cases hij : i = j
      · simp only [J, ite_eq_left hij, Set.mem_univ]
      · simp only [J, ite_eq_right hij, Set.mem_ofPred_eq, Fin.cons_succ]
        exact fun he => hij (hu he)
    · funext i
      exact congrArg y (Subsingleton.elim 0 i)
  · rintro ⟨z, ⟨hzA, hzJ⟩, hzy⟩
    have hy : z 0 = y 0 := congrFun hzy 0
    refine ⟨(fun i => z i.succ), ?_, ?_⟩
    · intro i j hij
      by_contra hne
      have h := Set.mem_iInter.mp (Set.mem_iInter.mp hzJ i) j
      change z ∈ J i j at h
      simp only [J, ite_eq_right hne, Set.mem_ofPred_eq] at h
      exact h hij
    · intro i
      simpa only [hy] using hzA i

theorem atMost_definable_base (B : Base (M := M))
    (R : Set (Fin 2 → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ) :
    GammaDefinableOverBase B {y | ¬ AtLeast R (N + 1) y} :=
  GammaOrderLogic.complement_definable_base B _ (atLeast_definable_base B R hR (N + 1))

theorem exactly_definable_base (B : Base (M := M))
    (R : Set (Fin 2 → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ) :
    GammaDefinableOverBase B {y | AtLeast R N y ∧ ¬ AtLeast R (N + 1) y} :=
  GammaDefinableFunctions.inter_definable_base B _ _
    (atLeast_definable_base B R hR N) (atMost_definable_base B R hR N)

theorem atMost_iff (R : Set (Fin 2 → Values.Gamma (M := M))) (N : ℕ)
    (y : Values.Gamma (M := M)) :
    ¬ AtLeast R (N + 1) y ↔ {x | ![x, y] ∈ R}.Finite ∧ {x | ![x, y] ∈ R}.ncard ≤ N :=
  (EulerFunction.finite_ncard_le_iff_no_inj {x | ![x, y] ∈ R} N).symm

theorem exactly_iff (R : Set (Fin 2 → Values.Gamma (M := M))) (N : ℕ)
    (y : Values.Gamma (M := M)) :
    (AtLeast R N y ∧ ¬ AtLeast R (N + 1) y) ↔
      {x | ![x, y] ∈ R}.Finite ∧ {x | ![x, y] ∈ R}.ncard = N := by
  constructor
  · rintro ⟨⟨u, hu, hmem⟩, hm⟩
    obtain ⟨hf, hle⟩ := (atMost_iff R N y).mp hm
    have hlo : (Set.univ : Set (Fin N)).ncard ≤ {x | ![x, y] ∈ R}.ncard :=
      Set.ncard_le_ncard_of_injOn u (fun i _ => hmem i) (fun _ _ _ _ h => hu h) hf
    rw [Set.ncard_univ] at hlo
    simp only [Nat.card_fin] at hlo
    exact ⟨hf, Nat.le_antisymm hle hlo⟩
  · rintro ⟨hf, hcard⟩
    exact ⟨EulerFunction.exists_fin_inj_of_finite_ncard _ hf hcard,
      (atMost_iff R N y).mpr ⟨hf, hcard.le⟩⟩

end DiamondIntegral.Section4.GammaFibreCounting
