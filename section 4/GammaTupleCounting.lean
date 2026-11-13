import «section 4».GammaFibreCounting
import «section 4».GammaIntegerFamilies

/-! Bounded counting in unary Gamma fibres with arbitrary finite Gamma
parameter tuples. Distinctness is imposed on Gamma values themselves. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaTupleCounting
open GammaOrderLogic GammaRelationLogic GammaQuantifierLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def AtLeast {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (N : ℕ)
    (y : Fin n → Values.Gamma (M := M)) : Prop :=
  ∃ u : Fin N → Values.Gamma (M := M), Function.Injective u ∧ ∀ i, Fin.cons (u i) y ∈ R

theorem atLeast_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ) :
    GammaDefinable B {y | AtLeast R N y} := by
  let A : Set (Fin (N + n) → Values.Gamma (M := M)) :=
    {z | ∀ i : Fin N, Fin.cons (z (Fin.castAdd n i)) (fun j => z (Fin.natAdd N j)) ∈ R}
  have hA : GammaDefinable B A := by
    have hi (i : Fin N) : GammaDefinable B
        {z : Fin (N + n) → Values.Gamma (M := M) |
          Fin.cons (z (Fin.castAdd n i)) (fun j => z (Fin.natAdd N j)) ∈ R} := by
      have h := preimage_definable_base B R hR (Fin.cons (Fin.castAdd n i) (Fin.natAdd N))
      convert h using 1
      ext z
      have he : z ∘ Fin.cons (Fin.castAdd n i) (Fin.natAdd N) =
          (Fin.cons (z (Fin.castAdd n i)) (fun j => z (Fin.natAdd N j)) :
            Fin (n + 1) → Values.Gamma (M := M)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      change (Fin.cons (z (Fin.castAdd n i)) (fun j => z (Fin.natAdd N j)) ∈ R) ↔
        z ∘ Fin.cons (Fin.castAdd n i) (Fin.natAdd N) ∈ R
      rw [he]
    simpa only [A, Set.iInter_ofPred] using finite_iInter_definable_base B _ hi
  let J (i j : Fin N) : Set (Fin (N + n) → Values.Gamma (M := M)) :=
    if i = j then Set.univ else {z | z (Fin.castAdd n i) ≠ z (Fin.castAdd n j)}
  have hJ (i j : Fin N) : GammaDefinable B (J i j) := by
    by_cases h : i = j
    · simpa only [J, ite_eq_left h] using GammaIntegerFamilies.univ_definable_base B (N + n)
    · simpa only [J, ite_eq_right h] using
        GammaFibreCounting.ne_definable_base B (Fin.castAdd n i) (Fin.castAdd n j)
  have hI := finite_iInter_definable_base B (fun i => ⋂ j, J i j)
    (fun i => finite_iInter_definable_base B (J i) (hJ i))
  have hAI := inter_definable_base B A (⋂ i, ⋂ j, J i j) hA hI
  have h := image_definable_base B _ hAI (Fin.natAdd N) (Fin.natAdd_injective n N)
  convert h using 1
  ext y
  change AtLeast R N y ↔ ∃ z ∈ A ∩ (⋂ i, ⋂ j, J i j), z ∘ Fin.natAdd N = y
  constructor
  · rintro ⟨u, hu, hRu⟩
    refine ⟨Fin.append u y, ⟨?_, ?_⟩, funext (Fin.append_right u y)⟩
    · change ∀ i, Fin.cons (Fin.append u y (Fin.castAdd n i))
        (fun j => Fin.append u y (Fin.natAdd N j)) ∈ R
      simpa only [Fin.append_left, Fin.append_right] using hRu
    · simp only [Set.mem_iInter]
      intro i j
      by_cases hij : i = j
      · simp only [J, ite_eq_left hij, Set.mem_univ]
      · simp only [J, ite_eq_right hij, Set.mem_ofPred_eq, Fin.append_left]
        exact fun he => hij (hu he)
  · rintro ⟨z, ⟨hzA, hzJ⟩, hzy⟩
    change (fun j => z (Fin.natAdd N j)) = y at hzy
    refine ⟨(fun i => z (Fin.castAdd n i)), ?_, ?_⟩
    · intro i j hij
      by_contra hne
      have h := Set.mem_iInter.mp (Set.mem_iInter.mp hzJ i) j
      change z ∈ J i j at h
      simp only [J, ite_eq_right hne, Set.mem_ofPred_eq] at h
      exact h hij
    · intro i
      simpa only [hzy] using hzA i

theorem atMost_iff {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (N : ℕ)
    (y : Fin n → Values.Gamma (M := M)) :
    ¬ AtLeast R (N + 1) y ↔ {x | Fin.cons x y ∈ R}.Finite ∧ {x | Fin.cons x y ∈ R}.ncard ≤ N := by
  change (¬ ∃ u : Fin (N + 1) → Values.Gamma (M := M), Function.Injective u ∧
    ∀ i, Fin.cons (u i) y ∈ R) ↔ _
  exact (EulerFunction.finite_ncard_le_iff_no_inj
    {x : Values.Gamma (M := M) | (Fin.cons x y : Fin (n + 1) → Values.Gamma (M := M)) ∈ R} N).symm

theorem exactly_iff {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (N : ℕ)
    (y : Fin n → Values.Gamma (M := M)) :
    (AtLeast R N y ∧ ¬ AtLeast R (N + 1) y) ↔
      {x | Fin.cons x y ∈ R}.Finite ∧ {x | Fin.cons x y ∈ R}.ncard = N := by
  constructor
  · rintro ⟨⟨u, hu, hmem⟩, hm⟩
    obtain ⟨hf, hle⟩ := (atMost_iff R N y).mp hm
    have hlo : (Set.univ : Set (Fin N)).ncard ≤ {x | Fin.cons x y ∈ R}.ncard :=
      Set.ncard_le_ncard_of_injOn u (fun i _ => hmem i) (fun _ _ _ _ h => hu h) hf
    rw [Set.ncard_univ] at hlo
    simp only [Nat.card_fin] at hlo
    exact ⟨hf, Nat.le_antisymm hle hlo⟩
  · rintro ⟨hf, hcard⟩
    exact ⟨EulerFunction.exists_fin_inj_of_finite_ncard _ hf hcard,
      (atMost_iff R N y).mpr ⟨hf, hcard.le⟩⟩

theorem exactly_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ) :
    GammaDefinable B {y | AtLeast R N y ∧ ¬ AtLeast R (N + 1) y} :=
  inter_definable_base B _ _ (atLeast_definable_base B R hR N)
    (complement_definable_base B _ (atLeast_definable_base B R hR (N + 1)))

theorem atLeast_succ_iff {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (N : ℕ)
    (y : Fin n → Values.Gamma (M := M)) (hf : {x | Fin.cons x y ∈ R}.Finite) :
    AtLeast R (N + 1) y ↔ N < {x | Fin.cons x y ∈ R}.ncard := by
  simpa only [hf, true_and, not_not, not_le] using not_congr (atMost_iff R N y)

end DiamondIntegral.Section4.GammaTupleCounting
