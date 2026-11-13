import «section 4».GammaRelationLogic
import Section3.GammaClosureLaws

/-! Quantification over arbitrary finite tuples of actual Gamma values.
Coordinate images are restricted to injective coordinate selections, so
the image retains every nonzero RV code of each output Gamma tuple. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaQuantifierLogic
open GammaOrderLogic GammaRelationLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem image_definable_base (B : Base (M := M)) {n m : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M))) (hP : GammaDefinable B P)
    (π : Fin m → Fin n) (hπ : Function.Injective π) :
    GammaDefinable B ((fun w => w ∘ π) '' P) := by
  have h := hP.image_real π
  change DefinableOverBase B (fun _ : Fin m => .rv)
    ((fun w => w ∘ π) ''
      {w | Proper w ∧ (fun j => codeValue (M := M) (w j)) ∈ P}) at h
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ ∃ w ∈ P, w ∘ π = fun i => codeValue (M := M) (z i)) ↔
    ∃ w, (Proper w ∧ (fun i => codeValue (M := M) (w i)) ∈ P) ∧ w ∘ π = z
  constructor
  · rintro ⟨hz, v, hv, he⟩
    choose t ht htv using fun j => EndpointLogic.codeValue_surjective (v j)
    let w : Fin n → M := fun j => if h : ∃ i, π i = j then z (Classical.choose h) else t j
    have hw (i : Fin m) : w (π i) = z i := by
      have hex : ∃ l, π l = π i := ⟨i, rfl⟩
      have hc : Classical.choose hex = i := hπ (Classical.choose_spec hex)
      simp only [w, dite_eq_left hex, hc]
    have hval (j : Fin n) : codeValue (M := M) (w j) = v j := by
      by_cases hex : ∃ i, π i = j
      · obtain ⟨i, rfl⟩ := hex
        rw [hw]
        exact (congrFun he i).symm
      · simp only [w, dite_eq_right hex]
        exact htv j
    refine ⟨w, ⟨?_, ?_⟩, funext hw⟩
    · intro j
      by_cases hex : ∃ i, π i = j
      · obtain ⟨i, rfl⟩ := hex
        rw [hw]
        exact hz i
      · simp only [w, dite_eq_right hex]
        exact ht j
    · convert hv using 1
      exact funext hval
  · rintro ⟨w, ⟨hw, hp⟩, he⟩
    have hs (i : Fin m) : w (π i) = z i := congrFun he i
    refine ⟨(fun i => hs i ▸ hw (π i)), (fun j => codeValue (M := M) (w j)), hp, ?_⟩
    funext i
    exact congrArg (codeValue (M := M)) (hs i)

theorem finite_iInter_definable_base (B : Base (M := M)) {n : ℕ} {ι : Type}
    [Finite ι] (P : ι → Set (Fin n → Values.Gamma (M := M)))
    (hP : ∀ i, GammaDefinable B (P i)) : GammaDefinable B (⋂ i, P i) := by
  let _ := Fintype.ofFinite ι
  have h := DefinableOverBase.finite_iInter Finset.univ
    (fun i => {z : Fin n → M | Proper z ∧ (fun j => codeValue (M := M) (z j)) ∈ P i})
    (fun i _ => hP i)
  have hp := (proper_definable_base B n).inter h
  unfold GammaDefinable
  convert hp using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  change (Proper z ∧ ∀ i, (fun j => codeValue (M := M) (z j)) ∈ P i) ↔
    Proper z ∧ (z ∈ sortedUniverse (fun _ => .rv) ∧
      ∀ i ∈ Finset.univ, Proper z ∧ (fun j => codeValue (M := M) (z j)) ∈ P i)
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨hz, (fun i => (hz i).1), fun i _ => ⟨hz, hp i⟩⟩
  · rintro ⟨hz, _, hp⟩
    exact ⟨hz, fun i => (hp i (Finset.mem_univ i)).2⟩

theorem union_definable_base (B : Base (M := M)) {n : ℕ}
    (P Q : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaDefinable B P) (hQ : GammaDefinable B Q) : GammaDefinable B (P ∪ Q) := by
  have h := complement_definable_base B _ (inter_definable_base B _ _
    (complement_definable_base B P hP) (complement_definable_base B Q hQ))
  simpa only [Set.compl_inter, compl_compl] using h

theorem finite_iUnion_definable_base (B : Base (M := M)) {n : ℕ} {ι : Type}
    [Finite ι] (P : ι → Set (Fin n → Values.Gamma (M := M)))
    (hP : ∀ i, GammaDefinable B (P i)) : GammaDefinable B (⋃ i, P i) := by
  have h := complement_definable_base B _ (finite_iInter_definable_base B
    (fun i => (P i)ᶜ) (fun i => complement_definable_base B (P i) (hP i)))
  simpa only [Set.compl_iInter, compl_compl] using h

end DiamondIntegral.Section4.GammaQuantifierLogic
