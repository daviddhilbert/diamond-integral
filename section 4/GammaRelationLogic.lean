import «section 4».GammaOrderLogic

/-! Closure of full Gamma relations under coordinate substitution and
quantification, preserving the original real/imaginary parameter base.
Existential elimination drops one coordinate; it never mistakes a repeated
raw RV projection for a full invariant Gamma preimage. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRelationLogic
open GammaOrderLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem preimage_definable_base (B : Base (M := M)) {n m : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M))) (hP : GammaDefinable B P) (π : Fin n → Fin m) :
    GammaDefinable B {z | z ∘ π ∈ P} := by
  have h := (proper_definable_base B m).inter
    (hP.preimage_real (fun _ : Fin m => .rv) π)
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ (fun i => codeValue (M := M) (z (π i))) ∈ P) ↔
    Proper z ∧ (Proper (z ∘ π) ∧ (fun i => codeValue (M := M) (z (π i))) ∈ P) ∧
      z ∈ sortedUniverse (fun _ => .rv)
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨hz, ⟨(fun i => hz (π i)), hp⟩, fun i => (hz i).1⟩
  · rintro ⟨hz, ⟨_, hp⟩, _⟩
    exact ⟨hz, hp⟩

theorem inter_definable_base (B : Base (M := M)) {n : ℕ}
    (P Q : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaDefinable B P) (hQ : GammaDefinable B Q) : GammaDefinable B (P ∩ Q) := by
  have h := hP.inter hQ
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ P ∩ Q) ↔
    (Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ P) ∧
      (Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ Q)
  simp only [Set.mem_inter_iff]
  tauto

theorem complement_definable_base (B : Base (M := M)) {n : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M))) (hP : GammaDefinable B P) :
    GammaDefinable B Pᶜ := by
  have h := (proper_definable_base B n).inter hP.compl
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ (fun i => codeValue (M := M) (z i)) ∉ P) ↔
    Proper z ∧ z ∈ sortedUniverse (fun _ => .rv) ∧
      ¬ (Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ P)
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, (fun i => (hz i).1), fun h => hn h.2⟩
  · rintro ⟨hz, _, hn⟩
    exact ⟨hz, fun h => hn ⟨hz, h⟩⟩

theorem exists_definable_base (B : Base (M := M)) {n : ℕ}
    (P : Set (Fin (n + 1) → Values.Gamma (M := M))) (hP : GammaDefinable B P) :
    GammaDefinable B {z | ∃ x, Fin.cons x z ∈ P} := by
  have h := hP.image_real (fun i : Fin n => i.succ)
  change DefinableOverBase B (fun _ : Fin n => .rv)
    ((fun w => w ∘ (fun i : Fin n => i.succ)) ''
      {w | Proper w ∧ (fun i => codeValue (M := M) (w i)) ∈ P}) at h
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ ∃ x, Fin.cons x (fun i => codeValue (M := M) (z i)) ∈ P) ↔
    ∃ w, (Proper w ∧ (fun i => codeValue (M := M) (w i)) ∈ P) ∧
      w ∘ (fun i : Fin n => i.succ) = z
  constructor
  · rintro ⟨hz, x, hx⟩
    obtain ⟨t, ht, htx⟩ := EndpointLogic.codeValue_surjective x
    refine ⟨Fin.cons t z, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact Fin.cases ht (fun j => hz j) i
    · have he : (fun i : Fin (n + 1) =>
          codeValue (M := M) ((Fin.cons t z : Fin (n + 1) → M) i)) =
          (Fin.cons x (fun i : Fin n => codeValue (M := M) (z i)) :
            Fin (n + 1) → Values.Gamma (M := M)) := by
        funext i
        exact Fin.cases htx (fun _ => rfl) i
      rw [he]
      exact hx
    · funext i
      rfl
  · rintro ⟨w, ⟨hw, hp⟩, he⟩
    have hs (i : Fin n) : w i.succ = z i := congrFun he i
    refine ⟨(fun i => hs i ▸ hw i.succ), codeValue (M := M) (w 0), ?_⟩
    have hc : Fin.cons (codeValue (M := M) (w 0)) (fun i => codeValue (M := M) (z i)) =
        (fun i => codeValue (M := M) (w i)) := by
      funext i
      exact Fin.cases rfl (fun j => congrArg (codeValue (M := M)) (hs j).symm) i
    rw [hc]
    exact hp

end DiamondIntegral.Section4.GammaRelationLogic
