import «section 3».EssentialVFMeasure

/-! Restriction comparison for the actual fixed-label Jacobians. This
extracts the pointwise argument already used by EssentialVFMeasure. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "X" => Fin n → VF
variable {A A' : Set (rawMixedSpace (M := M) n r).Carrier}
variable {B B' : Set (rawMixedSpace (M := M) n s).Carrier}

theorem mixedJacobian_eq_of_restriction (f : A → B) (g : A' → B')
    (i : A' → A) (hi : ∀ p, (i p).val = p.val) (he : ∀ p, (g p).val = (f (i p)).val)
    (p : A') {J K : VF} (hJ : HasMixedVFJacobianAt f (i p) J) (hK : HasMixedVFJacobianAt g p K) :
    J = K := by
  obtain ⟨F, ⟨ρ, hρ⟩, hf⟩ := hJ
  obtain ⟨G, ⟨σ, hσ⟩, hg⟩ := hK
  have hball : Set.EqOn F G (vfBall p.val.1 (max ρ σ)) := by
    intro x hx
    obtain ⟨ha, hfa⟩ := hρ x (by rw [hi]; exact vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hb, hgb⟩ := hσ x (vfBall_anti (le_max_right _ _) hx)
    let b : A' := ⟨(x, p.val.2), hb⟩
    have hab : (⟨(x, (i p).val.2), ha⟩ : A) = i b := by
      apply Subtype.ext
      change (x, (i p).val.2) = (i b).val
      rw [hi b]
      exact congrArg (Prod.mk x) (congrArg Prod.snd (hi p))
    have hf' := congrArg Prod.fst hfa
    rw [hab, ← he] at hf'
    exact hf'.symm.trans (congrArg Prod.fst hgb)
  have hf' : HasVFJacobianAt F p.val.1 J := by simpa only [hi] using hf
  exact (hf'.congr_on_vfBall hball).unique hg


end DiamondIntegral.Section3
