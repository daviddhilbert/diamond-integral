import «section 3».MixedVFJacobianRestriction

/-! Fixed-label Jacobians depend only on the VF component of a map.
The target RV presentation can be changed without changing that number. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n r s t : ℕ} {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]
variable {A : Set ((Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))}
variable {D : Set ((Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M))}
variable {E : Set ((Fin n → VFType (M := M)) × (Fin t → CanonicalRV.RVSort M))}

theorem mixedJacobian_eq_of_vf_eq (f : A → D) (g : A → E)
    (he : ∀ p, (f p).val.1 = (g p).val.1) (p : A)
    {J K : VFType (M := M)} (hJ : HasMixedVFJacobianAt f p J) (hK : HasMixedVFJacobianAt g p K) : J = K := by
  obtain ⟨F,⟨ρ,hρ⟩,hF⟩ := hJ
  obtain ⟨H,⟨σ,hσ⟩,hH⟩ := hK
  have hball : Set.EqOn F H (vfBall p.val.1 (max ρ σ)) := by
    intro x hx
    obtain ⟨ha,hfa⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hb,hgb⟩ := hσ x (vfBall_anti (le_max_right _ _) hx)
    exact (congrArg Prod.fst hfa).symm.trans ((he ⟨(x,p.val.2),ha⟩).trans (congrArg Prod.fst hgb))
  exact (hF.congr_on_vfBall hball).unique hH

end DiamondIntegral.Section3
