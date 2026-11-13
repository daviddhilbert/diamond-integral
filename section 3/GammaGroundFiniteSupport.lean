import «section 3».GammaGroundParameters

/-! Finitely many formulas over the Gamma ground base have one common
finite tuple of actual Gamma parameters, even with different target sorts. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

theorem GammaGroundDefinable.finiteSupport {n : ℕ} (Q : Fin n → Space LRV M)
    (A : ∀ i, Set (Q i).Carrier) (hA : ∀ i, GammaGroundDefinable hc ground (Q i) (A i)) :
    ∃ k, ∃ γ : Fin k → Values.Gamma (M := M), (∀ i, γ i ∈ ground.gamma) ∧
      ∀ i, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin k)) γ (Q i) ground.real (A i) := by
  induction n with
  | zero => exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨k, γ, hγ, h0⟩ := hA 0
    obtain ⟨l, δ, hδ, htail⟩ := ih (fun i => Q i.succ) (fun i => A i.succ) (fun i => hA i.succ)
    refine ⟨k + l, Fin.append γ δ, gammaGroundNames_append hγ hδ, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0.changeName (universalPowerProjection (volumeGammaSpace hc) ground.real (Fin.castAdd l))
        (gammaPowerProjection_left_append ground.real k l γ δ)
    · exact (htail j).changeName (universalPowerProjection (volumeGammaSpace hc) ground.real (Fin.natAdd k))
        (gammaPowerProjection_right_append ground.real k l γ δ)

end DiamondIntegral.Section3
