import «section 3».GammaGroundGammaRVCodeLift
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

/-- The lift contains every RV representative of every value tuple in I. -/
theorem gammaGroundGammaRVCodeLift_mem (I : GammaGroundGammaPiece hc ground k)
    (t : (rawRVSpace (M := M) k).Carrier) :
    t ∈ (gammaGroundGammaRVCodeLift I).domain.carrier ↔
      ∃ γ ∈ I.carrier, ∀ i, (γ i).val = Values.vrv (t i) := by
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨((volumeGammaSpace hc).power (Fin k)).decode c.val,c.property,?_⟩
    intro i
    rfl
  · rintro ⟨γ,hγ,he⟩
    have hn (i : Fin k) : (t i).val ≠ iRVZero := by
      intro hz
      exact (γ i).property ((he i).trans ((Values.vrv_eq_infinity_iff (t i)).mpr hz))
    let c : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier :=
      ⟨fun ij => (t ij.1).val,fun i => ⟨(t i).property,hn i⟩⟩
    have hd : ((volumeGammaSpace hc).power (Fin k)).decode c = γ := by
      funext i
      apply Subtype.ext
      exact (he i).symm
    let d : gammaGroundCodePreimage I := ⟨c,by
      change ((volumeGammaSpace hc).power (Fin k)).decode c ∈ I.carrier
      rw [hd]
      exact hγ⟩
    refine ⟨d,?_⟩
    funext i
    apply Subtype.ext
    rfl
end DiamondIntegral.Section3
