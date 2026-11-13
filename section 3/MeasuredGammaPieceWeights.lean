import «section 3».GammaGroundFormTotalization
import «section 3».GammaGroundMeasuredGammaSingleWeight
import «section 3».GammaGroundMeasuredGammaSemiring
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaGroundMeasuredGammaSingleForm (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    GammaGroundMeasuredGammaObject hc B n := ⟨GammaGroundGammaObject.single G,fun _ => w⟩

/-- Every actual form on one native Gamma piece has a full definable
combined-weight function, with no extension of the original ground. -/
theorem gammaGroundMeasuredGammaSingleForm_full_weight
    (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    ∃ f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M),
      ∃ hf : FullGammaFunction (integrationGammaBase B) f,
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleForm G w) =
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) := by
  obtain ⟨g,hg,hgval⟩ := gammaGroundGammaForm_total_function G w
  let f := fun γ : Fin n → Values.Gamma (M := M) => g γ * ∏ i, γ i
  have hf : FullGammaFunction (integrationGammaBase B) f :=
    hg.mul (FullGammaFunction.prod Finset.univ (fun i γ => γ i) (fun i _ => FullGammaFunction.proj _ i))
  let h : GammaGroundMeasuredGammaHom (gammaGroundMeasuredGammaSingleForm G w)
      (gammaGroundMeasuredGammaSingleWeight G f hf) :=
    { underlying := GammaGroundGammaHom.id (GammaGroundGammaObject.single G)
      preserves := by
        intro a
        rw [gammaGroundMeasuredGammaSingleWeight_combined]
        change (show Values.Gamma (M := M) from (w a.2).val) * (∏ i, (show Values.Gamma (M := M) from a.2.val i)) = g a.2.val * ∏ i, (show Values.Gamma (M := M) from a.2.val i)
        rw [hgval a.2] }
  exact ⟨f,hf,gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from h))⟩
end DiamondIntegral.Section3
