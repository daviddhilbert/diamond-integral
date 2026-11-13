import «section 3».GammaGroundGammaProductLaws
import «section 3».ProductTagDistributivity
/-! Gamma cartesian products distribute over the actual tagged disjoint
unions through an explicit definable tag permutation. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaProductRightDistribHom (A : GammaGroundGammaObject hc ground k) (B D : GammaGroundGammaObject hc ground l) :
    GammaGroundGammaHom (A.product (B.coprod D)) ((A.product B).coprod (A.product D)) :=
  gammaGroundGammaTagHom _ _ (finProductSumDistrib A.tags B.tags D.tags) (by
    intro i
    obtain ⟨p, rfl⟩ := (finProdFinEquiv : Fin A.tags × Fin (B.tags + D.tags) ≃ Fin (A.tags * (B.tags + D.tags))).surjective i
    obtain ⟨a, q⟩ := p
    refine Fin.addCases (fun b => ?_) (fun d => ?_) q
    · simp only [GammaGroundGammaObject.product, GammaGroundFiniteFamily.coprod, Equiv.symm_apply_apply,
        Fin.addCases_left, finProductSumDistrib_left]
      have h1 := (finProdFinEquiv : Fin A.tags × Fin (B.tags + D.tags) ≃ Fin (A.tags * (B.tags + D.tags))).symm_apply_apply (a, Fin.castAdd D.tags b)
      have h2 := (finProdFinEquiv : Fin A.tags × Fin B.tags ≃ Fin (A.tags * B.tags)).symm_apply_apply (a, b)
      rw [h1, h2]
      exact congrArg (fun P => (gammaGroundGammaAppendMap (A.piece a) P).image.carrier)
        (Fin.addCases_left (motive := fun _ => _) (left := B.piece) (right := D.piece) b)
    · simp only [GammaGroundGammaObject.product, GammaGroundFiniteFamily.coprod, Equiv.symm_apply_apply,
        Fin.addCases_right, finProductSumDistrib_right]
      have h1 := (finProdFinEquiv : Fin A.tags × Fin (B.tags + D.tags) ≃ Fin (A.tags * (B.tags + D.tags))).symm_apply_apply (a, Fin.natAdd B.tags d)
      have h2 := (finProdFinEquiv : Fin A.tags × Fin D.tags ≃ Fin (A.tags * D.tags)).symm_apply_apply (a, d)
      rw [h1, h2]
      exact congrArg (fun P => (gammaGroundGammaAppendMap (A.piece a) P).image.carrier)
        (Fin.addCases_right (motive := fun _ => _) (left := B.piece) (right := D.piece) d))

theorem gammaGroundGammaClass_product_coprod (A : GammaGroundGammaObject hc ground k) (B D : GammaGroundGammaObject hc ground l) :
    gammaGroundGammaClass (A.product (B.coprod D)) = gammaGroundGammaClass (A.product B) + gammaGroundGammaClass (A.product D) :=
  (gammaGroundGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundGammaProductRightDistribHom A B D))).trans (gammaGroundGammaClass_coprod _ _)

end DiamondIntegral.Section3
