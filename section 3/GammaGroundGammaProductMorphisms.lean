import «section 3».GammaGroundGammaProductCodeFunctions
import «section 3».GammaGroundGammaCodeDescent
/-! Actual Gamma morphisms are closed under cartesian products. Their
full RV witnesses are multiplied before definability is descended. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}
variable {A A' : GammaGroundGammaObject hc ground k} {B B' : GammaGroundGammaObject hc ground l}

def gammaGroundGammaProductFunctionEquiv (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B') :
    (A.product B).Carrier ≃ (A'.product B').Carrier :=
  (A.productCarrierEquiv B).trans ((Equiv.prodCongr f.equiv g.equiv).trans (A'.productCarrierEquiv B').symm)

theorem gammaGroundGammaProductFunctionEquiv_factor (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B')
    (a : (A.product B).Carrier) :
    A'.productCarrierEquiv B' (gammaGroundGammaProductFunctionEquiv f g a) =
      (f.equiv (A.productCarrierEquiv B a).1, g.equiv (A.productCarrierEquiv B a).2) :=
  (A'.productCarrierEquiv B').apply_symm_apply _

def GammaGroundGammaHom.productCodes (f : GammaGroundGammaHom A A') (g : GammaGroundGammaHom B B') :
    GammaGroundFamilyBijection (A.product B).codeLift (A'.product B').codeLift :=
  gammaGroundGammaProductCodeBijection (Classical.choose f.contraction) (Classical.choose g.contraction)

theorem GammaGroundGammaHom.productCodes_contract (f : GammaGroundGammaHom A A') (g : GammaGroundGammaHom B B')
    (c : (A.product B).codeLift.Carrier) :
    (A'.product B').decode ((f.productCodes g).equiv c) =
      gammaGroundGammaProductFunctionEquiv f.bijection g.bijection ((A.product B).decode c) := by
  let F := Classical.choose f.contraction
  let G := Classical.choose g.contraction
  have hF : ∀ a, A'.decode (F.equiv a) = f.bijection.equiv (A.decode a) := Classical.choose_spec f.contraction
  have hG : ∀ b, B'.decode (G.equiv b) = g.bijection.equiv (B.decode b) := Classical.choose_spec g.contraction
  apply (A'.productCarrierEquiv B').injective
  change A'.productCarrierEquiv B' ((A'.product B').decode (gammaGroundGammaProductCodeFunctionEquiv F G c)) = _
  calc
    _ = (A'.decode (F.equiv (A.productCodeEquiv B c).1), B'.decode (G.equiv (A.productCodeEquiv B c).2)) := by
      rw [GammaGroundGammaObject.productCodeEquiv_decode, gammaGroundGammaProductCodeFunctionEquiv_factor]
    _ = (f.bijection.equiv (A.decode (A.productCodeEquiv B c).1),
        g.bijection.equiv (B.decode (A.productCodeEquiv B c).2)) := congrArg₂ Prod.mk (hF _) (hG _)
    _ = (f.bijection.equiv (A.productCarrierEquiv B ((A.product B).decode c)).1,
        g.bijection.equiv (A.productCarrierEquiv B ((A.product B).decode c)).2) :=
      congrArg (Equiv.prodCongr f.bijection.equiv g.bijection.equiv) (A.productCodeEquiv_decode B c).symm
    _ = _ := (gammaGroundGammaProductFunctionEquiv_factor f.bijection g.bijection _).symm

def GammaGroundGammaHom.product (f : GammaGroundGammaHom A A') (g : GammaGroundGammaHom B B') : GammaGroundGammaHom (A.product B) (A'.product B') where
  bijection := {
    equiv := gammaGroundGammaProductFunctionEquiv f.bijection g.bijection
    definable := (f.productCodes g).definable.descend _ (f.productCodes_contract g) }
  contraction := ⟨f.productCodes g, f.productCodes_contract g⟩

theorem GammaGroundGammaHom.product_factor (f : GammaGroundGammaHom A A') (g : GammaGroundGammaHom B B') (a : (A.product B).Carrier) :
    A'.productCarrierEquiv B' ((f.product g).bijection.equiv a) =
      (f.bijection.equiv (A.productCarrierEquiv B a).1, g.bijection.equiv (A.productCarrierEquiv B a).2) :=
  gammaGroundGammaProductFunctionEquiv_factor f.bijection g.bijection a

end DiamondIntegral.Section3
