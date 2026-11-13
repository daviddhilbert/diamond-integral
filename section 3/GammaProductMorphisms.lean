import «section 3».GammaProductCodeFunctions
import «section 3».GammaCodeDescent

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}
variable {A A' : GammaObject hc S k} {B B' : GammaObject hc S l}

def gammaProductFunctionEquiv (f : FamilyBijection A A') (g : FamilyBijection B B') :
    (A.product B).Carrier ≃ (A'.product B').Carrier :=
  (A.productCarrierEquiv B).trans ((Equiv.prodCongr f.equiv g.equiv).trans (A'.productCarrierEquiv B').symm)

theorem gammaProductFunctionEquiv_factor (f : FamilyBijection A A') (g : FamilyBijection B B')
    (a : (A.product B).Carrier) :
    A'.productCarrierEquiv B' (gammaProductFunctionEquiv f g a) =
      (f.equiv (A.productCarrierEquiv B a).1, g.equiv (A.productCarrierEquiv B a).2) :=
  (A'.productCarrierEquiv B').apply_symm_apply _

def GammaHom.productCodes (f : GammaHom A A') (g : GammaHom B B') :
    FamilyBijection (A.product B).codeLift (A'.product B').codeLift :=
  gammaProductCodeBijection (Classical.choose f.contraction) (Classical.choose g.contraction)

theorem GammaHom.productCodes_contract (f : GammaHom A A') (g : GammaHom B B')
    (c : (A.product B).codeLift.Carrier) :
    (A'.product B').decode ((f.productCodes g).equiv c) =
      gammaProductFunctionEquiv f.bijection g.bijection ((A.product B).decode c) := by
  let F := Classical.choose f.contraction
  let G := Classical.choose g.contraction
  have hF : ∀ a, A'.decode (F.equiv a) = f.bijection.equiv (A.decode a) := Classical.choose_spec f.contraction
  have hG : ∀ b, B'.decode (G.equiv b) = g.bijection.equiv (B.decode b) := Classical.choose_spec g.contraction
  apply (A'.productCarrierEquiv B').injective
  change A'.productCarrierEquiv B' ((A'.product B').decode (gammaProductCodeFunctionEquiv F G c)) = _
  calc
    _ = (A'.decode (F.equiv (A.productCodeEquiv B c).1), B'.decode (G.equiv (A.productCodeEquiv B c).2)) := by
      rw [GammaObject.productCodeEquiv_decode, gammaProductCodeFunctionEquiv_factor]
    _ = (f.bijection.equiv (A.decode (A.productCodeEquiv B c).1),
        g.bijection.equiv (B.decode (A.productCodeEquiv B c).2)) := congrArg₂ Prod.mk (hF _) (hG _)
    _ = (f.bijection.equiv (A.productCarrierEquiv B ((A.product B).decode c)).1,
        g.bijection.equiv (A.productCarrierEquiv B ((A.product B).decode c)).2) :=
      congrArg (Equiv.prodCongr f.bijection.equiv g.bijection.equiv) (A.productCodeEquiv_decode B c).symm
    _ = _ := (gammaProductFunctionEquiv_factor f.bijection g.bijection _).symm

def GammaHom.product (f : GammaHom A A') (g : GammaHom B B') : GammaHom (A.product B) (A'.product B') where
  bijection := {
    equiv := gammaProductFunctionEquiv f.bijection g.bijection
    definable := (f.productCodes g).definable.descend _ (f.productCodes_contract g) }
  contraction := ⟨f.productCodes g, f.productCodes_contract g⟩

theorem GammaHom.product_factor (f : GammaHom A A') (g : GammaHom B B') (a : (A.product B).Carrier) :
    A'.productCarrierEquiv B' ((f.product g).bijection.equiv a) =
      (f.bijection.equiv (A.productCarrierEquiv B a).1, g.bijection.equiv (A.productCarrierEquiv B a).2) :=
  gammaProductFunctionEquiv_factor f.bijection g.bijection a

end DiamondIntegral.Section3
