import «section 3».GammaGroundParameters

/-! Definable sets over the complete Gamma ground base retain their
actual carriers and use only finitely many names in each definition. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

def GammaGroundDefSet.ofReal (A : DefSet Q ground.real) : GammaGroundDefSet hc ground Q :=
  ⟨A.carrier, GammaGroundDefinable.of_real A.definable⟩

def GammaGroundDefSet.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (Q : Space LRV M) : GammaGroundDefSet hc ground Q :=
  .ofReal (DefSet.empty Q ground.real)

def GammaGroundDefSet.univ (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (Q : Space LRV M) : GammaGroundDefSet hc ground Q :=
  .ofReal (DefSet.univ Q ground.real)

def GammaGroundDefSet.inter (A B : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q :=
  ⟨A.carrier ∩ B.carrier, A.definable.inter B.definable⟩

def GammaGroundDefSet.union (A B : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q :=
  ⟨A.carrier ∪ B.carrier, A.definable.union B.definable⟩

def GammaGroundDefSet.compl (A : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q :=
  ⟨A.carrierᶜ, A.definable.compl⟩

def GammaGroundDefSet.sdiff (A B : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q := A.inter B.compl

end DiamondIntegral.Section3
