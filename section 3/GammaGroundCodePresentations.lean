import «section 3».GammaGroundFiniteFamilies
import «section 3».CodePresentations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P : Space LRV M}

def gammaGroundCodePreimage (A : GammaGroundDefSet hc ground P) : GammaGroundDefSet hc ground (codeSpace P) where
  carrier := {c | P.decode c ∈ A.carrier}
  definable := by
    let F : Map (DefSet.univ (codeSpace P) ground.real) (DefSet.univ P ground.real) := codeDecode (DefSet.univ P ground.real)
    exact A.definable.preimage F

def gammaGroundCodeDecode (A : GammaGroundDefSet hc ground P) : GammaGroundMap (gammaGroundCodePreimage A) A :=
  GammaGroundMap.ofGlobal _ _ (codeDecode (DefSet.univ P ground.real)) (fun c => c.property)

theorem gammaGroundCodeDecode_surjective (A : GammaGroundDefSet hc ground P) :
    Function.Surjective (gammaGroundCodeDecode A) := by
  intro a
  obtain ⟨c, he⟩ := P.onto a.val
  have hm : P.decode c ∈ A.carrier := he.symm ▸ a.property
  exact ⟨⟨c, hm⟩, Subtype.ext he⟩

def GammaGroundFiniteFamily.codeLift (A : GammaGroundFiniteFamily hc ground P) :
    GammaGroundFiniteFamily hc ground (codeSpace P) := ⟨A.tags, fun i => gammaGroundCodePreimage (A.piece i)⟩

def GammaGroundFiniteFamily.decode (A : GammaGroundFiniteFamily hc ground P)
    (c : A.codeLift.Carrier) : A.Carrier := ⟨c.1, gammaGroundCodeDecode (A.piece c.1) c.2⟩

theorem GammaGroundFiniteFamily.decode_surjective (A : GammaGroundFiniteFamily hc ground P) :
    Function.Surjective A.decode := by
  rintro ⟨i, a⟩
  obtain ⟨c, rfl⟩ := gammaGroundCodeDecode_surjective (A.piece i) a
  exact ⟨⟨i, c⟩, rfl⟩

end DiamondIntegral.Section3
