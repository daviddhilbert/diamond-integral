import «section 3».GammaGroundMapPreimages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
namespace GammaGroundBijection

def inverseImage (f : GammaGroundBijection A B) (Y : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground P :=
  f.map.preimage Y

theorem inverseImage_subset (f : GammaGroundBijection A B) (Y : GammaGroundDefSet hc ground Q) :
    (f.inverseImage Y).carrier ⊆ A.carrier :=
  fun _ ⟨a,ha,_⟩ => ha ▸ a.property

def restrictTargetMap (f : GammaGroundBijection A B) (Y : GammaGroundDefSet hc ground Q) : GammaGroundMap (f.inverseImage Y) Y :=
  (f.map.restrict (f.inverseImage_subset Y)).corestrict (fun x => by
    obtain ⟨a,ha,hy⟩ := x.property
    have he : (⟨x.val,f.inverseImage_subset Y x.property⟩ : A) = a := Subtype.ext ha.symm
    change (f.map ⟨x.val,f.inverseImage_subset Y x.property⟩).val ∈ Y.carrier
    rw [he]
    exact hy)

/-- Restriction to a definable target piece is an actual same-base
bijection with its definable preimage. -/
def restrictTarget (f : GammaGroundBijection A B) (Y : GammaGroundDefSet hc ground Q) (hY : Y.carrier ⊆ B.carrier) :
    GammaGroundBijection (f.inverseImage Y) Y where
  map := f.restrictTargetMap Y
  bijective := by
    constructor
    · intro x y hxy
      have he := congrArg (fun z : Y => z.val) hxy
      change (f.map ⟨x.val,f.inverseImage_subset Y x.property⟩).val =
          (f.map ⟨y.val,f.inverseImage_subset Y y.property⟩).val at he
      have ha := f.bijective.1 (Subtype.ext he)
      exact Subtype.ext (congrArg (fun z : A => z.val) ha)
    · intro y
      obtain ⟨a,ha⟩ := f.bijective.2 ⟨y.val,hY y.property⟩
      have hy : (f.map a).val ∈ Y.carrier := by rw [ha]; exact y.property
      refine ⟨⟨a.val,a,rfl,hy⟩,?_⟩
      apply Subtype.ext
      change (f.map a).val = y.val
      exact congrArg (fun z : B => z.val) ha
end GammaGroundBijection
end DiamondIntegral.Section3
