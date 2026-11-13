import «section 3».DefinableBijections
import Section4.MapCorestrict
import Section4.Products
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}
namespace DefinableBijection

def inverseImage (f : DefinableBijection A B) (Y : DefSet Q S) : DefSet P S :=
  ⟨{x | ∃ a : A, a.val = x ∧ (f.map a).val ∈ Y.carrier},f.map.definable_preimage Y.definable⟩

theorem inverseImage_subset (f : DefinableBijection A B) (Y : DefSet Q S) :
    (f.inverseImage Y).carrier ⊆ A.carrier :=
  fun _ ⟨a,ha,_⟩ => ha ▸ a.property

def restrictTargetMap (f : DefinableBijection A B) (Y : DefSet Q S) : Map (f.inverseImage Y) Y :=
  (f.map.restrict (f.inverseImage_subset Y)).corestrict (fun x => by
    obtain ⟨a,ha,hy⟩ := x.property
    have he : (⟨x.val,f.inverseImage_subset Y x.property⟩ : A) = a := Subtype.ext ha.symm
    change (f.map ⟨x.val,f.inverseImage_subset Y x.property⟩).val ∈ Y.carrier
    rw [he]
    exact hy)

/-- Restriction to a definable target piece is an actual same-base
bijection with its definable preimage. -/
def restrictTarget (f : DefinableBijection A B) (Y : DefSet Q S) (hY : Y.carrier ⊆ B.carrier) :
    DefinableBijection (f.inverseImage Y) Y where
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
end DefinableBijection
end DiamondIntegral.Section3
