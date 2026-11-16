import «section 6».ProjectedFocusPieces

/-! Same-base descent of an actual definable map through a surjective
definable projection. A temporary set-theoretic section does not enter
the defining graph or enlarge the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M]
variable {P Q R : Space LRV M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

def descendSurjectiveMap (π : Map A B) (hπ : Function.Surjective π) (f : Map A C)
    (hcompat : ∀ a b : A, π a = π b → f a = f b) : Map B C := by
  let sectionPoint (b : B) : A := (hπ b).choose
  have hsection (b : B) : π (sectionPoint b) = b := (hπ b).choose_spec
  let g (b : B) := f (sectionPoint b)
  have hfactor (a : A) : g (π a) = f a := hcompat _ a (hsection (π a))
  refine ⟨g,?_⟩
  apply (((π.graph_definable.swap P Q).comp Q P R f.graph_definable).congr Q R)
  intro x z
  constructor
  · rintro ⟨y,⟨a,rfl,hπa⟩,⟨b,hba,hfb⟩⟩
    have hba' : b = a := Subtype.ext hba
    subst b
    exact ⟨π a,hπa,by rw [hfactor]; exact hfb⟩
  · rintro ⟨b,rfl,hgb⟩
    exact ⟨(sectionPoint b).val,⟨sectionPoint b,rfl,congrArg Subtype.val (hsection b)⟩,
      sectionPoint b,rfl,hgb⟩

theorem descendSurjectiveMap_factor (π : Map A B) (hπ : Function.Surjective π) (f : Map A C)
    (hcompat : ∀ a b : A, π a = π b → f a = f b) (a : A) :
    descendSurjectiveMap π hπ f hcompat (π a) = f a :=
  hcompat _ a (hπ (π a)).choose_spec

theorem map_toImage_surjective (π : Map A B) : Function.Surjective π.toImage := by
  rintro ⟨b,a,ha⟩
  exact ⟨a,Subtype.ext ha⟩

end DiamondIntegral.Section6
