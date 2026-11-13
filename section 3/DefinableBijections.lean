import Section4.DefinableCategory

/-! Groupoids of genuine definable bijections. All graphs and their inverses
are over the same base. This is the unmeasured morphism convention in §3. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section3

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R : Space L M} {S : Set M}

structure DefinableBijection (A : DefSet P S) (B : DefSet Q S) where
  map : Map A B
  bijective : Function.Bijective map

namespace DefinableBijection

variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

@[ext] theorem ext {f g : DefinableBijection A B} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : DefSet P S) : DefinableBijection A A := ⟨Map.id A, Function.bijective_id⟩

def comp (g : DefinableBijection B C) (f : DefinableBijection A B) :
    DefinableBijection A C := ⟨g.map.comp f.map, g.bijective.comp f.bijective⟩

noncomputable def symm (f : DefinableBijection A B) : DefinableBijection B A :=
  ⟨f.map.inverse f.bijective, (Equiv.ofBijective f.map f.bijective).symm.bijective⟩

@[simp] theorem symm_apply_apply (f : DefinableBijection A B) (a : A) :
    f.symm.map (f.map a) = a := Map.inverse_apply f.map f.bijective a

@[simp] theorem apply_symm_apply (f : DefinableBijection A B) (b : B) :
    f.map (f.symm.map b) = b := Map.apply_inverse f.map f.bijective b

end DefinableBijection

/-- Definable points are defined by singleton definability in the complete
presentation. This also works for imaginary sorts with many real codes. -/
def IsDefinablePoint (S : Set M) (x : P.Carrier) : Prop := P.Definable S {x}

theorem IsDefinablePoint.map {A : DefSet P S} {B : DefSet Q S} (f : Map A B)
    (a : A) (ha : IsDefinablePoint S a.val) : IsDefinablePoint S (f a).val := by
  let X : DefSet P S := ⟨{a.val}, ha⟩
  have hX : X.carrier ⊆ A.carrier := by
    intro x hx
    exact (Set.mem_singleton_iff.mp hx) ▸ a.property
  have h := (f.comp (Map.inclusion hX)).definable_image
  have he : Set.range (fun x : X => (f.comp (Map.inclusion hX) x).val) = {(f a).val} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (Map.inclusion hX x : A) = a := Subtype.ext (Set.mem_singleton_iff.mp x.property)
      simp only [Map.comp_apply, hx, Set.mem_singleton_iff]
    · intro hy
      exact ⟨⟨a.val, Set.mem_singleton _⟩, Set.mem_singleton_iff.mp hy |>.symm⟩
  change Q.Definable S {(f a).val}
  rwa [he] at h

theorem definableBijection_has_point_iff {A : DefSet P S} {B : DefSet Q S}
    (f : DefinableBijection A B) :
    (∃ a : A, IsDefinablePoint S a.val) ↔ ∃ b : B, IsDefinablePoint S b.val := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨f.map a, ha.map f.map a⟩
  · rintro ⟨b, hb⟩
    exact ⟨f.symm.map b, hb.map f.symm.map b⟩

end DiamondIntegral.Section3
