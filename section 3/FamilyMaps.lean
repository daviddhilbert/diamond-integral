import «section 3».FiniteFamilies

/-! Functions between finite definable families carry their complete
branch graphs. Bijections supply such maps without changing parameters. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P Q R : Space L M}

structure FamilyMap (A : FiniteFamily P S) (B : FiniteFamily Q S) where
  toFun : A.Carrier → B.Carrier
  definable : FamilyDefinable A B toFun

@[ext] theorem FamilyMap.ext {A : FiniteFamily P S} {B : FiniteFamily Q S} {f g : FamilyMap A B}
    (h : f.toFun = g.toFun) : f = g := by cases f; cases g; cases h; rfl

def FamilyMap.id (A : FiniteFamily P S) : FamilyMap A A := ⟨fun x => x, FamilyDefinable.id A⟩

def FamilyMap.comp {A : FiniteFamily P S} {B : FiniteFamily Q S} {C : FiniteFamily R S}
    (g : FamilyMap B C) (f : FamilyMap A B) : FamilyMap A C :=
  ⟨g.toFun ∘ f.toFun, g.definable.comp f.definable⟩

def FamilyBijection.toFamilyMap {A : FiniteFamily P S} {B : FiniteFamily Q S} (f : FamilyBijection A B) : FamilyMap A B :=
  ⟨f.equiv, f.definable⟩

theorem FamilyDefinable.congr_fun {A : FiniteFamily P S} {B : FiniteFamily Q S}
    {f g : A.Carrier → B.Carrier} (hf : FamilyDefinable A B f) (h : ∀ a, f a = g a) : FamilyDefinable A B g :=
  (funext h) ▸ hf

end DiamondIntegral.Section3
