import «section 3».GammaGroundFiniteFamilies
/-! Functions between finite definable families carry their complete
branch graphs. Bijections supply such maps without changing parameters. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q R : Space LRV M}

structure GammaGroundFamilyMap (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q) where
  toFun : A.Carrier → B.Carrier
  definable : GammaGroundFamilyDefinable A B toFun

@[ext] theorem GammaGroundFamilyMap.ext {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q} {f g : GammaGroundFamilyMap A B}
    (h : f.toFun = g.toFun) : f = g := by cases f; cases g; cases h; rfl

def GammaGroundFamilyMap.id (A : GammaGroundFiniteFamily hc ground P) : GammaGroundFamilyMap A A := ⟨fun x => x, GammaGroundFamilyDefinable.id A⟩

def GammaGroundFamilyMap.comp {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q} {C : GammaGroundFiniteFamily hc ground R}
    (g : GammaGroundFamilyMap B C) (f : GammaGroundFamilyMap A B) : GammaGroundFamilyMap A C :=
  ⟨g.toFun ∘ f.toFun, g.definable.comp f.definable⟩

def GammaGroundFamilyBijection.toFamilyMap {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q} (f : GammaGroundFamilyBijection A B) : GammaGroundFamilyMap A B :=
  ⟨f.equiv, f.definable⟩

theorem GammaGroundFamilyDefinable.congr_fun {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q}
    {f g : A.Carrier → B.Carrier} (hf : GammaGroundFamilyDefinable A B f) (h : ∀ a, f a = g a) : GammaGroundFamilyDefinable A B g :=
  (funext h) ▸ hf

end DiamondIntegral.Section3
