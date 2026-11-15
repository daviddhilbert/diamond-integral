import «section 5».VarietyMorphisms
import «section 5».ReducedImmersionLifts

/-! A geometric equivariant morphism whose image lies in a reduced
immersion factors through it as an actual equivariant complex morphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] Object.reduced
variable {X Y Z : Object}

def Morphism.factorThrough (i : Morphism Y X) [IsImmersion i.hom]
    (f : Morphism Z X) (h : Set.range f.hom ⊆ Set.range i.hom) : Morphism Z Y := by
  let L := reducedImmersionLift i.hom f.hom h
  have hL : L ≫ i.hom = f.hom := reducedImmersionLift_fac _ _ h
  exact {
    hom := L
    overC := by rw [← i.overC, ← Category.assoc, hL, f.overC]
    equivariant := fun g => by
      apply (cancel_mono i.hom).mp
      calc
        ((Z.action g).asIso.hom ≫ L) ≫ i.hom = (Z.action g).asIso.hom ≫ f.hom := by
          rw [Category.assoc, hL]
        _ = f.hom ≫ (X.action g).asIso.hom := f.equivariant g
        _ = (L ≫ i.hom) ≫ (X.action g).asIso.hom := by rw [hL]
        _ = L ≫ (i.hom ≫ (X.action g).asIso.hom) := Category.assoc _ _ _
        _ = L ≫ ((Y.action g).asIso.hom ≫ i.hom) :=
          congrArg (fun m => L ≫ m) (i.equivariant g).symm
        _ = (L ≫ (Y.action g).asIso.hom) ≫ i.hom := (Category.assoc _ _ _).symm }

@[reassoc]
theorem Morphism.factorThrough_fac (i : Morphism Y X) [IsImmersion i.hom]
    (f : Morphism Z X) (h : Set.range f.hom ⊆ Set.range i.hom) :
    (i.factorThrough f h).hom ≫ i.hom = f.hom := reducedImmersionLift_fac _ _ h

end DiamondIntegral.Section5.EquivariantVariety
