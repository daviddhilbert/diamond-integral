import «section 5».EquivariantVarietyRing

/-! Actual equivariant morphism and isomorphism composition over the
complex base, used by the geometric comparison maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
variable {X Y Z : Object}

def Morphism.id (X : Object) : Morphism X X where
  hom := 𝟙 _
  overC := Category.id_comp _
  equivariant := fun _ => by simp

def Morphism.comp (g : Morphism Y Z) (f : Morphism X Y) : Morphism X Z where
  hom := f.hom ≫ g.hom
  overC := by rw [Category.assoc, g.overC, f.overC]
  equivariant h := by
    rw [← Category.assoc, f.equivariant, Category.assoc, g.equivariant, ← Category.assoc]

@[instance]
theorem Morphism.comp_immersion (g : Morphism Y Z) (f : Morphism X Y)
    [IsImmersion f.hom] [IsImmersion g.hom] : IsImmersion (g.comp f).hom :=
  inferInstanceAs (IsImmersion (f.hom ≫ g.hom))

def Iso.toMorphism (f : Iso X Y) : Morphism X Y := ⟨f.iso.hom, f.overC, f.equivariant⟩

def Iso.refl (X : Object) : Iso X X := ⟨CategoryTheory.Iso.refl _, Category.id_comp _, fun _ => by simp⟩

def Iso.symm (f : Iso X Y) : Iso Y X where
  iso := f.iso.symm
  overC := by
    change f.iso.inv ≫ X.toC = Y.toC
    rw [← f.overC, ← Category.assoc, f.iso.inv_hom_id, Category.id_comp]
  equivariant h := by
    apply (cancel_mono f.iso.hom).mp
    calc
      ((Y.action h).asIso.hom ≫ f.iso.inv) ≫ f.iso.hom = (Y.action h).asIso.hom := by simp
      _ = f.iso.inv ≫ (f.iso.hom ≫ (Y.action h).asIso.hom) := by simp
      _ = f.iso.inv ≫ ((X.action h).asIso.hom ≫ f.iso.hom) :=
        congrArg (fun m => f.iso.inv ≫ m) (f.equivariant h).symm
      _ = (f.iso.inv ≫ (X.action h).asIso.hom) ≫ f.iso.hom := (Category.assoc _ _ _).symm

def Iso.trans (f : Iso X Y) (g : Iso Y Z) : Iso X Z where
  iso := f.iso ≪≫ g.iso
  overC := (Morphism.comp g.toMorphism f.toMorphism).overC
  equivariant := (Morphism.comp g.toMorphism f.toMorphism).equivariant

end DiamondIntegral.Section5.EquivariantVariety
