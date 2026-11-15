import «section 5».FiniteAffineVarietyPresentations

/-! Arbitrary reduced separated finite-type complex varieties have actual
finite affine presentations. The already proved geometric construction
is applied to the trivial compatible-root action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

structure ComplexVariety where
  scheme : Scheme
  toC : scheme ⟶ Spec (.of ℂ)
  locally_finite_type : LocallyOfFiniteType toC
  compact : CompactSpace scheme
  separated : IsSeparated toC
  reduced : AlgebraicGeometry.IsReduced scheme

def ComplexVariety.trivialObject (X : ComplexVariety) : EquivariantVariety.Object where
  scheme := X.scheme
  toC := X.toC
  locally_finite_type := X.locally_finite_type
  compact := X.compact
  separated := X.separated
  reduced := X.reduced
  action := 1
  overC _ := by simp
  finite_level := ⟨1,1,rfl⟩
  good x := by
    obtain ⟨U,hU,hx,_⟩ := exists_isAffineOpen_mem_and_subset (X := X.scheme) (x := x)
      (U := ⊤) (by trivial)
    exact ⟨U,hU,fun _ => hx⟩

structure ComplexVariety.Morphism (X Y : ComplexVariety) where
  hom : X.scheme ⟶ Y.scheme
  overC : hom ≫ Y.toC = X.toC

def ComplexVariety.Morphism.trivialMorphism {X Y : ComplexVariety} (f : X.Morphism Y) :
    EquivariantVariety.Morphism X.trivialObject Y.trivialObject where
  hom := f.hom
  overC := f.overC
  equivariant _ := by simp [ComplexVariety.trivialObject]

theorem ComplexVariety.finite_affine_presentation (X : ComplexVariety) :
    Nonempty (EquivariantVariety.AffineVarietyPresentation X.trivialObject) :=
  EquivariantVariety.finite_affine_variety_presentation X.trivialObject

end DiamondIntegral.Section5
