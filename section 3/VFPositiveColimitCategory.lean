import «section 3».VFPositiveColimit
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-! The dimension filtration has the asserted categorical colimit in
additive commutative monoids. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M)

def vfPositiveDiagram : ℕ ⥤ AddCommMonCat where
  obj k := AddCommMonCat.of (VFKPlus (M := M) (C.base : Set M) k)
  map f := AddCommMonCat.ofHom (vfRaiseKPlus (leOfHom f))
  map_id k := by
    apply AddCommMonCat.hom_ext
    exact vfRaiseKPlus_refl
  map_comp f g := by
    apply AddCommMonCat.hom_ext
    exact (vfRaiseKPlus_comp (leOfHom f) (leOfHom g)).symm

variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def vfPositiveCocone : Cocone (vfPositiveDiagram C) where
  pt := AddCommMonCat.of (VFPositiveSemiring C hc hv)
  ι := {
    app := fun _ => AddCommMonCat.ofHom (vfKPlusToSemiring C hc hv)
    naturality := by
      intro k l f
      apply AddCommMonCat.hom_ext
      exact vfKPlusToSemiring_raise C hc hv (leOfHom f) }

def vfCompatibleOfCocone (s : Cocone (vfPositiveDiagram C)) : CompatibleVFPositiveMaps C (A := s.pt) where
  map k := (s.ι.app k).hom
  compatible k l hkl := by
    have h := congrArg (fun f : (vfPositiveDiagram C).obj k ⟶ s.pt => f.hom) (s.w (homOfLE hkl))
    exact h

def vfPositiveIsColimit : IsColimit (vfPositiveCocone C hc hv) where
  desc s := AddCommMonCat.ofHom (vfColimitLift C hc hv (vfCompatibleOfCocone C s))
  fac s k := by
    apply AddCommMonCat.hom_ext
    exact vfColimitLift_inclusion C hc hv (vfCompatibleOfCocone C s) k
  uniq s m hm := by
    apply AddCommMonCat.hom_ext
    apply vfColimitLift_unique C hc hv (vfCompatibleOfCocone C s) m.hom
    intro k
    exact congrArg (fun f : (vfPositiveDiagram C).obj k ⟶ s.pt => f.hom) (hm k)

end DiamondIntegral.Section3
