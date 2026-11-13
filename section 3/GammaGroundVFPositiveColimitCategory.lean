import «section 3».GammaGroundVFPositiveColimit
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-! The dimension filtration over Gamma ground parameters has its actual
colimit in additive commutative monoids. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M))

def gammaGroundVFPositiveDiagram : ℕ ⥤ AddCommMonCat where
  obj k := AddCommMonCat.of (GammaGroundVFKPlus hc ground k)
  map f := AddCommMonCat.ofHom (gammaGroundVFRaiseKPlus (leOfHom f))
  map_id k := by
    apply AddCommMonCat.hom_ext
    exact gammaGroundVFRaiseKPlus_refl
  map_comp f g := by
    apply AddCommMonCat.hom_ext
    exact (gammaGroundVFRaiseKPlus_comp (leOfHom f) (leOfHom g)).symm

def gammaGroundVFPositiveCocone : Cocone (gammaGroundVFPositiveDiagram hc ground) where
  pt := AddCommMonCat.of (GammaGroundFiniteVFKPlus hc ground)
  ι := {
    app := fun _ => AddCommMonCat.ofHom gammaGroundVFToFiniteKPlus
    naturality := by
      intro k l f
      apply AddCommMonCat.hom_ext
      exact gammaGroundVFToFiniteKPlus_raise (leOfHom f) }

def gammaGroundVFCompatibleOfCocone (s : Cocone (gammaGroundVFPositiveDiagram hc ground)) :
    CompatibleGammaGroundVFPositiveMaps hc ground s.pt where
  map k := (s.ι.app k).hom
  compatible k l hkl := by
    have h := congrArg (fun f : (gammaGroundVFPositiveDiagram hc ground).obj k ⟶ s.pt => f.hom)
      (s.w (homOfLE hkl))
    exact h

def gammaGroundVFPositiveIsColimit : IsColimit (gammaGroundVFPositiveCocone hc ground) where
  desc s := AddCommMonCat.ofHom (gammaGroundVFColimitLift (gammaGroundVFCompatibleOfCocone hc ground s))
  fac s k := by
    apply AddCommMonCat.hom_ext
    exact gammaGroundVFColimitLift_inclusion (gammaGroundVFCompatibleOfCocone hc ground s) k
  uniq s m hm := by
    apply AddCommMonCat.hom_ext
    apply gammaGroundVFColimitLift_unique (gammaGroundVFCompatibleOfCocone hc ground s) m.hom
    intro k
    exact congrArg (fun f : (gammaGroundVFPositiveDiagram hc ground).obj k ⟶ s.pt => f.hom) (hm k)

end DiamondIntegral.Section3
