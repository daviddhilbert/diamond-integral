import «section 3».GammaGroundMeasuredVFData
import «section 3».GammaGroundBijections
import Mathlib.CategoryTheory.Groupoid

/-! In degree zero the measured VF arrows are genuine same-ground
bijections preserving the full Gamma form at every point. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

abbrev GammaGroundZeroMeasuredVF (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := GammaGroundMeasuredVFData hc ground 0

structure GammaGroundZeroMeasuredVFHom (U V : GammaGroundZeroMeasuredVF hc ground) where
  bijection : GammaGroundBijection U.domain V.domain
  preserves : ∀ a, gammaGroundFormValue U.form a = gammaGroundFormValue V.form (bijection.map a)

@[ext] theorem GammaGroundZeroMeasuredVFHom.ext {U V : GammaGroundZeroMeasuredVF hc ground}
    {f g : GammaGroundZeroMeasuredVFHom U V} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def GammaGroundZeroMeasuredVFHom.id (U : GammaGroundZeroMeasuredVF hc ground) : GammaGroundZeroMeasuredVFHom U U :=
  ⟨GammaGroundBijection.id U.domain, fun _ => rfl⟩

def GammaGroundZeroMeasuredVFHom.comp {U V W : GammaGroundZeroMeasuredVF hc ground}
    (g : GammaGroundZeroMeasuredVFHom V W) (f : GammaGroundZeroMeasuredVFHom U V) : GammaGroundZeroMeasuredVFHom U W :=
  ⟨g.bijection.comp f.bijection, fun a => (f.preserves a).trans (g.preserves (f.bijection.map a))⟩

def GammaGroundZeroMeasuredVFHom.symm {U V : GammaGroundZeroMeasuredVF hc ground}
    (f : GammaGroundZeroMeasuredVFHom U V) : GammaGroundZeroMeasuredVFHom V U where
  bijection := f.bijection.symm
  preserves b := by
    have h := f.preserves (f.bijection.symm.map b)
    rw [GammaGroundBijection.symm, GammaGroundMap.apply_inverse] at h
    exact h.symm

instance gammaGroundZeroMeasuredVFGroupoid : Groupoid (GammaGroundZeroMeasuredVF hc ground) where
  Hom := GammaGroundZeroMeasuredVFHom
  id := GammaGroundZeroMeasuredVFHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundZeroMeasuredVFHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundZeroMeasuredVFHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundZeroMeasuredVFHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  inv_comp f := by apply GammaGroundZeroMeasuredVFHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.bijection.map.apply_inverse f.bijection.bijective a
  comp_inv f := by apply GammaGroundZeroMeasuredVFHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.bijection.map.inverse_apply f.bijection.bijective a

end DiamondIntegral.Section3
