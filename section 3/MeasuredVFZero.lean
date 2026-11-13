import «section 3».GammaVolumeForms
import «section 3».DefinableBijections
import «section 3».VFDimensionBridge
import Mathlib.CategoryTheory.Groupoid

/-! The degree-zero case of Definition 3.5 retains the Gamma form.
There is no exceptional point to discard, and the empty determinant is 1.
Thus its arrows are genuine form-preserving definable bijections. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure ZeroMeasuredVF (S : Set M) (hc : CanonicalStructure.IsCanonical (M := M)) where
  arity : ℕ
  domain : DefSet (rawMixedSpace (M := M) 0 arity) S
  finite : ∀ a, {t | (a, t) ∈ domain.carrier}.Finite
  form : GammaVolumeForm hc domain

variable {S : Set M} {hc : CanonicalStructure.IsCanonical (M := M)}

theorem ZeroMeasuredVF.finite_domain (A : ZeroMeasuredVF S hc) : A.domain.carrier.Finite := by
  apply (A.finite (fun i => i.elim0)).of_injOn (f := Prod.snd)
  · intro p hp
    have he : p.1 = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
    exact he ▸ hp
  · intro p _ q _ he
    exact Prod.ext (funext (fun i => i.elim0)) he

structure ZeroMeasuredVFHom (A B : ZeroMeasuredVF S hc) where
  bijection : DefinableBijection A.domain B.domain
  preserves : ∀ a, gammaFormValue A.form a = gammaFormValue B.form (bijection.map a)

namespace ZeroMeasuredVFHom
variable {A B D : ZeroMeasuredVF S hc}

@[ext] theorem ext {f g : ZeroMeasuredVFHom A B} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : ZeroMeasuredVF S hc) : ZeroMeasuredVFHom A A :=
  ⟨DefinableBijection.id A.domain, fun _ => rfl⟩

def comp (g : ZeroMeasuredVFHom B D) (f : ZeroMeasuredVFHom A B) : ZeroMeasuredVFHom A D :=
  ⟨g.bijection.comp f.bijection, fun a => (f.preserves a).trans (g.preserves (f.bijection.map a))⟩

def symm (f : ZeroMeasuredVFHom A B) : ZeroMeasuredVFHom B A where
  bijection := f.bijection.symm
  preserves b := by
    have h := f.preserves (f.bijection.symm.map b)
    rw [f.bijection.apply_symm_apply] at h
    exact h.symm

end ZeroMeasuredVFHom

instance : Groupoid (ZeroMeasuredVF S hc) where
  Hom := ZeroMeasuredVFHom
  id := ZeroMeasuredVFHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply ZeroMeasuredVFHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply ZeroMeasuredVFHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply ZeroMeasuredVFHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  inv_comp f := by
    apply ZeroMeasuredVFHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a
    exact f.bijection.apply_symm_apply a
  comp_inv f := by
    apply ZeroMeasuredVFHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a
    exact f.bijection.symm_apply_apply a

theorem zeroMeasuredVF_equation (A B : ZeroMeasuredVF S hc)
    (f : DefinableBijection A.domain B.domain) (a : A.domain) :
    gammaFormValue A.form a = gammaFormValue B.form (f.map a) ↔
      (gammaFormValue A.form a).val =
        (gammaFormValue B.form (f.map a)).val * Values.vfValueHom (1 : VFType (M := M)) := by
  simp only [map_one, mul_one, Subtype.val_inj]

end DiamondIntegral.Section3
