import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Basic.Complex.Basic

/-! The actual complex overlap algebra of two affine pieces with the
same input coordinates. Its universal property is proved explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
open scoped TensorProduct
variable {S A B : Type} [CommRing S] [CommRing A] [CommRing B]
variable [Algebra ℂ S] [Algebra ℂ A] [Algebra ℂ B]

def overlapIdeal (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) : Ideal (A ⊗[ℂ] B) :=
  Ideal.span (Set.range (fun s =>
    (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) (f s) -
      (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B) (g s)))

abbrev OverlapAlgebra (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) := (A ⊗[ℂ] B) ⧸ overlapIdeal f g

def overlapLeft (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) : A →ₐ[ℂ] OverlapAlgebra f g :=
  (Ideal.Quotient.mkₐ ℂ (overlapIdeal f g)).comp Algebra.TensorProduct.includeLeft

def overlapRight (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) : B →ₐ[ℂ] OverlapAlgebra f g :=
  (Ideal.Quotient.mkₐ ℂ (overlapIdeal f g)).comp Algebra.TensorProduct.includeRight

theorem overlap_commutes (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) :
    (overlapLeft f g).comp f = (overlapRight f g).comp g := by
  ext s
  have hmem : (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) (f s) -
      (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B) (g s) ∈ overlapIdeal f g :=
    Ideal.subset_span (Set.mem_range_self s)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem overlapAlgebra_finiteType [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B]
    (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) : Algebra.FiniteType ℂ (OverlapAlgebra f g) := by
  letI : Algebra.FiniteType ℂ (A ⊗[ℂ] B) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℂ A)
      (inferInstance : Algebra.FiniteType A (A ⊗[ℂ] B))
  infer_instance

variable {R : Type} [CommRing R] [Algebra ℂ R]

def overlapLift (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B)
    (u : A →ₐ[ℂ] R) (v : B →ₐ[ℂ] R) (he : u.comp f = v.comp g) :
    OverlapAlgebra f g →ₐ[ℂ] R :=
  Ideal.Quotient.liftₐ _ (Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)) (by
    change overlapIdeal f g ≤ RingHom.ker (Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) (f s) -
        (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B) (g s)) = 0
    simp only [map_sub, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
    exact sub_eq_zero.mpr (AlgHom.congr_fun he s))

theorem overlapLift_left (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B)
    (u : A →ₐ[ℂ] R) (v : B →ₐ[ℂ] R) (he : u.comp f = v.comp g) (a : A) :
    overlapLift f g u v he (overlapLeft f g a) = u a := by
  change Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
    ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) a) = u a
  simp

theorem overlapLift_right (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B)
    (u : A →ₐ[ℂ] R) (v : B →ₐ[ℂ] R) (he : u.comp f = v.comp g) (b : B) :
    overlapLift f g u v he (overlapRight f g b) = v b := by
  change Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
    ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B) b) = v b
  simp

end DiamondIntegral.Section5
