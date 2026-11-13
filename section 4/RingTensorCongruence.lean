import Mathlib.RingTheory.TensorProduct.Maps

/-! Tensor products of commutative rings transport across equivalences
of both factors and their coefficient ring, with explicit scalar squares. -/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace DiamondIntegral.Section4.RingTensorCongruence
variable {R S A B C D : Type*} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra S C] [Algebra S D]

def map (f : A →+* C) (g : B →+* D)
    (h : ∀ r, Algebra.TensorProduct.includeLeft (R := S) (S := S) (B := D) (f (algebraMap R A r)) =
      Algebra.TensorProduct.includeRight (R := S) (A := C) (g (algebraMap R B r))) :
    A ⊗[R] B →+* C ⊗[S] D := by
  let L : A →+* C ⊗[S] D := (Algebra.TensorProduct.includeLeft (R := S) (S := S) (B := D)).toRingHom.comp f
  let H : B →+* C ⊗[S] D := (Algebra.TensorProduct.includeRight (R := S) (A := C)).toRingHom.comp g
  letI : Algebra R (C ⊗[S] D) := (L.comp (algebraMap R A)).toAlgebra
  let F : A →ₐ[R] C ⊗[S] D := ⟨L, fun _ => rfl⟩
  let G : B →ₐ[R] C ⊗[S] D := ⟨H, fun r => (h r).symm⟩
  exact (Algebra.TensorProduct.lift F G (fun _ _ => Commute.all _ _)).toRingHom

theorem map_tmul (f : A →+* C) (g : B →+* D) (h) (a : A) (b : B) :
    map f g h (a ⊗ₜ[R] b) = f a ⊗ₜ[S] g b := by
  change (f a ⊗ₜ[S] 1) * (1 ⊗ₜ[S] g b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem hom_ext {T : Type*} [Semiring T] (f g : A ⊗[R] B →+* T)
    (h : ∀ a b, f (a ⊗ₜ[R] b) = g (a ⊗ₜ[R] b)) : f = g := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def congr (e : R ≃+* S) (f : A ≃+* C) (g : B ≃+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) : A ⊗[R] B ≃+* C ⊗[S] D := by
  have h : ∀ r, Algebra.TensorProduct.includeLeft (R := S) (S := S) (B := D) (f (algebraMap R A r)) =
      Algebra.TensorProduct.includeRight (R := S) (A := C) (g (algebraMap R B r)) := by
    intro r
    rw [hf, hg, AlgHom.commutes, AlgHom.commutes]
  have h' : ∀ s, Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := B) (f.symm (algebraMap S C s)) =
      Algebra.TensorProduct.includeRight (R := R) (A := A) (g.symm (algebraMap S D s)) := by
    intro s
    have hf' : f.symm (algebraMap S C s) = algebraMap R A (e.symm s) := by
      apply f.injective
      rw [RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]
    have hg' : g.symm (algebraMap S D s) = algebraMap R B (e.symm s) := by
      apply g.injective
      rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
    rw [hf', hg', AlgHom.commutes, AlgHom.commutes]
  let F := map f.toRingHom g.toRingHom h
  let G := map f.symm.toRingHom g.symm.toRingHom h'
  have hGF : G.comp F = RingHom.id _ := by
    apply hom_ext
    intro a b
    change G (F (a ⊗ₜ[R] b)) = a ⊗ₜ[R] b
    rw [show F (a ⊗ₜ[R] b) = f a ⊗ₜ[S] g b from map_tmul _ _ _ _ _,
      show G (f a ⊗ₜ[S] g b) = f.symm (f a) ⊗ₜ[R] g.symm (g b) from map_tmul _ _ _ _ _,
      RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  have hFG : F.comp G = RingHom.id _ := by
    apply hom_ext
    intro a b
    change F (G (a ⊗ₜ[S] b)) = a ⊗ₜ[S] b
    rw [show G (a ⊗ₜ[S] b) = f.symm a ⊗ₜ[R] g.symm b from map_tmul _ _ _ _ _,
      show F (f.symm a ⊗ₜ[R] g.symm b) = f (f.symm a) ⊗ₜ[S] g (g.symm b) from map_tmul _ _ _ _ _,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact RingEquiv.ofRingHom F G hFG hGF

theorem congr_tmul (e : R ≃+* S) (f : A ≃+* C) (g : B ≃+* D) (hf hg) (a : A) (b : B) :
    congr e f g hf hg (a ⊗ₜ[R] b) = f a ⊗ₜ[S] g b :=
  map_tmul f.toRingHom g.toRingHom (by
    intro r
    change (Algebra.TensorProduct.includeLeft : C →ₐ[S] C ⊗[S] D) (f (algebraMap R A r)) =
      Algebra.TensorProduct.includeRight (g (algebraMap R B r))
    rw [hf, hg, AlgHom.commutes, AlgHom.commutes]) a b

end DiamondIntegral.Section4.RingTensorCongruence
