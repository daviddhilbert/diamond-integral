import «section 3».Grothendieck
import Mathlib.Algebra.DirectSum.Basic

/-! Additive group completion commutes with the genuine graded direct sum.
No cancellation is required of any positive component. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
universe u v w
variable {I : Type u} [DecidableEq I] (A : I → Type v) [∀ i, AddCommMonoid (A i)]

open Algebra.GrothendieckAddGroup

theorem completionAddHom_ext {B : Type w} [AddCommMonoid B] {G : Type v} [AddCommGroup G]
    {f g : Algebra.GrothendieckAddGroup B →+ G} (h : ∀ b, f (of b) = g (of b)) : f = g := by
  apply (lift (M := B) (G := G)).symm.injective
  rw [lift_symm_apply, lift_symm_apply]
  exact AddMonoidHom.ext h

def completionDirectSumForward : Algebra.GrothendieckAddGroup (DirectSum I A) →+
    DirectSum I (fun i => Algebra.GrothendieckAddGroup (A i)) :=
  lift (DirectSum.toAddMonoid (fun i => (DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i).comp of))

def completionDirectSumBackward : DirectSum I (fun i => Algebra.GrothendieckAddGroup (A i)) →+
    Algebra.GrothendieckAddGroup (DirectSum I A) :=
  DirectSum.toAddMonoid (fun i => lift (of.comp (DirectSum.of A i)))

@[simp] theorem completionDirectSumForward_of (i : I) (a : A i) :
    completionDirectSumForward A (of (DirectSum.of A i a)) =
      DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i (of a) := by
  rw [completionDirectSumForward, lift_apply_of, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]

@[simp] theorem completionDirectSumBackward_of (i : I) (a : A i) :
    completionDirectSumBackward A (DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i (of a)) =
      of (DirectSum.of A i a) := by
  rw [completionDirectSumBackward, DirectSum.toAddMonoid_of, lift_apply_of, AddMonoidHom.comp_apply]

def completionDirectSumEquiv : Algebra.GrothendieckAddGroup (DirectSum I A) ≃+
    DirectSum I (fun i => Algebra.GrothendieckAddGroup (A i)) := by
  let F := completionDirectSumForward A
  let B := completionDirectSumBackward A
  have hBF : B.comp F = AddMonoidHom.id _ := by
    apply completionAddHom_ext
    intro a
    have h : B.comp (F.comp of) = of := by
      apply DirectSum.addHom_ext
      intro i a
      change B (F (of (DirectSum.of A i a))) = of (DirectSum.of A i a)
      rw [completionDirectSumForward_of, completionDirectSumBackward_of]
    exact DFunLike.congr_fun h a
  have hFB : F.comp B = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i a
    have h : (F.comp B).comp (DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i) =
        DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i := by
      apply completionAddHom_ext
      intro a
      change F (B (DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i (of a))) = _
      rw [completionDirectSumBackward_of, completionDirectSumForward_of]
    exact DFunLike.congr_fun h a
  exact {
    toFun := F
    invFun := B
    left_inv := DFunLike.congr_fun hBF
    right_inv := DFunLike.congr_fun hFB
    map_add' := F.map_add }

@[simp] theorem completionDirectSumEquiv_of (i : I) (a : A i) :
    completionDirectSumEquiv A (of (DirectSum.of A i a)) =
      DirectSum.of (fun i => Algebra.GrothendieckAddGroup (A i)) i (of a) := completionDirectSumForward_of A i a

end DiamondIntegral.Section3
