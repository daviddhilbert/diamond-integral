import «section 3».Grothendieck
import «section 3».VFCategories

/-! Definition 3.1 instantiated with VF[k] and its actual dimension.
Restriction preserves dimension bounds and the original RV labels. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4

noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [TopologicalSpace (Section2.VF M)] {S : Set M} {k : ℕ}

def VFObject.difference (U : VFObject (M := M) S k)
    (X : DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) S) :
    DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) S :=
  ⟨U.domain.carrier \ X.carrier, U.domain.definable.sdiff _ X.definable⟩

def VFScissor (A B C D : VFObject (M := M) S k) : Prop :=
  ∃ U : VFObject S k,
    ∃ X : DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) S,
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧
      B = U.restrict (U.difference X) (fun _ h => h.1) ∧ C = U ∧ D = VFObject.empty S k

def vfPresentation (S : Set M) (k : ℕ) : ScissorPresentation (VFObject (M := M) S k) where
  iso U V := Nonempty (U ≅ V)
  empty := VFObject.empty S k
  scissor := VFScissor

abbrev VFKPlus (S : Set M) (k : ℕ) := KPlus (vfPresentation (M := M) S k)
abbrev VFKGroup (S : Set M) (k : ℕ) := KGroup (vfPresentation (M := M) S k)

def vfClass (U : VFObject (M := M) S k) : VFKPlus S k := positiveClass (vfPresentation S k) U

theorem vfClass_iso {U V : VFObject (M := M) S k} (e : U ≅ V) : vfClass U = vfClass V :=
  positiveClass_iso (vfPresentation S k) ⟨e⟩

@[simp] theorem vfClass_empty : vfClass (VFObject.empty (M := M) S k) = 0 :=
  positiveClass_empty (vfPresentation S k)

theorem vfClass_scissor (U : VFObject (M := M) S k)
    (X : DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) S)
    (hX : X.carrier ⊆ U.domain.carrier) :
    vfClass (U.restrict X hX) + vfClass (U.restrict (U.difference X) (fun _ h => h.1)) =
      vfClass U := by
  have h : VFScissor (U.restrict X hX)
      (U.restrict (U.difference X) (fun _ h => h.1)) U (VFObject.empty S k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (vfPresentation S k) h
  change vfClass _ + vfClass _ = vfClass _ + vfClass _ at hs
  simpa only [vfClass_empty, add_zero] using hs

end DiamondIntegral.Section3
