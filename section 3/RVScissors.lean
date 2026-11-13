import «section 3».Grothendieck
import «section 3».RVCategories

/-! Definition 3.1 instantiated with the actual section 3 RV groupoid.
Scissors retain the chosen finite-to-one target on both pieces. These
fixed-degree quotients are additive; graded products are a separate step. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4

noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVObject.empty (S : Set M) (k : ℕ) : RVObject (M := M) S k where
  arity := 0
  domain := DefSet.empty (rawRVSpace 0) S
  volume := Map.empty (rawRVSpace 0) (rawRVSpace k) S
  finite _ := by
    have : IsEmpty (DefSet.empty (rawRVSpace (M := M) 0) S) := ⟨fun a => a.property⟩
    exact Set.toFinite _
  nonzero a := False.elim a.property

def RVObject.restrict (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    RVObject S k where
  arity := U.arity
  domain := A
  volume := U.volume.comp (Map.inclusion hA)
  finite := U.finite.comp (Map.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun u : U.domain => u.val) he)))
  nonzero a i := U.nonzero (Map.inclusion hA a) i

def RVObject.difference (U : RVObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.arity) S) :
    DefSet (rawRVSpace (M := M) U.arity) S :=
  ⟨U.domain.carrier \ X.carrier, U.domain.definable.sdiff _ X.definable⟩

def RVScissor (A B C D : RVObject (M := M) S k) : Prop :=
  ∃ U : RVObject S k, ∃ X : DefSet (rawRVSpace (M := M) U.arity) S,
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧
      B = U.restrict (U.difference X) (fun _ h => h.1) ∧ C = U ∧ D = RVObject.empty S k

def rvPresentation (S : Set M) (k : ℕ) : ScissorPresentation (RVObject (M := M) S k) where
  iso U V := Nonempty (U ≅ V)
  empty := RVObject.empty S k
  scissor := RVScissor

abbrev RVKPlus (S : Set M) (k : ℕ) := KPlus (rvPresentation (M := M) S k)
abbrev RVKGroup (S : Set M) (k : ℕ) := KGroup (rvPresentation (M := M) S k)

def rvClass (U : RVObject (M := M) S k) : RVKPlus S k := positiveClass (rvPresentation S k) U

theorem rvClass_iso {U V : RVObject (M := M) S k} (e : U ≅ V) : rvClass U = rvClass V :=
  positiveClass_iso (rvPresentation S k) ⟨e⟩

@[simp] theorem rvClass_empty : rvClass (RVObject.empty (M := M) S k) = 0 :=
  positiveClass_empty (rvPresentation S k)

theorem rvClass_scissor (U : RVObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.arity) S) (hX : X.carrier ⊆ U.domain.carrier) :
    rvClass (U.restrict X hX) + rvClass (U.restrict (U.difference X) (fun _ h => h.1)) =
      rvClass U := by
  have h : RVScissor (U.restrict X hX)
      (U.restrict (U.difference X) (fun _ h => h.1)) U (RVObject.empty S k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (rvPresentation S k) h
  change rvClass _ + rvClass _ = rvClass _ + rvClass _ at hs
  simpa only [rvClass_empty, add_zero] using hs

end DiamondIntegral.Section3
