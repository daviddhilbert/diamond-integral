import «section 6».MeasuredRVIsomorphisms

/-! Actual relatively unary RV chains and their measured counterparts.
In degree one every isomorphism is one permitted coordinate step; this
is the complete degree-one case of 6.29, with no partition hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVUnaryRelativeAt {U V : RVObject (M := M) S k} (f : Map U.domain V.domain) (i : Fin k) : Prop :=
  ∀ u : U.domain, ∀ j : Fin k, j ≠ i → V.value (f u) j = U.value u j

theorem rvUnaryRelativeAt_one {U V : RVObject (M := M) S 1} (f : Map U.domain V.domain) :
    RVUnaryRelativeAt f 0 := by
  intro u j hj
  exact (hj (Subsingleton.elim _ _)).elim

inductive RVUnaryChain (S : Set M) (k : ℕ) : RVObject (M := M) S k → RVObject (M := M) S k → Type where
  | identity (U : RVObject (M := M) S k) : RVUnaryChain S k U U
  | step {U V W : RVObject (M := M) S k} (i : Fin k) (e : U ≅ V)
      (unary : RVUnaryRelativeAt e.hom.map i) (tail : RVUnaryChain S k V W) : RVUnaryChain S k U W

def RVUnaryChain.iso {U V : RVObject (M := M) S k} : RVUnaryChain S k U V → (U ≅ V)
  | .identity U => Iso.refl U
  | .step _ e _ tail => e ≪≫ tail.iso

theorem lemma_6_29_degree_one {U V : RVObject (M := M) S 1} (e : U ≅ V) :
    ∃ T : RVUnaryChain S 1 U V, T.iso.hom.map = e.hom.map := by
  refine ⟨.step 0 e (rvUnaryRelativeAt_one e.hom.map) (.identity V),?_⟩
  apply Map.ext
  intro u
  rfl

inductive MeasuredRVUnaryChain (S : Set M) (k : ℕ) :
    MeasuredRVObject (M := M) S k → MeasuredRVObject (M := M) S k → Type where
  | identity (U : MeasuredRVObject (M := M) S k) : MeasuredRVUnaryChain S k U U
  | step {U V W : MeasuredRVObject (M := M) S k} (i : Fin k) (e : MeasuredRVIso U V)
      (unary : RVUnaryRelativeAt e.iso.hom.map i) (tail : MeasuredRVUnaryChain S k V W) :
      MeasuredRVUnaryChain S k U W

def MeasuredRVUnaryChain.iso {U V : MeasuredRVObject (M := M) S k} :
    MeasuredRVUnaryChain S k U V → MeasuredRVIso U V
  | .identity U => .identity U
  | .step _ e _ tail => e.comp tail.iso

theorem lemma_6_29_measured_degree_one {U V : MeasuredRVObject (M := M) S 1} (e : MeasuredRVIso U V) :
    ∃ T : MeasuredRVUnaryChain S 1 U V, T.iso.iso.hom.map = e.iso.hom.map := by
  refine ⟨.step 0 e (rvUnaryRelativeAt_one e.iso.hom.map) (.identity V),?_⟩
  apply Map.ext
  intro u
  rfl

end DiamondIntegral.Section6
