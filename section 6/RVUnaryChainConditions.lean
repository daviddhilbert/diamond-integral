import «section 6».RVUnaryFactorizations

/-! Every intermediate object of a one-coordinate factorization retains
finite volume and the double bounds. These conditions are recorded on
the entire actual chain, rather than just its endpoints. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVObjectDoublyBounded (U : RVObject (M := M) S k) : Prop :=
  RVValueDoublyBounded U.domain.carrier ∧ RVValueDoublyBounded (Set.range U.value)

def RVUnaryChain.finiteVolume {U V : RVObject (M := M) S k} : RVUnaryChain S k U V → Prop
  | .identity U => U.volume.FiniteFibres
  | .step _ _ _ tail => U.volume.FiniteFibres ∧ tail.finiteVolume

def RVUnaryChain.doublyBounded {U V : RVObject (M := M) S k} : RVUnaryChain S k U V → Prop
  | .identity U => RVObjectDoublyBounded U
  | .step _ _ _ tail => RVObjectDoublyBounded U ∧ tail.doublyBounded

theorem lemma_6_29_finite_degree_one {U V : RVObject (M := M) S 1}
    (e : U ≅ V) (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres) :
    ∃ T : RVUnaryChain S 1 U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume := by
  exact ⟨.step 0 e (rvUnaryRelativeAt_one e.hom.map) (.identity V),rfl,hU,hV⟩

theorem lemma_6_29_doublyBounded_degree_one {U V : RVObject (M := M) S 1}
    (e : U ≅ V) (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres)
    (hUB : RVObjectDoublyBounded U) (hVB : RVObjectDoublyBounded V) :
    ∃ T : RVUnaryChain S 1 U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume ∧ T.doublyBounded := by
  exact ⟨.step 0 e (rvUnaryRelativeAt_one e.hom.map) (.identity V),rfl,⟨hU,hV⟩,hUB,hVB⟩

def MeasuredRVUnaryChain.doublyBounded {U V : MeasuredRVObject (M := M) S k} :
    MeasuredRVUnaryChain S k U V → Prop
  | .identity U => U.doublyBounded
  | .step _ _ _ tail => U.doublyBounded ∧ tail.doublyBounded

theorem lemma_6_29_measured_doublyBounded_degree_one
    {U V : MeasuredRVObject (M := M) S 1} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ T : MeasuredRVUnaryChain S 1 U V, T.iso.iso.hom.map = e.iso.hom.map ∧ T.doublyBounded := by
  exact ⟨.step 0 e (rvUnaryRelativeAt_one e.iso.hom.map) (.identity V),rfl,hU,hV⟩

end DiamondIntegral.Section6
