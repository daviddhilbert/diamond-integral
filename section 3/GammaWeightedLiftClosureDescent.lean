import «section 3».GammaOriginalWeightedDifferentiableLift
import Section3.GammaClosureLaws
import IntegrationSection6.SmallGammaDefinableClosure

/-! Eliminate the internal definable-closure base from the weighted
polynomial lift. The Jacobian is calculated at original-base independent
points, rather than assuming independence over the enlarged real base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def gammaRVObjectClosure (U : GammaRVObject B n) (hU : (closureBase B).real ⊆ U.codes) :
    GammaRVObject (closureBase B) n where
  codes := U.codes
  real_contains := hU
  object := U.object
  domain_graph := U.domain_graph.mono (subset_closureBase B).1 (subset_closureBase B).2
  volume_graph := U.volume_graph.mono (subset_closureBase B).1 (subset_closureBase B).2

def gammaRVIsoClosure {U V : GammaRVObject B n}
    (hU : (closureBase B).real ⊆ U.codes) (hV : (closureBase B).real ⊆ V.codes)
    (e : GammaRVIso U V) : GammaRVIso (gammaRVObjectClosure U hU) (gammaRVObjectClosure V hV) where
  equiv := e.equiv
  graph := e.graph.mono (subset_closureBase B).1 (subset_closureBase B).2
  weight := e.weight
  leftFinite := e.leftFinite
  rightFinite := e.rightFinite

theorem gammaWeightedLift_closure_descent [CharZero (Section2.VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    {G : Type} [LinearOrderedCommGroupWithZero G] (w : Valuation (Section2.VF M) G)
    (hw : ∀ x y : Section2.VF M, VFValued.predV x y ↔ w x ≤ w y)
    {U V : GammaRVObject B n}
    (hCU : (closureBase B).real ⊆ U.codes) (hCV : (closureBase B).real ⊆ V.codes)
    (e : GammaRVIso U V)
    (hU : ∀ u : rvObjectDomain U.object, ∀ i, (gammaVolumeValue U u i).val ≠ iRVZero)
    (hV : ∀ v : rvObjectDomain V.object, ∀ i, (gammaVolumeValue V v i).val ≠ iRVZero) :
    ∃ f : GammaIso B U.lift V.lift,
      (∀ p : U.lift, ∃ u : rvObjectDomain U.object,
        u.val = p.val.2 ∧ (e.equiv u).val = (f.equiv p).val.2) ∧
      ∀ p : U.lift, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : Section2.VF M, HasMixedVFJacobianAt f.equiv p J ∧
          w J = (∏ i,w ((f.equiv p).val.1 i)) / ∏ i,w (p.val.1 i) := by
  let eC := gammaRVIsoClosure hCU hCV e
  obtain ⟨fC,hlabels,hJ⟩ := gammaOriginalWeightedDifferentiableLift hc hκ.le hs h00
    (closureBase_real_small hκ B hr hγ) hB w hw eC hU hV
  let f : GammaIso B U.lift V.lift :=
    ⟨fC.equiv,(DefinableOverBase.closureBase_iff B _ _).mp fC.graph⟩
  refine ⟨f,hlabels,fun p hp => ?_⟩
  letI : Valued (Section2.VF M) G := Valued.mk' w
  obtain ⟨L,hL⟩ := gammaOriginalIso_differentiable hc hκ.le hs hr hw U.lift_definable V.lift_definable f p hp
  refine ⟨(LinearMap.toMatrix' L).det,?_,hJ p L hL⟩
  obtain ⟨F,hF,hFL⟩ := hL
  exact ⟨F,hF,hFL.hasJacobianAt⟩

end DiamondIntegral.Section3
