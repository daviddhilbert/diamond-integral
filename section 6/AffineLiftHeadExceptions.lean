import «section 6».MixedAffineTailDifferentiability
import «section 6».AffineTailSlopeMaps
import «section 6».MeasuredRVHeads
import Section9.AffineLift

/-! An actual affine extension of an everywhere differentiable head
lift has full derivatives off a set of whole old labels whose RV
dimension is strictly smaller than the head degree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {k m : ℕ}

theorem exists_affineLift_small_head_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U V : MeasuredRVObject (M := M) S ((k+1)+m))
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (F : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
      (rvLift (measuredRVHead hc V (productLeft (k+1) m) hV).object))
    (hF : Function.Bijective F) (hFD : ∀ p, ∃ L, HasMixedVFDerivativeAt F p L)
    (a b : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
      (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
      (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0)
    (haRV : ∀ p, tupleRV (a p).val = U.object.value
      (liftLabelMap (measuredRVHead hc U (productLeft (k+1) m) hU).object p) ∘ productRight (k+1) m)
    (hbRV : ∀ p, tupleRV (b p).val = V.object.value
      (liftLabelMap (measuredRVHead hc V (productLeft (k+1) m) hV).object (F p)) ∘ productRight (k+1) m) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p : rvLift U.object,
        let x := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU p
        (f p).val = (productTuple (F x).val.1
          (affineTail (a x).val (b x).val
            (affineTailSlopesForHead Valued.v (a x).val (b x).val j ((D x).val 0) ((c x).val 0))
            (p.val.1 ∘ productRight (k+1) m)),(F x).val.2)) ∧
      ∃ E : DefSet (rawRVSpace (M := M) U.object.arity) S,
        E.carrier ⊆ U.object.domain.carrier ∧ rvDim E < k+1 ∧
          ∀ p : rvLift U.object, p.val.2 ∉ E.carrier → ∃ L, HasMixedVFDerivativeAt f p L := by
  obtain ⟨s,hslope⟩ := exists_affineTailSlopesMap Valued.v hv a b D c j ha hb
  obtain ⟨f,hf,heq⟩ := exists_affineLift_of_headLift Valued.v hv
    ⟨U.object,U.finiteVolume⟩ ⟨V.object,V.finiteVolume⟩ hU hV F hF a b D c j ha hb haRV hbRV
  let A := rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object
  let coeff : Fin 3 → Map A (DefSet.univ (rawVFSpace (M := M) m) S) := ![a,b,s]
  obtain ⟨E,hE,hDim,hGood⟩ := exists_small_rv_labels_for_tuple_differentiability
    h00 hc hκ hs hsmall hΓ hv (measuredRVHead hc U (productLeft (k+1) m) hU)
    (fun _ : Fin 3 => m) coeff
  refine ⟨f,hf,heq,E,hE,hDim,fun p hp => ?_⟩
  let x := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU p
  apply mixedDerivative_affineTail_of_coefficient_derivatives U V hU hV F f a b s
  · intro q
    dsimp only
    rw [hslope]
    exact heq q
  · exact hFD x
  · exact hGood x hp 0
  · exact hGood x hp 1
  · exact hGood x hp 2

end DiamondIntegral.Section6
