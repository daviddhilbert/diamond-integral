import «section 6».AffineLiftHeadExceptions

/-! Prescribed full total Jacobians for the actual affine extension,
outside a set of whole labels smaller than the head dimension. -/

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

theorem exists_affineLift_small_head_jacobian_exception
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
      (liftLabelMap (measuredRVHead hc V (productLeft (k+1) m) hV).object (F p)) ∘ productRight (k+1) m)
    (hD : ∀ p L, HasMixedVFDerivativeAt F p L → (D p).val 0 = (LinearMap.toMatrix' L).det)
    (hCorrection : ∀ p, affineTailCorrectionGood Valued.v (a p).val (b p).val
      ((D p).val 0) ((c p).val 0)) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p : rvLift U.object, (f p).val.2 =
        (F (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU p)).val.2) ∧
      ∃ E : DefSet (rawRVSpace (M := M) U.object.arity) S,
        E.carrier ⊆ U.object.domain.carrier ∧ rvDim E < k+1 ∧
          ∀ p : rvLift U.object, p.val.2 ∉ E.carrier →
            ∃ L, HasMixedVFDerivativeAt f p L ∧ (LinearMap.toMatrix' L).det =
              (c (rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU p)).val 0 := by
  obtain ⟨f,hf,heq,E,hE,hDim,hGood⟩ := exists_affineLift_small_head_exception
    h00 hc hκ hs hsmall hΓ hv U V hU hV F hF hFD a b D c j ha hb haRV hbRV
  refine ⟨f,hf,fun p => congrArg Prod.snd (heq p),E,hE,hDim,fun p hp => ?_⟩
  let H := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU
  let s x := affineTailSlopesForHead Valued.v (a x).val (b x).val j ((D x).val 0) ((c x).val 0)
  obtain ⟨L,hL⟩ := hGood p hp
  obtain ⟨L₁,hL₁⟩ := hFD (H p)
  have hdet := det_affineLift_of_mixed_derivatives
    ⟨U.object,U.finiteVolume⟩ ⟨V.object,V.finiteVolume⟩ hU hV F f
    (fun x => (a x).val) (fun x => (b x).val) s
    (fun q => congrArg Prod.fst (heq q)) p L₁ L hL₁ hL
  refine ⟨L,hL,?_⟩
  rw [hdet,← hD (H p) L₁ hL₁]
  exact (affineTailSlopesForHead_spec Valued.v (a (H p)).val (b (H p)).val j
    ((D (H p)).val 0) ((c (H p)).val 0) (ha (H p)) (hb (H p))).2 (hCorrection (H p))

end DiamondIntegral.Section6
