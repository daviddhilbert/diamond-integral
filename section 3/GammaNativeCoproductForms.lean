import «section 3».GammaNativeCombinedWeights
import «section 3».GammaGroundMeasuredRVCoproducts
import «section 5».Completed18RVOperations

/-! Arbitrary Gamma forms assemble on the native tagged coproduct.
The existing literal tag and volume formulas are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaNativeTaggedDomain (U V : GammaObjectAt B Set.univ n) :=
  (gammaGroundRVLeftTag (Section5.nativeRVGroundDomain (hc := hc) U) (rvObjectArity V.object.obj)).image.union
    (gammaGroundRVRightTag (Section5.nativeRVGroundDomain (hc := hc) V) (rvObjectArity U.object.obj)).image

theorem gammaNativeCoprod_domain (U V : GammaObjectAt B Set.univ n) :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaCoprodAt U V)).carrier =
      (gammaNativeTaggedDomain (hc := hc) U V).carrier := by
  rw [Section5.nativeRVGroundDomain_carrier]
  ext x
  change ((∃ u : rvObjectDomain U.object.obj,@rvLeftTag M N hN _ _ u.val=x) ∨
    (∃ v : rvObjectDomain V.object.obj,@rvRightTag M N hN _ _ v.val=x)) ↔
    ((∃ u : Section5.nativeRVGroundDomain (hc := hc) U,rvLeftTag _ u.val=x) ∨
      ∃ v : Section5.nativeRVGroundDomain (hc := hc) V,rvRightTag _ v.val=x)
  constructor
  · rintro (⟨u,hu⟩|⟨v,hv⟩)
    · exact Or.inl ⟨(Section5.nativeRVGroundDomainEquiv U).symm u,
        (@Section5.rvLeftTag_normalized M sM hM (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) u.val).symm.trans hu⟩
    · exact Or.inr ⟨(Section5.nativeRVGroundDomainEquiv V).symm v,
        (@Section5.rvRightTag_normalized M sM hM (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) v.val).symm.trans hv⟩
  · rintro (⟨u,hu⟩|⟨v,hv⟩)
    · exact Or.inl ⟨Section5.nativeRVGroundDomainEquiv U u,(@Section5.rvLeftTag_normalized M sM hM (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) u.val).trans hu⟩
    · exact Or.inr ⟨Section5.nativeRVGroundDomainEquiv V v,(@Section5.rvRightTag_normalized M sM hM (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) v.val).trans hv⟩

def gammaNativeCoprodForm (U V : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V)) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaCoprodAt U V)) :=
  ((ω.comp (gammaGroundRVUntagLeft (Section5.nativeRVGroundDomain U) (rvObjectArity V.object.obj))).union
    (η.comp (gammaGroundRVUntagRight (Section5.nativeRVGroundDomain V) (rvObjectArity U.object.obj)))).comp
      (GammaGroundBijection.ofCarrierEq (gammaNativeCoprod_domain (hc := hc) U V)).map

theorem gammaNativeCoprodForm_left (U V : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (u : Section5.nativeRVGroundDomain (hc := hc) U)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaCoprodAt U V))
    (hw : w.val = rvLeftTag (rvObjectArity V.object.obj) u.val) :
    gammaGroundFormValue (gammaNativeCoprodForm U V ω η) w = gammaGroundFormValue ω u := by
  let A := Section5.nativeRVGroundDomain (hc := hc) U
  let D := Section5.nativeRVGroundDomain (hc := hc) V
  have he : (GammaGroundBijection.ofCarrierEq (gammaNativeCoprod_domain (hc := hc) U V)).map w =
      ⟨((gammaGroundRVLeftTag A (rvObjectArity V.object.obj)).toImage u).val,
        Or.inl ((gammaGroundRVLeftTag A (rvObjectArity V.object.obj)).toImage u).property⟩ := Subtype.ext hw
  change cast (gammaCarrier hc) (((ω.comp (gammaGroundRVUntagLeft A _)).union
    (η.comp (gammaGroundRVUntagRight D _))) _).val = _
  rw [he,GammaGroundMap.union_on_left]
  exact congrArg (fun z => cast (gammaCarrier hc) z.val)
    (congrArg ω (GammaGroundMap.inverse_apply _ _ u))

theorem gammaNativeCoprodForm_right (U V : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (u : Section5.nativeRVGroundDomain (hc := hc) V)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaCoprodAt U V))
    (hw : w.val = rvRightTag (rvObjectArity U.object.obj) u.val) :
    gammaGroundFormValue (gammaNativeCoprodForm U V ω η) w = gammaGroundFormValue η u := by
  let A := Section5.nativeRVGroundDomain (hc := hc) U
  let D := Section5.nativeRVGroundDomain (hc := hc) V
  have he : (GammaGroundBijection.ofCarrierEq (gammaNativeCoprod_domain (hc := hc) U V)).map w =
      ⟨((gammaGroundRVRightTag D (rvObjectArity U.object.obj)).toImage u).val,
        Or.inr ((gammaGroundRVRightTag D (rvObjectArity U.object.obj)).toImage u).property⟩ := Subtype.ext hw
  change cast (gammaCarrier hc) (((ω.comp (gammaGroundRVUntagLeft A _)).union
    (η.comp (gammaGroundRVUntagRight D _))) _).val = _
  rw [he,GammaGroundMap.union_on_right _ _ (gammaGroundRVTaggedImages_disjoint A D)]
  exact congrArg (fun z => cast (gammaCarrier hc) z.val)
    (congrArg η (GammaGroundMap.inverse_apply _ _ u))

theorem gammaNativeCoprod_volume_left (U V : GammaObjectAt B Set.univ n)
    (u : Section5.nativeRVGroundDomain (hc := hc) U)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaCoprodAt U V))
    (hw : w.val = rvLeftTag (rvObjectArity V.object.obj) u.val) :
    (Section5.nativeRVGroundVolume (gammaCoprodAt U V) w).val = (Section5.nativeRVGroundVolume U u).val := by
  let u0 := Section5.nativeRVGroundDomainEquiv U u
  have he : Section5.nativeRVGroundDomainEquiv (gammaCoprodAt U V) w =
      @rvCoprodLeftMap M N hN Set.univ n U.object.obj V.object.obj u0 :=
    Subtype.ext (hw.trans (@Section5.rvLeftTag_normalized M sM hM (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) u.val).symm)
  rw [gammaNativeRVGroundVolume_value,he,gammaNativeRVGroundVolume_value]
  exact @rvCoprod_value_left M N hN Set.univ n U.object.obj V.object.obj u0

theorem gammaNativeCoprod_volume_right (U V : GammaObjectAt B Set.univ n)
    (u : Section5.nativeRVGroundDomain (hc := hc) V)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaCoprodAt U V))
    (hw : w.val = rvRightTag (rvObjectArity U.object.obj) u.val) :
    (Section5.nativeRVGroundVolume (gammaCoprodAt U V) w).val = (Section5.nativeRVGroundVolume V u).val := by
  let u0 := Section5.nativeRVGroundDomainEquiv V u
  have he : Section5.nativeRVGroundDomainEquiv (gammaCoprodAt U V) w =
      @rvCoprodRightMap M N hN Set.univ n U.object.obj V.object.obj u0 :=
    Subtype.ext (hw.trans (@Section5.rvRightTag_normalized M sM hM (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) u.val).symm)
  rw [gammaNativeRVGroundVolume_value,he,gammaNativeRVGroundVolume_value]
  exact @rvCoprod_value_right M N hN Set.univ n U.object.obj V.object.obj u0

end DiamondIntegral.Section3
