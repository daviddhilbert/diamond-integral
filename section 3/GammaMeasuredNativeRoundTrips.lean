import «section 3».GammaMeasuredSchemaPromotion
import «section 3».GammaNativeFullWeightNormalization

/-! Reuse the existing original-ground/native round trip for complete
Gamma forms as well as structural volume. This gives measured schema
promotion for arbitrary actual measured objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k p : ℕ}

theorem gammaRVFormCodeRows_comp_identity
    {A D : GammaGroundDefSet hc B (rawRVSpace (M := M) a)}
    (f : GammaGroundBijection A D) (hf : ∀ u, (f.map u).val = u.val)
    (ω : GammaGroundVolumeForm hc B D) :
    gammaRVFormCodeRows (ω.comp f.map) = gammaRVFormCodeRows ω := by
  ext w
  constructor
  · rintro ⟨hx,hcValue,u,hu,hω⟩
    exact ⟨hx,hcValue,f.map u,(hf u).trans hu,hω⟩
  · rintro ⟨hx,hcValue,v,hv,hω⟩
    obtain ⟨u,hu⟩ := f.bijective.surjective v
    refine ⟨hx,hcValue,u,(hf u).symm.trans ((congrArg Subtype.val hu).trans hv),?_⟩
    change (ω (f.map u)).val = _
    rw [hu]
    exact hω

def gammaGroundMeasuredNativeForm (U : GammaGroundMeasuredRVObject hc B k) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (Section5.groundRVAt U.underlying)) :=
  U.form.comp (Section5.groundRVObjectRoundTrip U.underlying).map

theorem gammaGroundMeasuredNative_volume (U : GammaGroundMeasuredRVObject hc B k)
    (u : Section5.nativeRVGroundDomain (hc := hc) (Section5.groundRVAt U.underlying)) :
    (Section5.nativeRVGroundVolume (Section5.groundRVAt U.underlying) u).val =
      (U.underlying.volume ((Section5.groundRVObjectRoundTrip U.underlying).map u)).val := by
  rw [gammaNativeRVGroundVolume_value,Section5.groundRVAt_volume_eq]
  rfl

def gammaGroundMeasuredNativeRoundTrip (U : GammaGroundMeasuredRVObject hc B k) :
    GammaGroundMeasuredRVHom
      (⟨Section5.nativeRVGroundObject (Section5.groundRVAt U.underlying) (Section5.groundRVAt_full U.underlying),
        gammaGroundMeasuredNativeForm U⟩ : GammaGroundMeasuredRVObject hc B k) U where
  bijection := Section5.groundRVObjectRoundTrip U.underlying
  preserves u := by
    change gammaGroundFormValue (gammaGroundMeasuredNativeForm U) u * _ =
      gammaGroundFormValue U.form ((Section5.groundRVObjectRoundTrip U.underlying).map u) * _
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    apply Subtype.ext
    exact congrFun (gammaGroundMeasuredNative_volume U u) j

theorem gammaGroundMeasured_object_schema_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k) :
    ∃ F : GammaMeasuredRVSchema hc B p U.underlying.arity k sp,
      F.valid z ∧ gammaSchemaRepresents (Section5.groundRVAt U.underlying).toGamma F.object z ∧
      F.object.rowDomain z = U.underlying.domain.carrier ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔ Fin.append x y ∈ gammaRVFormCodeRows U.form) := by
  obtain ⟨F,hF,hRep,hDomain,hDensity⟩ := gammaMeasured_schema_promotion hκ hs hr hg sp z hz
    (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U)
  have hCodes : gammaRVFormCodeRows (gammaGroundMeasuredNativeForm U) = gammaRVFormCodeRows U.form :=
    gammaRVFormCodeRows_comp_identity (Section5.groundRVObjectRoundTrip U.underlying)
      (fun _ => rfl) U.form
  exact ⟨F,hF,hRep,hDomain.trans ((Section5.nativeRVGroundDomain_carrier _).trans (Section5.groundRVAt_domain _)),
    fun x y => (hDensity x y).trans (Set.ext_iff.mp hCodes (Fin.append x y))⟩

end DiamondIntegral.Section3
