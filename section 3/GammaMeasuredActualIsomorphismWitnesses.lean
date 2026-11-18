import «section 3».GammaMeasuredIsomorphismPromotion
import «section 3».GammaMeasuredNativeRoundTrips

/-! Every actual measured object isomorphism supplies a finite formula
witness for its fixed promoted endpoint schemata. All native conversions
are the existing literal original-ground round trips. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gammaNativeFullMeasured_weight
    (U : GammaObjectAt B Set.univ k) (hU : GammaFullWeightAt U)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    ((⟨Section5.nativeRVGroundObject U hU,ω⟩ : GammaGroundMeasuredRVObject hc B k).combinedWeight u).val =
      gammaNativeCombinedWeight U ω u := by
  change (gammaGroundFormValue ω u * ∏ j, Section2.rvFiniteValue
    ((Section5.nativeRVGroundObject U hU).target u j)).val = _
  rw [Values.gamma_val_mul]
  have hw : (∏ j, Section2.rvFiniteValue ((Section5.nativeRVGroundObject U hU).target u j)).val =
      ∏ j, Values.vrv ((Section5.nativeRVGroundVolume U u).val j) := by
    change Values.gammaValHom (∏ j, Section2.rvFiniteValue _) = _
    rw [map_prod]
    rfl
  exact congrArg ((gammaGroundFormValue ω u).val * ·) hw

theorem gammaGroundMeasuredNative_weight (U : GammaGroundMeasuredRVObject hc B k)
    (u : Section5.nativeRVGroundDomain (hc := hc) (Section5.groundRVAt U.underlying)) :
    gammaNativeCombinedWeight (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U) u =
      (U.combinedWeight ((Section5.groundRVObjectRoundTrip U.underlying).map u)).val :=
  (gammaNativeFullMeasured_weight _ (Section5.groundRVAt_full U.underlying) _ u).symm.trans
    (congrArg Subtype.val ((gammaGroundMeasuredNativeRoundTrip U).preserves u))

theorem gammaMeasured_actual_isomorphism_formula_witness {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (z : Fin p → M)
    (U V : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1))
    (F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp)
    (G : GammaMeasuredRVSchema hc B p V.underlying.arity (k+1) sp)
    (hF : F.valid z) (hG : G.valid z)
    (hRF : gammaSchemaRepresents (Section5.groundRVAt U.underlying).toGamma F.object z)
    (hRG : gammaSchemaRepresents (Section5.groundRVAt V.underlying).toGamma G.object z)
    (hDF : ∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔ Fin.append x y ∈ gammaRVFormCodeRows U.form)
    (hDG : ∀ x y, Fin.append (Fin.append z x) y ∈ G.density ↔ Fin.append x y ∈ gammaRVFormCodeRows V.form)
    (f : GammaGroundMeasuredRVHom U V) :
    ∃ I : GammaMeasuredRVIsoSchema hc B p U.underlying.arity V.underlying.arity k sp,
      I.source = F ∧ I.target = G ∧ I.valid z := by
  let E := Section5.groundRVObjectRoundTrip U.underlying
  let D := Section5.groundRVObjectRoundTrip V.underlying
  let g := D.symm.comp (f.bijection.comp E)
  have hgMap (u) : D.map (g.map u) = f.bijection.map (E.map u) :=
    D.map.apply_inverse D.bijective _
  have hWeight (u) :
      gammaNativeCombinedWeight (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U) u =
        gammaNativeCombinedWeight (Section5.groundRVAt V.underlying) (gammaGroundMeasuredNativeForm V) (g.map u) := by
    rw [gammaGroundMeasuredNative_weight,gammaGroundMeasuredNative_weight,hgMap]
    exact congrArg Subtype.val (f.preserves (E.map u))
  have hUCode := gammaRVFormCodeRows_comp_identity E (fun _ => rfl) U.form
  have hVCode := gammaRVFormCodeRows_comp_identity D (fun _ => rfl) V.form
  obtain ⟨I,hIF,hIG,hI,_⟩ := gammaMeasured_isomorphism_schema_promotion hκ hs hr hg z
    (Section5.groundRVAt U.underlying) (Section5.groundRVAt V.underlying)
    (Section5.groundRVAt_full U.underlying) (Section5.groundRVAt_full V.underlying)
    (gammaGroundMeasuredNativeForm U) (gammaGroundMeasuredNativeForm V) F G hF hG hRF hRG
    (fun x y => (hDF x y).trans (Set.ext_iff.mp hUCode (Fin.append x y)).symm)
    (fun x y => (hDG x y).trans (Set.ext_iff.mp hVCode (Fin.append x y)).symm) g hWeight
  exact ⟨I,hIF,hIG,hI⟩

end DiamondIntegral.Section3
