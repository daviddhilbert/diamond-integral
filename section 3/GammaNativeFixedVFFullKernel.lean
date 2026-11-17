import «section 3».GammaNativeFixedVFPointKernel
import «section 3».GammaFullMeasuredFixedWeights
import «section 3».GammaNativeTypedConjugacy

/-! The full measured VF-fixed kernel is proved in every positive
degree, using the existing finite-row and preparation proofs. The generic
Jacobian equation supplies the Gamma form equality needed on those rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeFixedVFFullMeasured_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V π))
    (hVF : ∀ p, (f.map.map p).val.1 = p.val.1) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V π := by
  let F := gammaNativeTypedFullConjugate hκ hs hr hv U V ω π f
  have hValue (p : (gammaNativeTypedMeasuredData U ω).domain) :
      (F.map.map p).val = (f.map.map ((gammaNativeTypedLiftBijection U).map p)).val := by
    let q := f.map.map ((gammaNativeTypedLiftBijection U).map p)
    have h := (gammaNativeTypedLiftBijection V).map.apply_inverse
      (gammaNativeTypedLiftBijection V).bijective q
    exact congrArg (fun z : (gammaNativeUnitLift (hc := hc) V.toGamma).domain => z.val) h
  have hFixed : ∀ p, (F.map.map p).val.1 = p.val.1 := by
    intro p
    exact (congrArg Prod.fst (hValue p)).trans (hVF ((gammaNativeTypedLiftBijection U).map p))
  let E := gammaGroundPointIso F.map
  apply gammaNativeFixedVFPoint_comparison hκ hs h00 hr hg C hBC U V ω π E hFixed
  intro p hp
  have H := gammaFullMeasuredFixedVF_form_eq hκ hs hr hv F hFixed p hp
  calc
    ω (gammaPresentationLabelAt U (normalizedTypedLift_presents U.object.obj) p) =
        (gammaNativeTypedMeasuredData U ω).form p := congrArg ω (Subtype.ext rfl)
    _ = (gammaNativeTypedMeasuredData V π).form (F.map.map p) := H
    _ = π (gammaPresentationLabelAt V (normalizedTypedLift_presents V.object.obj) (E.equiv p)) :=
      congrArg π (Subtype.ext rfl)

end DiamondIntegral.Section3
