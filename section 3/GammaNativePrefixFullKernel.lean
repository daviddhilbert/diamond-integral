import «section 3».GammaNativeUnarySliceKernel
import «section 3».GammaFrozenPrefixFullMeasured

/-! A full Gamma-measured native bijection that changes only its last
VF coordinate preserves the original principal class in every positive
degree. No resolved base or RV density representative is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativePrefixFullMeasured_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaObjectAt B Set.univ (p+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (hFix : ∀ q, (f.map.map q).val.1 ∘ Fin.castAdd 1 = q.val.1 ∘ Fin.castAdd 1) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V η := by
  obtain ⟨N,hFV⟩ := gammaNativeMeasuredVFSliceSchema_uniform_bound hκ.le hs hr hg U ω
  obtain ⟨L,hGV⟩ := gammaNativeMeasuredVFSliceSchema_uniform_bound hκ.le hs hr hg V η
  apply gammaNative_unary_slice_comparison hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1 U V ω η N L hFV hGV
  intro x hx
  obtain ⟨P⟩ := (gammaNativeMeasuredVFSliceSchema U ω N).object.realize (vfValues x) (hFV x).1
  obtain ⟨Q⟩ := (gammaNativeMeasuredVFSliceSchema V η L).object.realize (vfValues x) (hGV x).1
  exact ⟨hFV x,hGV x,P,Q,⟨gammaNativeUnarySliceFullMeasured U V ω η N L x (hFV x) (hGV x) P Q f hFix hx⟩⟩

end DiamondIntegral.Section3
