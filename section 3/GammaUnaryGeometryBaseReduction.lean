import «section 3».GammaGroundMeasuredElementaryBaseReduction
import «section 3».GammaUnaryLocalGeometricRelations
import «section 3».GammaMeasuredRealBaseExtension

/-! A finite unary measured geometric proof descends through a definable
base reduction. Adjoining a coefficient field does not change the original
category, its forms or its elementary relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {k : ℕ}

def GammaGroundRVObject.monoReal (U : GammaGroundRVObject hc B k) {S : Set M} (h : B.real ⊆ S) :
    GammaGroundRVObject hc ⟨S,B.gamma⟩ k :=
  ⟨U.arity,U.domain.monoReal h,U.volume.monoReal h,U.finite,U.nonzero⟩

def GammaGroundMeasuredRVObject.monoReal (U : GammaGroundMeasuredRVObject hc B k) {S : Set M} (h : B.real ⊆ S) :
    GammaGroundMeasuredRVObject hc ⟨S,B.gamma⟩ k := ⟨U.underlying.monoReal h,U.form.monoReal h⟩

theorem gammaGroundMeasuredRVReduce_monoReal {S : Set M} (h : B.real ⊆ S)
    (H : GammaDefinableBaseReduction ⟨S,B.gamma⟩ B) (U : GammaGroundMeasuredRVObject hc B k) :
    gammaGroundMeasuredRVReduceObject H (U.monoReal h) = U := by
  cases U
  rfl

theorem gammaNativeMeasuredNormalization_monoReal
    (U : GammaObjectAt B Set.univ (k+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) {S : Set M} (h : B.real ⊆ S) :
    gammaNativeMeasuredNormalization (gammaNativeRealBaseExtend U h) (gammaNativeRealBaseExtendForm U ω h) =
      (gammaNativeMeasuredNormalization U ω).monoReal h := by
  rfl

theorem gammaUnaryMeasuredGeometry_reduce {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hrC : Cardinal.mk C.real < κ) (hrB : Cardinal.mk B.real < κ)
    (H : GammaDefinableBaseReduction C B)
    {U V : GammaGroundMeasuredRVObject hc C 1} (h : GammaUnaryMeasuredGeometry hκ hs h00 hrC U V) :
    GammaUnaryMeasuredGeometry hκ hs h00 hrB (gammaGroundMeasuredRVReduceObject H U) (gammaGroundMeasuredRVReduceObject H V) := by
  induction h with
  | iso e =>
    obtain ⟨e⟩ := e
    exact .iso ⟨asIso (gammaGroundMeasuredRVReduceHom H e.hom)⟩
  | elementary U hAd =>
    let hUB := gammaGroundRVReduceObject_admissible H U.underlying 0 hAd
    obtain ⟨e⟩ := gammaGroundMeasuredRVReduceElementaryHom hκ hs h00 hrC hrB H U 0 hAd
    exact (GammaUnaryMeasuredGeometry.elementary (gammaGroundMeasuredRVReduceObject H U) hUB).trans (.iso ⟨(asIso e).symm⟩)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | coprod h₁ h₂ ih₁ ih₂ =>
    rw [gammaGroundMeasuredRVReduceObject_coprod,gammaGroundMeasuredRVReduceObject_coprod]
    exact ih₁.coprod ih₂

end DiamondIntegral.Section3
