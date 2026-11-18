import «section 3».GammaUnaryGeometryBaseReduction
import «section 3».GammaLastMeasuredGeometry

/-! Definable closure names can be eliminated from finite measured
geometric proofs in every positive degree, including all density graphs. -/
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

theorem gammaLastMeasuredGeometry_reduce {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hrC : Cardinal.mk C.real < κ) (hrB : Cardinal.mk B.real < κ)
    (H : GammaDefinableBaseReduction C B)
    {U V : GammaGroundMeasuredRVObject hc C (k+1)} (h : GammaLastMeasuredGeometry hκ hs h00 hrC U V) :
    GammaLastMeasuredGeometry hκ hs h00 hrB (gammaGroundMeasuredRVReduceObject H U) (gammaGroundMeasuredRVReduceObject H V) := by
  induction h with
  | iso e =>
    obtain ⟨e⟩ := e
    exact .iso ⟨asIso (gammaGroundMeasuredRVReduceHom H e.hom)⟩
  | elementary U hAd =>
    let hUB := gammaGroundRVReduceObject_admissible H U.underlying (Fin.last k) hAd
    obtain ⟨e⟩ := gammaGroundMeasuredRVReduceElementaryHom hκ hs h00 hrC hrB H U (Fin.last k) hAd
    exact (GammaLastMeasuredGeometry.elementary (gammaGroundMeasuredRVReduceObject H U) hUB).trans (.iso ⟨(asIso e).symm⟩)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | coprod h₁ h₂ ih₁ ih₂ =>
    rw [gammaGroundMeasuredRVReduceObject_coprod,gammaGroundMeasuredRVReduceObject_coprod]
    exact ih₁.coprod ih₂


end DiamondIntegral.Section3
