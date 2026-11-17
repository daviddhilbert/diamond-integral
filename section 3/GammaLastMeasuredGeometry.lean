import «section 3».GammaNativeElementaryPermutationTransport
import «section 3».GammaMeasuredGeometricRelations
import «section 3».GammaNativeElementaryHighMeasure

/-! Finite geometric proofs in any positive degree can use only the
last-coordinate local elementary operation. Actual measured permutations
and the existing elementary product charts give the conversion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

inductive GammaLastMeasuredGeometry
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    GammaGroundMeasuredRVObject hc B (n+1) → GammaGroundMeasuredRVObject hc B (n+1) → Prop
  | iso {U V} : Nonempty (U ≅ V) → GammaLastMeasuredGeometry hκ hs h00 hr U V
  | elementary (U : GammaGroundMeasuredRVObject hc B (n+1))
      (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject (Fin.last n)) :
      GammaLastMeasuredGeometry hκ hs h00 hr U
        (gammaMeasuredElementaryObject hκ hs h00 hr U (Fin.last n) hAd)
  | symm {U V} : GammaLastMeasuredGeometry hκ hs h00 hr U V → GammaLastMeasuredGeometry hκ hs h00 hr V U
  | trans {U V W} : GammaLastMeasuredGeometry hκ hs h00 hr U V →
      GammaLastMeasuredGeometry hκ hs h00 hr V W → GammaLastMeasuredGeometry hκ hs h00 hr U W
  | coprod {U V X Y} : GammaLastMeasuredGeometry hκ hs h00 hr U V →
      GammaLastMeasuredGeometry hκ hs h00 hr X Y → GammaLastMeasuredGeometry hκ hs h00 hr (U.coprod X) (V.coprod Y)

theorem gammaLastMeasuredGeometry_of_native
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {h00 : M ⊨ Axioms.ACVF00} {hr : Cardinal.mk B.real < κ}
    {U V : GammaGroundMeasuredRVObject hc B (n+1)} (h : GammaMeasuredGeometricRelation hκ hs h00 hr U V) :
    GammaLastMeasuredGeometry hκ hs h00 hr U V := by
  induction h with
  | iso e => exact .iso e
  | elementary U ω i hAd =>
    let H := gammaHighRestrictionAt U
    let hH := gammaHighRestriction_fullWeight U
    let ρ := ω.comp (gammaNativeHighLabelInclusion U)
    let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap i (Fin.last n)
    have hLast : σ (Fin.last n) = i := by simp only [σ,Equiv.swap_apply_right]
    let V := H.reindexVolume σ
    let hV := gammaNativeReindex_full H hH σ
    let π := gammaNativePermutedForm H σ ρ
    let hAdH := gammaNativeHigh_admissible U i hAd
    have hAdV : GammaAdmissible V.toGamma.toGammaRVObject (Fin.last n) := by
      apply gammaNativeReindex_admissible H σ (Fin.last n)
      rw [hLast]
      exact hAdH
    let P : GammaGroundMeasuredRVObject hc B (n+1) := ⟨Section5.nativeRVGroundObject V hV,π⟩
    let e1 := gammaNativeFullWeightNormalizationHom H hH ρ
    let e2 := gammaNativeVolumePermutationMeasured H σ ρ
    let e3 := gammaNativeFullWeightNormalizationHom V hV π
    let e := e3.symm.comp (e2.comp e1)
    let hAP := gammaNativeGround_admissible (hc := hc) V hV (Fin.last n) hAdV
    obtain ⟨fLocal⟩ := gammaNativeElementary_local_measured_hom hκ hs h00 hr V hV π (Fin.last n) hAdV
    obtain ⟨fTransport⟩ := gammaNativeElementary_transport_measured hκ hs h00 hr H V hH hV ρ π i (Fin.last n) hAdH hAdV e
    let fHigh := gammaNativeElementaryHighMeasuredHom hκ hs h00 hr U i hAd ω
    have hSource : GammaLastMeasuredGeometry hκ hs h00 hr (gammaNativeMeasuredNormalization U ω) P := .iso ⟨asIso e⟩
    exact hSource.trans ((GammaLastMeasuredGeometry.elementary P hAP).trans
      ((GammaLastMeasuredGeometry.iso ⟨(asIso fLocal).symm⟩).trans
        ((GammaLastMeasuredGeometry.iso ⟨(asIso fTransport).symm⟩).trans
          (GammaLastMeasuredGeometry.iso ⟨asIso fHigh⟩))))
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | coprod h₁ h₂ ih₁ ih₂ => exact ih₁.coprod ih₂

end DiamondIntegral.Section3
