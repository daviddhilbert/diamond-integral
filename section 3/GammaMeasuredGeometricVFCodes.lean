import «section 3».GammaMeasuredGeometricRecoding
import Integration7.GammaVolumeWitnessVFCodesInBase

/-! Finite geometric proofs have finite RV row codes over the existing
internal coefficient-field base. The code theorems apply to the complete
Gamma density relations without requiring RV-function validity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {p a b k : ℕ}

theorem gammaMeasured_geometry_vf_code_in_base
    (L : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    {F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf)}
    {G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf)}
    (H : GammaMeasuredRelationSchema F G) :
    GammaVFRowCode C p (H.RecodeAgreement (GammaParameterRecode.identity B p (fun _ => .vf))) := by
  induction H with
  | iso I =>
    exact (gamma_volume_object_vf_code_in_base L FC I.source.toRVTemplate).and
      ((gamma_volume_object_vf_code_in_base L FC I.target.toRVTemplate).and
        (gamma_relation_vf_code_in_base L FC ⟨I.chart,I.chart_definable⟩))
  | agreement F G =>
    exact (gamma_volume_object_vf_code_in_base L FC F.toRVTemplate).and
      ((gamma_volume_object_vf_code_in_base L FC G.toRVTemplate).and GammaVFRowCode.true)
  | elementary F N A =>
    exact (gamma_volume_object_vf_code_in_base L FC F.toRVTemplate).and
      ((gamma_volume_object_vf_code_in_base L FC (F.elementaryFormula.essential.withBound N).toRVTemplate).and GammaVFRowCode.true)
  | @symm a b F G H ih =>
    exact (gamma_volume_object_vf_code_in_base L FC G.toRVTemplate).and
      ((gamma_volume_object_vf_code_in_base L FC F.toRVTemplate).and ih)
  | @trans a b c F G E H K ihH ihK =>
    exact (gamma_volume_object_vf_code_in_base L FC F.toRVTemplate).and
      ((gamma_volume_object_vf_code_in_base L FC G.toRVTemplate).and (ihH.and ihK))
  | @coprod a b c d F G E D H K N R ihH ihK =>
      exact (gamma_volume_object_vf_code_in_base L FC ((F.coprodFormula E).withBound N).toRVTemplate).and
        ((gamma_volume_object_vf_code_in_base L FC ((G.coprodFormula D).withBound R).toRVTemplate).and (ihH.and ihK))

theorem gammaMeasured_geometry_cover_vf_code_in_base
    (L : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (J : Finset (GammaMeasuredRelationSchema F G)) :
    GammaVFRowCode C p (fun z t =>
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement F.toRVTemplate z t ∧
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement G.toRVTemplate z t ∧
      ∀ H ∈ J, H.RecodeAgreement (GammaParameterRecode.identity B p (fun _ => .vf)) z t) :=
  (gamma_volume_object_vf_code_in_base L FC F.toRVTemplate).and
    ((gamma_volume_object_vf_code_in_base L FC G.toRVTemplate).and
      (GammaVFRowCode.finset J _ (fun H _ => gammaMeasured_geometry_vf_code_in_base L FC H)))

end DiamondIntegral.Section3
