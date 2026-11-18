import «section 3».GammaMeasuredGeometricRecodingValidity
import Integration7.GammaPreparedVolumeRows

/-! Constancy of the existing primitive VF row codes gives exact
agreement of every measured geometric proof over the prepared RV key.
No RV-valued density or new Gamma parameter is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p l a b k : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S p 0}
variable {Z : SpecialTransformations.Section5.DefSet (M := M) S p l}

theorem gamma_prepared_measured_geometry_agreement
    (T : SpecialBijection A Z) (hT : GammaChainDefinable B T.chain)
    {F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf)}
    {G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf)}
    (H : GammaMeasuredRelationSchema F G) :
    (∀ x y : Z, SameRV x.val y.val →
      H.RecodeAgreement (GammaParameterRecode.identity B p (fun _ => .vf))
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val)) →
    ∀ x : Z, H.RecodeAgreement (GammaParameterRecode.prepared T hT)
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  induction H with
  | iso I =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT I.source.toRVTemplate (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_object_agreement T hT I.target.toRVTemplate (fun x y hxy => (hH x y hxy).2.1) x,
      gamma_prepared_relation_agreement T hT ⟨I.chart,I.chart_definable⟩ (fun x y hxy => (hH x y hxy).2.2) x⟩
  | agreement F G =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT F.toRVTemplate (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_object_agreement T hT G.toRVTemplate (fun x y hxy => (hH x y hxy).2.1) x,trivial⟩
  | elementary F N R =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT F.toRVTemplate (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_object_agreement T hT (F.elementaryFormula.essential.withBound N).toRVTemplate
        (fun x y hxy => (hH x y hxy).2.1) x,trivial⟩
  | @symm a b F G H ih =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT G.toRVTemplate (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_object_agreement T hT F.toRVTemplate (fun x y hxy => (hH x y hxy).2.1) x,
      ih (fun x y hxy => (hH x y hxy).2.2) x⟩
  | @trans a b c F G E H K ihH ihK =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT F.toRVTemplate (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_object_agreement T hT G.toRVTemplate (fun x y hxy => (hH x y hxy).2.1) x,
      ihH (fun x y hxy => (hH x y hxy).2.2.1) x,ihK (fun x y hxy => (hH x y hxy).2.2.2) x⟩
  | @coprod a b c d F G E D H K N R ihH ihK =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT ((F.coprodFormula E).withBound N).toRVTemplate
        (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_object_agreement T hT ((G.coprodFormula D).withBound R).toRVTemplate
        (fun x y hxy => (hH x y hxy).2.1) x,
      ihH (fun x y hxy => (hH x y hxy).2.2.1) x,ihK (fun x y hxy => (hH x y hxy).2.2.2) x⟩

end DiamondIntegral.Section3
