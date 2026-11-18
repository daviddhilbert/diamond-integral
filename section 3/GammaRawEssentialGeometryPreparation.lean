import «section 3».GammaGenericMeasuredGeometryPreparation
import «section 3».GammaMeasuredEssentialSchemata

/-! Prepare raw measured rows and finite geometric proofs of their
essential restrictions simultaneously. All certificates descend to the
original base after the internal finite-code construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b k : ℕ}

theorem gamma_prepare_raw_essential_geometry_in_context
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (J : Finset (GammaMeasuredRelationSchema F.essential G.essential)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier Z) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.essential.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.essential.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ H ∈ J, ∀ x : Z, H.RecodeAgreement (GammaParameterRecode.prepared T hT)
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  let CF := vfFieldNamedBase B
  let D := vfFieldContainingVolumeContext C₀ B hBC₀
  have hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inl hx)
  have hCFD : CF.real ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inr hx)
  let A' := extendBase A hC₀D
  have hA' : GammaSetDefinable CF (carrier A') := hA.mono Set.subset_union_left (Set.Subset.refl _)
  let L : GammaFormulaBaseChange B CF := ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hGeom := gammaMeasured_geometry_cover_vf_code_in_base L (vfFieldNamedBase_field B) F.essential G.essential J
  have hCode := hGeom.and ((gamma_volume_object_vf_code_in_base L (vfFieldNamedBase_field B) F.toRVTemplate).and
    (gamma_volume_object_vf_code_in_base L (vfFieldNamedBase_field B) G.toRVTemplate))
  obtain ⟨l,Z,T,hTC,hZ,hRows⟩ := gamma_prepare_vf_row_code (B := CF) C₀.saturated C₀.model00
    (vfFieldNamedBase_small B C₀.uncountable ((Cardinal.mk_le_mk_of_subset hBC₀).trans_lt C₀.small))
    (vfFieldNamedBase_field B) hCFD A' hA' _ hCode
  have hT : GammaChainDefinable B T.chain := (vfFieldBaseReduction B).chainDefinable T.chain hTC
  refine ⟨D,hC₀D,l,Z,T,hT,hZ,?_,?_,?_,?_,?_⟩
  · exact gamma_prepared_volume_object_agreement T hT F.toRVTemplate (fun x y hxy => (hRows x y hxy).2.1)
  · exact gamma_prepared_volume_object_agreement T hT G.toRVTemplate (fun x y hxy => (hRows x y hxy).2.2)
  · exact gamma_prepared_volume_object_agreement T hT F.essential.toRVTemplate (fun x y hxy => (hRows x y hxy).1.1)
  · exact gamma_prepared_volume_object_agreement T hT G.essential.toRVTemplate (fun x y hxy => (hRows x y hxy).1.2.1)
  · intro H hH x
    exact gamma_prepared_measured_geometry_agreement T hT H (fun x y hxy => (hRows x y hxy).1.2.2 H hH) x

end DiamondIntegral.Section3
