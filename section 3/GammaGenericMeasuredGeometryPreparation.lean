import «section 3».GammaPreparedMeasuredGeometry
import «section 3».GammaMeasuredGeometricVFCodes
import Integration7.PreparedFiniteVolumeGeometry
import Integration7.PreparedGenericRVCells
import Integration7.GenericGammaWitnessCovers

/-! Reuse finite RV code preparation and generic-cell realization for
finite Gamma-measured geometric witnesses. All internal coefficient-field
names are eliminated by the existing original-base reduction. -/
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

theorem gamma_prepare_measured_geometry_in_context
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (J : Finset (GammaMeasuredRelationSchema F G)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier Z) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.toRVTemplate
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
  have hCode := gammaMeasured_geometry_cover_vf_code_in_base L (vfFieldNamedBase_field B) F G J
  obtain ⟨l,Z,T,hTC,hZ,hRows⟩ := gamma_prepare_vf_row_code (B := CF) C₀.saturated C₀.model00
    (vfFieldNamedBase_small B C₀.uncountable ((Cardinal.mk_le_mk_of_subset hBC₀).trans_lt C₀.small))
    (vfFieldNamedBase_field B) hCFD A' hA' _ hCode
  have hT : GammaChainDefinable B T.chain := (vfFieldBaseReduction B).chainDefinable T.chain hTC
  refine ⟨D,hC₀D,l,Z,T,hT,hZ,?_,?_,?_⟩
  · exact gamma_prepared_volume_object_agreement T hT F.toRVTemplate (fun x y hxy => (hRows x y hxy).1)
  · exact gamma_prepared_volume_object_agreement T hT G.toRVTemplate (fun x y hxy => (hRows x y hxy).2.1)
  · intro H hH x
    exact gamma_prepared_measured_geometry_agreement T hT H (fun x y hxy => (hRows x y hxy).2.2 H hH) x

theorem gammaGeneric_measured_geometry_preparation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (hWitness : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema F G, H.valid (vfValues x)) :
    ∃ J : Finset (GammaMeasuredRelationSchema F G),
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier Z) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ x : Z, (∀ j, (rv (x.val.1 j)).val ≠ iRVZero) → ∃ H ∈ J,
        (H.recode (GammaParameterRecode.prepared T hT)).valid (rawPreparedKey x.val) := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B hκ hs hr hg
    (fun H : GammaMeasuredRelationSchema F G => {z | H.valid z}) (fun H => H.valid_definable) hWitness
  obtain ⟨D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,hAg⟩ := gamma_prepare_measured_geometry_in_context C₀ hBC₀ A hA F G J
  refine ⟨J,D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,?_⟩
  intro x hx
  obtain ⟨y,hy,hind⟩ := exists_generic_inverse_in_prepared_cell hc D T hZ x hx
  have hindB := independent_over_smaller_real_base (hBC₀.trans hC₀D) hind
  obtain ⟨H,hH,hValid⟩ := hJ (T.inverseMap y).val.1 hindB
  have hRecoded := H.recode_valid (GammaParameterRecode.prepared T hT) _ _
    (fun j => ((flatKey y.val).2 j).property) (hAg H hH y) hValid
  have hk : rawPreparedKey y.val = rawPreparedKey x.val :=
    congrArg (fun q => fun j => (q.2 j).val) ((flatKey_eq_iff _ _).mpr hy)
  exact ⟨H,hH,hk ▸ hRecoded⟩

end DiamondIntegral.Section3
