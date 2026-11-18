import «section 3».GammaRawEssentialGeometryPreparation
import «section 3».GammaMeasuredIndexedNormalizedComparison
import «section 3».GammaMeasuredIndexedWitnessGluing
import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaPreparedIndexValues

/-! Generic finite measured proofs of normalized rows yield a comparison
of the actual raw prepared indexed families. Both raw density graphs and
their normalization are prepared over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b k : ℕ}

theorem gammaGeneric_raw_prepared_family_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (hFV : ∀ x : Fin p → VFType (M := M), F.valid (vfValues x))
    (hGV : ∀ x : Fin p → VFType (M := M), G.valid (vfValues x))
    (hWitness : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema F.essential G.essential, H.valid (vfValues x)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
    ∃ hZ : IsRVPullback (carrier Z), ∃ BP : PreparedIndexPresentation B Z,
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      let K := GammaParameterRecode.prepared T hT
      ∃ hF : ∀ t ∈ preparedKeyDomain Z, (F.recode K).valid (rvValues t),
      ∃ hG : ∀ t ∈ preparedKeyDomain Z, (G.recode K).valid (rvValues t),
        ∀ (P : (F.recode K).object.IndexedPresentation BP) (Q : (G.recode K).object.IndexedPresentation BP),
          gammaMeasuredPrincipalValue ((F.recode K).indexedObject BP hF P) =
            gammaMeasuredPrincipalValue ((G.recode K).indexedObject BP hG Q) := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B hκ hs hr hg
    (fun H : GammaMeasuredRelationSchema F.essential G.essential => {z | H.valid z})
    (fun H => H.valid_definable) hWitness
  obtain ⟨D,hCD,l,Z,T,hT,hZ,hFA,hGA,hFEA,hGEA,hAg⟩ :=
    gamma_prepare_raw_essential_geometry_in_context C₀ hBC₀ A hA F G J
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hr (hBC₀.trans hCD) T hT hZ
  let K := GammaParameterRecode.prepared T hT
  let FE := F.essential.recode K
  let GE := G.essential.recode K
  have hF : ∀ t ∈ preparedKeyDomain Z, (F.recode K).valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact F.recode_valid K _ _ (fun j => ((flatKey x.val).2 j).property) (hFA x) (hFV (T.inverseMap x).val.1)
  have hG : ∀ t ∈ preparedKeyDomain Z, (G.recode K).valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact G.recode_valid K _ _ (fun j => ((flatKey x.val).2 j).property) (hGA x) (hGV (T.inverseMap x).val.1)
  have hFE : ∀ t ∈ preparedKeyDomain Z, FE.valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact F.essential.recode_valid K _ _ (fun j => ((flatKey x.val).2 j).property) (hFEA x)
      (F.essential_valid _ (hFV (T.inverseMap x).val.1))
  have hGE : ∀ t ∈ preparedKeyDomain Z, GE.valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact G.essential.recode_valid K _ _ (fun j => ((flatKey x.val).2 j).property) (hGEA x)
      (G.essential_valid _ (hGV (T.inverseMap x).val.1))
  have hCover : ∀ x : Z, (∀ j, (rv (x.val.1 j)).val ≠ iRVZero) → ∃ H ∈ J,
      (H.recode K).valid (rawPreparedKey x.val) := by
    intro x hx
    obtain ⟨y,hy,hind⟩ := exists_generic_inverse_in_prepared_cell hc D T hZ x hx
    have hindB := independent_over_smaller_real_base (hBC₀.trans hCD) hind
    obtain ⟨H,hH,hValid⟩ := hJ (T.inverseMap y).val.1 hindB
    have hRecoded := H.recode_valid K _ _ (fun j => ((flatKey y.val).2 j).property) (hAg H hH y) hValid
    have hk : rawPreparedKey y.val = rawPreparedKey x.val :=
      congrArg (fun q => fun j => (q.2 j).val) ((flatKey_eq_iff _ _).mpr hy)
    exact ⟨H,hH,hk ▸ hRecoded⟩
  let JK := J.image (fun H => H.recode K)
  have hCoverE : ∀ t ∈ essentialIndexDomain BP, ∃ H ∈ JK, H.valid (rvValues t) := by
    rintro t ⟨ht,hNZ⟩
    obtain ⟨q,rfl⟩ := ht
    have hNZ' : ∀ j, (rv (q.val.1 j)).val ≠ iRVZero := by
      intro j hz
      apply hNZ j
      have hv := congrFun (PreparedIndexPresentation.totalVolume_eq Z BP (flatKey q.val).2 ⟨q,rfl⟩) j
      calc
        (BP.totalVolume (flatKey q.val).2 j).val = ((flatKey q.val).2 (Fin.castAdd l j)).val := congrArg Subtype.val hv
        _ = (rv (q.val.1 j)).val := by simp only [flatKey,Fin.append_left,key]
        _ = iRVZero := hz
    obtain ⟨H,hH,hValid⟩ := hCover q hNZ'
    exact ⟨H.recode K,Finset.mem_image.mpr ⟨H,hH,rfl⟩,hValid⟩
  have hEqF : ∀ t ∈ preparedKeyDomain Z, (F.recode K).essential.toRVTemplate.sameRow FE.toRVTemplate (rvValues t) := by
    rintro t ⟨x,rfl⟩
    have hRaw := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows F.toRVTemplate _ _ (hFA x)
    have hCan := gammaMeasured_rowAgreement_essential (F := F) (G := F.recode K) hRaw
    have hEss := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows F.essential.toRVTemplate _ _ (hFEA x)
    exact gammaMeasured_sameRow_of_agreements (fun j => ((T.inverseMap x).val.1 j).property)
      (fun j => ((flatKey x.val).2 j).property) hCan hEss
  have hEqG : ∀ t ∈ preparedKeyDomain Z, (G.recode K).essential.toRVTemplate.sameRow GE.toRVTemplate (rvValues t) := by
    rintro t ⟨x,rfl⟩
    have hRaw := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows G.toRVTemplate _ _ (hGA x)
    have hCan := gammaMeasured_rowAgreement_essential (F := G) (G := G.recode K) hRaw
    have hEss := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows G.essential.toRVTemplate _ _ (hGEA x)
    exact gammaMeasured_sameRow_of_agreements (fun j => ((T.inverseMap x).val.1 j).property)
      (fun j => ((flatKey x.val).2 j).property) hCan hEss
  let PE := FE.object.indexedPresentation_finiteRows (essentialIndexPresentation BP)
    (fun t ht => FE.object.finiteRow_of_valid _ (hFE t ht.1).1)
  let QE := GE.object.indexedPresentation_finiteRows (essentialIndexPresentation BP)
    (fun t ht => GE.object.finiteRow_of_valid _ (hGE t ht.1).1)
  have hMain := gammaMeasured_finite_indexed_geometry_glue hκ hs h00 hr hg FE GE JK
    (essentialIndexPresentation BP) (fun t ht => hFE t ht.1) (fun t ht => hGE t ht.1) hCoverE PE QE
  refine ⟨D,hCD,l,Z,T,hT,hZ,BP,hFA,hGA,hF,hG,?_⟩
  intro P Q
  exact (gammaMeasuredIndexed_normalized_comparison (F.recode K) FE BP hF hFE hEqF P PE).trans
    (hMain.trans (gammaMeasuredIndexed_normalized_comparison (G.recode K) GE BP hG hGE hEqG Q QE).symm)

end DiamondIntegral.Section3
