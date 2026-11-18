import «section 3».GammaGenericMeasuredGeometryPreparation
import «section 3».GammaMeasuredIndexedWitnessGluing
import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaPreparedIndexValues
import Integration7.GammaEssentialIndexDomains

/-! Generic finite Gamma-measured proofs become an actual principal
comparison of the prepared essential indexed families. Preparation and
all indexed sums retain the original real/Gamma parameter base. -/
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

theorem gammaGeneric_prepared_measured_geometry_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (hWitness : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema F G, H.valid (vfValues x)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
    ∃ hZ : IsRVPullback (carrier Z), ∃ BP : PreparedIndexPresentation B Z,
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      let K := GammaParameterRecode.prepared T hT
      ∃ hF : ∀ t ∈ essentialIndexDomain BP, (F.recode K).valid (rvValues t),
      ∃ hG : ∀ t ∈ essentialIndexDomain BP, (G.recode K).valid (rvValues t),
        ∀ (P : (F.recode K).object.IndexedPresentation (essentialIndexPresentation BP))
          (Q : (G.recode K).object.IndexedPresentation (essentialIndexPresentation BP)),
          gammaMeasuredPrincipalValue ((F.recode K).indexedObject (essentialIndexPresentation BP) hF P) =
            gammaMeasuredPrincipalValue ((G.recode K).indexedObject (essentialIndexPresentation BP) hG Q) := by
  obtain ⟨J,D,hCD,l,Z,T,hT,hZ,hFA,hGA,hCover⟩ := gammaGeneric_measured_geometry_preparation
    hκ hs hr hg C₀ hBC₀ A hA F G hWitness
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hr (hBC₀.trans hCD) T hT hZ
  let K := GammaParameterRecode.prepared T hT
  let JK := J.image (fun H => H.recode K)
  have hCoverE : ∀ t ∈ essentialIndexDomain BP, ∃ H ∈ JK, H.valid (rvValues t) := by
    rintro t ⟨ht,hNZ⟩
    obtain ⟨q,rfl⟩ := ht
    have hNZ' : ∀ j, (rv (q.val.1 j)).val ≠ iRVZero := by
      intro j hz
      apply hNZ j
      have hv := congrFun (PreparedIndexPresentation.totalVolume_eq Z BP (flatKey q.val).2 ⟨q,rfl⟩) j
      calc
        (BP.totalVolume (flatKey q.val).2 j).val =
            ((flatKey q.val).2 (Fin.castAdd l j)).val := congrArg Subtype.val hv
        _ = (rv (q.val.1 j)).val := by simp only [flatKey,Fin.append_left,key]
        _ = iRVZero := hz
    obtain ⟨H,hH,hValid⟩ := hCover q hNZ'
    exact ⟨H.recode K,Finset.mem_image.mpr ⟨H,hH,rfl⟩,hValid⟩
  have hF : ∀ t ∈ essentialIndexDomain BP, (F.recode K).valid (rvValues t) := by
    intro t ht
    obtain ⟨H,_,hH⟩ := hCoverE t ht
    exact (H.valid_endpoints hH).1
  have hG : ∀ t ∈ essentialIndexDomain BP, (G.recode K).valid (rvValues t) := by
    intro t ht
    obtain ⟨H,_,hH⟩ := hCoverE t ht
    exact (H.valid_endpoints hH).2
  refine ⟨D,hCD,l,Z,T,hT,hZ,BP,hFA,hGA,hF,hG,?_⟩
  intro P Q
  exact gammaMeasured_finite_indexed_geometry_glue hκ hs h00 hr hg (F.recode K) (G.recode K)
    JK (essentialIndexPresentation BP) hF hG hCoverE P Q

end DiamondIntegral.Section3
