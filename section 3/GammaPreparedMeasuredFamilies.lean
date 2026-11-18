import «section 3».GammaMeasuredEssentialRowUniformity
import «section 3».GammaPreparedFormConstraintRetention
import Integration7.HKGenericFiniteConstrainedPreparation
import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaPreparedIndexValues

/-! The existing generic finite-row preparation supplies a simultaneous
measured comparison for arbitrary retained Gamma forms and every positive
base dimension. No representative of either form is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b n : ℕ}

theorem gammaGeneric_measured_family_preparation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (X : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) 0)
    (hX : GammaSetDefinable B (carrier X))
    (F : GammaFiniteRVSchema B (n+1) a 0) (G : GammaFiniteRVSchema B (n+1) b 0)
    (hF : ∀ x : X, F.valid (rawVFParameter x.val))
    (hG : ∀ x : X, G.valid (rawVFParameter x.val))
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)
    (hAF : ∀ x : X, F.rowDomain (rawVFParameter x.val) ⊆ A.carrier)
    (hDG : ∀ x : X, G.rowDomain (rawVFParameter x.val) ⊆ D.carrier)
    (hWitness : ∀ x : Fin (n+1) → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B (n+1) a b (fun _ => .vf),
        H.val ⊆ gammaParametricFormConstraint A D ω π (fun _ => .vf) ∧
          (gammaFiniteRowChartSchema F G H).valid (vfValues x)) :
    ∃ C' : BaseContext M, ∃ hCC' : (C.base : Set M) ⊆ (C'.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (C'.base : Set M) (n+1) l,
    ∃ T : SpecialBijection (extendBase X hCC') Z, ∃ hT : GammaChainDefinable B T.chain,
    ∃ hZ : IsRVPullback (carrier Z), ∃ BP : PreparedIndexPresentation B Z,
      (∀ q : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement F
        (rawVFParameter (T.inverseMap q).val) (rawPreparedKey q.val)) ∧
      (∀ q : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement G
        (rawVFParameter (T.inverseMap q).val) (rawPreparedKey q.val)) ∧
      ∃ hAF' : ∀ t ∈ preparedKeyDomain Z,
          ((GammaParameterRecode.prepared T hT).object F).rowDomain (rvValues t) ⊆ A.carrier,
      ∃ hDG' : ∀ t ∈ preparedKeyDomain Z,
          ((GammaParameterRecode.prepared T hT).object G).rowDomain (rvValues t) ⊆ D.carrier,
      ∀ (P : ((GammaParameterRecode.prepared T hT).object F).IndexedPresentation BP)
        (Q : ((GammaParameterRecode.prepared T hT).object G).IndexedPresentation BP),
        Nonempty (GammaGroundMeasuredRVHom
          (gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma)
            (ω.comp (gammaIndexedOriginalLabelMap BP _ P A hAF')))
          (gammaNativeMeasuredNormalization (gammaUniversalObject Q.toGamma)
            (π.comp (gammaIndexedOriginalLabelMap BP _ Q D hDG')))) := by
  obtain ⟨J,C',hCC',l,Z,T,hT,hZ,hFA,hGA,hCover⟩ := HK.generic_finite_constrained_preparation
    hc hκ hs hr hg C hBC X hX F G (gammaParametricFormConstraint A D ω π (fun _ => .vf)) hWitness
  let K := GammaParameterRecode.prepared T hT
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hr (hBC.trans hCC') T hT hZ
  have hDF : ∀ t ∈ preparedKeyDomain Z, (K.object F).valid (rvValues t) := by
    rintro t ⟨q,rfl⟩
    exact K.object_valid F _ _ (fun j => ((flatKey q.val).2 j).property) (hFA q)
      (hF ⟨(T.inverseMap q).val,(T.inverseMap q).property⟩)
  have hDDG : ∀ t ∈ preparedKeyDomain Z, (K.object G).valid (rvValues t) := by
    rintro t ⟨q,rfl⟩
    exact K.object_valid G _ _ (fun j => ((flatKey q.val).2 j).property) (hGA q)
      (hG ⟨(T.inverseMap q).val,(T.inverseMap q).property⟩)
  have hAF' : ∀ t ∈ preparedKeyDomain Z, (K.object F).rowDomain (rvValues t) ⊆ A.carrier := by
    rintro t ⟨q,rfl⟩ r hr'
    exact hAF ⟨(T.inverseMap q).val,(T.inverseMap q).property⟩ ((hFA q).domains.ge hr')
  have hDG' : ∀ t ∈ preparedKeyDomain Z, (K.object G).rowDomain (rvValues t) ⊆ D.carrier := by
    rintro t ⟨q,rfl⟩ r hr'
    exact hDG ⟨(T.inverseMap q).val,(T.inverseMap q).property⟩ ((hGA q).domains.ge hr')
  refine ⟨C',hCC',l,Z,T,hT,hZ,BP,hFA,hGA,hAF',hDG',?_⟩
  intro P Q
  apply gammaMeasured_essential_row_uniformity hκ hs hr hg BP (K.object F) (K.object G)
    hDF hDDG P Q A D ω π hAF' hDG'
  rintro t ⟨q,rfl⟩ hNZ
  have hNZ' : ∀ j, (rv (q.val.1 j)).val ≠ iRVZero := by
    intro j hz
    apply hNZ j
    have hv := congrFun (PreparedIndexPresentation.totalVolume_eq Z BP (flatKey q.val).2 ⟨q,rfl⟩) j
    calc
      (BP.totalVolume (flatKey q.val).2 j).val =
          ((flatKey q.val).2 (Fin.castAdd l j)).val := congrArg Subtype.val hv
      _ = (rv (q.val.1 j)).val := by simp only [flatKey,Fin.append_left,key]
      _ = iRVZero := hz
  obtain ⟨H,_,hH⟩ := hCover q hNZ'
  exact ⟨K.relation H.val,gammaPrepared_relation_form_constraint A D ω π T hT H.val H.property,hH⟩

end DiamondIntegral.Section3
