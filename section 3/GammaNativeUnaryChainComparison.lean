import «section 3».GammaNativeChainDensity
import «section 3».GammaNativeUnaryPartialFocus
import «section 3».GammaMeasuredCanonicalPresentation
import «section 3».GammaNativePresentationLabels
import IntegrationSection6.FiniteGammaChartedChains

/-! Unary alternating special chains preserve the original principal
Gamma quotient, with a coherent arbitrary Gamma density on every output.
The second induction clause retains the entire initial full key. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeUnaryChain_comparison_pair
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ 1 m}
    {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ 1 l}
    (T : Chain Set.univ 1 A C) : ∀ hΓ : GammaChainDefinable B T,
    (∀ (V : @DefSet LRV M N (@rawRVSpace M N m) Set.univ)
       (v : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ Set.univ V
         (@DefSet.univ LRV M N (@rawRVSpace M N 1) Set.univ))
       (hV : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ Set.univ V _ v)
       (h : @PresentsLift M N hN Set.univ 1 (@SpecialTransformations.Section4.RVObject.mk M N Set.univ 1 m V v) (normalizedPointSet A)),
      T.Alternating none →
      ∀ ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain
        (gammaLiteralAt (Set.subset_univ _) ⟨@SpecialTransformations.Section4.RVObject.mk M N Set.univ 1 m V v,hV⟩ h (GammaChainDefinable.source B T hΓ))),
      ∃ hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)),
      ∃ η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain
        (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T hΓ) hCF)),
        gammaNativeSpecialClass (gammaLiteralAt (Set.subset_univ _) ⟨@SpecialTransformations.Section4.RVObject.mk M N Set.univ 1 m V v,hV⟩ h
          (GammaChainDefinable.source B T hΓ)) ω =
          gammaNativeSpecialClass (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T hΓ) hCF) η ∧
        ∀ p : A, η (gammaNativePullbackKeyAt C (GammaChainDefinable.target B T hΓ) hCF (T.toMap p)) =
          ω (gammaPresentationLabelAt _ h p)) ∧
    (IsRVPullback (carrier A) →
      ∀ hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)),
      T.Alternating (some true) →
      ∀ ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain
        (gammaPullbackAt (Set.subset_univ _) A (GammaChainDefinable.source B T hΓ) hAF)),
      ∃ hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)),
      ∃ η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain
        (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T hΓ) hCF)),
        gammaNativeSpecialClass (gammaPullbackAt (Set.subset_univ _) A (GammaChainDefinable.source B T hΓ) hAF) ω =
          gammaNativeSpecialClass (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T hΓ) hCF) η ∧
        ∀ p : A, η (gammaNativePullbackKeyAt C (GammaChainDefinable.target B T hΓ) hCF (T.toMap p)) =
          ω (gammaNativePullbackKeyAt A (GammaChainDefinable.source B T hΓ) hAF p)) := by
  induction T with
  | nil A =>
    intro hΓ
    constructor
    · intro V v hV h _ ω
      let U := gammaLiteralAt (Set.subset_univ _) ⟨@SpecialTransformations.Section4.RVObject.mk M N Set.univ 1 _ V v,hV⟩ h hΓ
      let P := gammaPresentationAt U h hΓ
      let F := Section5.nativeRVGroundIso (hc := hc) (gammaPresentationIsoAt U h hΓ)
      let η := ω.comp F.map
      refine ⟨P.object.property,η,(gammaNativeSpecialClass_hom P U η ω (gammaMeasuredPresentationHom U h hΓ ω)).symm,?_⟩
      intro p
      change ω (F.map (gammaNativePullbackKeyAt A hΓ P.object.property p)) =
        ω (gammaPresentationLabelAt U h p)
      congr 1
      apply Subtype.ext
      rw [gammaNativePresentation_old_labels,gammaPresentationLabelAt_val,gammaNativePullbackKeyAt_val]
      funext j
      exact Fin.append_right _ _ j
    · intro _ hAF _ ω
      exact ⟨hAF,ω,rfl,fun _ => rfl⟩
  | @cons m l k A D C p tail ih =>
    intro hΓ
    have ih := ih hΓ.2
    cases p with
    | canonical A =>
      constructor
      · intro V v hV h hAlt ω
        let U := gammaLiteralAt (Set.subset_univ _) ⟨@SpecialTransformations.Section4.RVObject.mk M N Set.univ 1 m V v,hV⟩ h hΓ.1
        let R := gammaCanonicalAt U h hΓ.1
        have hR := normalizedPresentsLift_canonical h
        let F := Section5.nativeRVGroundIso (hc := hc) (gammaCanonicalIsoAt U h hΓ.1)
        let ωR := ω.comp F.map
        obtain ⟨hCF,η,H,hη⟩ := ih.1 (@SpecialTransformations.Section4.RVObject.domain M N Set.univ 1 R.object.obj)
          (@SpecialTransformations.Section4.RVObject.volume M N Set.univ 1 R.object.obj) R.object.property hR
          (chainAlternating_none hAlt.2) ωR
        refine ⟨hCF,η,(gammaNativeSpecialClass_hom R U ωR ω (gammaMeasuredCanonicalPresentationHom U h hΓ.1 ω)).symm.trans H,?_⟩
        intro a
        let q := (Primitive.canonical A).toMap a
        change η (gammaNativePullbackKeyAt C _ hCF (tail.toMap q)) = _
        rw [hη q]
        change ω (F.map (gammaPresentationLabelAt R hR q)) = ω (gammaPresentationLabelAt U h a)
        congr 1
        apply Subtype.ext
        rw [gammaNativeCanonical_old_labels,gammaPresentationLabelAt_val,gammaPresentationLabelAt_val]
        exact gammaPrimitive_old_labels (.canonical A) a
      · intro hAP hAF hAlt ω
        have hR := normalizedCanonicalImage_presents A hAP
        let R := gammaPullbackAt (Set.subset_univ _) A hΓ.1 hAF
        obtain ⟨hCF,η,H,hη⟩ := ih.1 (@SpecialTransformations.Section4.RVObject.domain M N Set.univ 1 R.object.obj)
          (@SpecialTransformations.Section4.RVObject.volume M N Set.univ 1 R.object.obj) R.object.property hR
          (chainAlternating_none hAlt.2) ω
        refine ⟨hCF,η,H,?_⟩
        intro a
        let q := (Primitive.canonical A).toMap a
        change η (gammaNativePullbackKeyAt C _ hCF (tail.toMap q)) = _
        rw [hη q]
        rfl
    | @centripetal _ i j D =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      constructor
      · intro V v hV h hAlt ω
        let U := gammaLiteralAt (Set.subset_univ _) ⟨@SpecialTransformations.Section4.RVObject.mk M N Set.univ 1 m V v,hV⟩ h hΓ.1.1
        let R := gammaPartialFocusImageAt hκ hs h00 hr U h D hΓ.1.1 hΓ.1.2
        let T := SpecialBijection.centripetal D
        let hT := gammaCentripetal_chain_definable D hΓ.1.1 hΓ.1.2
        let K := gammaPreparedRVLabelMap (hc := hc) U h T hT R.object.property
        let β := ω.comp K
        have hAP := (pullback_normalize (carrier A)).mp
          (@PresentsLift.pullback M N hN Set.univ 1 U.object.obj (normalizedPointSet A) h)
        obtain ⟨hCF,η,H,hη⟩ := ih.2 (D.etaImage_pullback hAP) R.object.property hAlt.2 β
        have H0 := (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr
          (gammaNativeUnaryPartialFocus_congruence hκ hs h00 hr U h D hΓ.1.1 hΓ.1.2 ω)
        refine ⟨hCF,η,H0.trans H,?_⟩
        intro a
        let q := (Primitive.centripetal D).toMap a
        change η (gammaNativePullbackKeyAt C _ hCF (tail.toMap q)) = _
        rw [hη q]
        change ω (K (gammaNativePullbackKeyAt D.etaImage _ R.object.property q)) =
          ω (gammaPresentationLabelAt U h a)
        congr 1
        apply Subtype.ext
        rw [gammaPreparedRVLabelMap_val,gammaNativePullbackKeyAt_val,gammaPresentationLabelAt_val]
        funext j
        change Fin.append (Section2.tupleRV M q.val.1) q.val.2 (Fin.natAdd 1 j) = a.val.2 j
        exact (Fin.append_right _ _ j).trans (congrFun (gammaChain_old_labels T.chain a) j)
      · intro _ _ hAlt
        exact False.elim (hAlt.1 rfl)

end DiamondIntegral.Section3
