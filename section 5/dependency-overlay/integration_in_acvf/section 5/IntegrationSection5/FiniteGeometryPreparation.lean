import IntegrationSection5.FiniteNumbered
import IntegrationSection5.UnaryBijection
import IntegrationSection5.GammaMapPresentation
import IntegrationSection5.UnaryPartition
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {n m u w l : ℕ}
theorem lemma_5_1_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (F : SpecialTransformations.Section3.VFFieldBase P.real)
    (A : Set (Point (M := M) n m)) (B : Set (Point (M := M) u w)) (f : A → B)
    (hA : GammaSetDefinable P A) (hB : GammaSetDefinable P B)
    (hf : GammaGraphDefinable P (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q))
    (hFiniteA : FiniteMixedRVFibres A) (hFiniteB : FiniteMixedRVFibres B) :
    ∃ S : Set M,
    ∃ hAr : SetDefinable (pointSpace n m) S A,
    ∃ hBr : SetDefinable (pointSpace u w) S B,
    ∃ hfr : RelationDefinable (pointSpace n m) (pointSpace u w) S
      (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q),
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S n r, ∃ B' : DefSet (M := M) S u s,
    ∃ TA : SpecialBijection (PresentedSet.mk A hAr) A',
    ∃ TB : SpecialBijection (PresentedSet.mk B hBr) B',
      GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
      IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
      Contractible (Map.comp TB.toMap (Map.comp (Map.mk f hfr) TA.inverseMap)) ∧
      GammaGraphDefinable P
        (pointMapGraph (Map.comp TB.toMap (Map.comp (Map.mk f hfr) TA.inverseMap))) ∧
      Map.FiniteFibres (rvObjectVolume (pullbackObject A')) ∧
      Map.FiniteFibres (rvObjectVolume (pullbackObject B')) := by
  obtain ⟨S,hAr,hBr,hfr,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hΓ⟩ :=
    lemma_5_1 hs h00 hsmall F A B f hA hB hf
  have hFA := GammaIso.finite_mixed_rv_fibres hκ hs hsmall (gammaSpecialIso TA hTA) hFiniteA
  have hFB := GammaIso.finite_mixed_rv_fibres hκ hs hsmall (gammaSpecialIso TB hTB) hFiniteB
  exact ⟨S,hAr,hBr,hfr,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hΓ,
    pullbackObject_finiteVolume A' hA' hFA,pullbackObject_finiteVolume B' hB' hFB⟩

theorem lemma_5_2_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase P.real)
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (f : A → B) (hf : Function.Bijective f)
    (hA : GammaSetDefinable P A) (hB : GammaSetDefinable P B)
    (hfDef : GammaGraphDefinable P (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q)) (hFinite : FiniteMixedRVFibres A) :
    ∃ S : Set M,
    ∃ hAr : SetDefinable (pointSpace 1 m) S A,
    ∃ hBr : SetDefinable (pointSpace 1 l) S B,
    ∃ hfr : RelationDefinable (pointSpace 1 m) (pointSpace 1 l) S
      (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q),
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S 1 r, ∃ B' : DefSet (M := M) S 1 s,
      ∃ TA : SpecialBijection (PresentedSet.mk A hAr) A',
      ∃ TB : SpecialBijection (PresentedSet.mk B hBr) B',
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB (Map.mk f hfr)) ∧
        Contractible (Map.inverse (unaryConjugate TA TB (Map.mk f hfr))
          (unaryConjugate_bijective TA TB (Map.mk f hfr) hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB (Map.mk f hfr))) ∧
        (∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB (Map.mk f hfr) a) ) ∧
        ∃ hVA : Map.FiniteFibres (rvObjectVolume (pullbackObject A')),
        ∃ hVB : Map.FiniteFibres (rvObjectVolume (pullbackObject B')),
        ∃ e : GammaRVFiniteIso P (⟨pullbackObject A',hVA⟩ : FiniteRVObject S 1)
          (⟨pullbackObject B',hVB⟩ : FiniteRVObject S 1),
          ∀ a : A', finiteRVHomMap e.iso.hom (Map.toImage (rawKeyMap A') a) =
            Map.toImage (rawKeyMap B') (unaryConjugate TA TB (Map.mk f hfr) a) := by
  obtain ⟨S,hAr,hBr,hfr,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hback,hΓ,hKeys⟩ :=
    lemma_5_2 hκ hs hsmall h00 δ hδ hδ1 FBase A B f hf hA hB hfDef
  have hFA := GammaIso.finite_mixed_rv_fibres hκ hs hsmall (gammaSpecialIso TA hTA) hFinite
  obtain ⟨hVA,hVB,e,hSquare⟩ := lemma_5_3_finite hκ hs hsmall
    (unaryConjugate TA TB (Map.mk f hfr))
    (unaryConjugate_bijective TA TB (Map.mk f hfr) hf) hc hback hA' hB' hΓ hFA
  exact ⟨S,hAr,hBr,hfr,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hback,hΓ,hKeys,hVA,hVB,e,hSquare⟩

end IntegrationInACVF.Section5
