import «section 6».FusionResidualGammaGeometry

/-! After a final local centripetal component, the residual is already
prepared. Full terminal Gamma rows, including comparisons between head
parameters, supply its actual measured preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.MeasuredCentripetalFusionRepair
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {K : FocusComponentParameterTemplate (M := M) S 1 (n+1) s}
variable {A : MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {W : GammaFormParameterTemplate (M := M) S 1 (n+1) s}
variable {C : DefSet (rawMixedSpace (M := M) (n+2) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable {ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (R : MeasuredCentripetalFusionRepair (G := G) η (.centripetal K) K A P W C π σ ω)

theorem terminal_residual_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hBRP : IsRVPullback B.carrier)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈
      (CentripetalProgramTemplate.centripetal K).rvTrace A P) :
    ∃ F : MeasuredCoordinatePreparation (G := G) (R.geometric.residualTarget hCoeffMem)
        (R.geometric.residualPiece hCoeffMem) (R.geometric.residualPiece_subset hCoeffMem)
        (R.geometric.fusionResidualGammaMap h00 hCoeffMem ω),
      FormCompatibleSynchronizedChain (G := G) (Fin k) (R.geometric.residualTarget hCoeffMem) F.target F.map
        (R.geometric.residualPiece hCoeffMem) (R.geometric.fusionResidualGammaMap h00 hCoeffMem ω) := by
  let Y := R.geometric.residualContext h00 hc hκ hs hv hCoeffMem
  let J := Y.finish (G := G) hBRP R.family.toUniformProgramFamily.prepared_target_fibres
    (fun i => R.family.rows _ ((CentripetalProgramTemplate.centripetal K).terminal_piece_data_mem A P i))
  let Ω := R.geometric.fusionResidualGammaMap h00 hCoeffMem ω
  have hPhi : FormCompatibleSynchronizedChain (G := G) (Fin k) (R.geometric.residualTarget hCoeffMem)
      J.target J.map
      (fun i => rvLabelPullback (R.geometric.residualTarget hCoeffMem)
        (Fin.addCases (centripetalBaseLabels R.geometric.component π) (centripetalLocalLabels R.geometric.component σ))
        (unaryIndexedMixedFamily R.geometric.parameter ((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i)))) Ω :=
    .identity _ Y.proper _ (fun i => rvLabelPullback_subset _ _ _) Y.piecesProper Ω
  obtain ⟨F,hF⟩ := J.measured_form_compatible_target h00 hc hκ hs hv Ω hPhi (by
    intro z w hTags
    change z.val.2=w.val.2 at hTags
    obtain ⟨p,hp⟩ := R.geometric.stage_preimage ⟨z.val,z.property.1⟩
    obtain ⟨q,hq⟩ := R.geometric.stage_preimage ⟨w.val,w.property.1⟩
    let b := R.geometric.context.baseMap p
    let c := R.geometric.context.baseMap q
    let x := R.geometric.localSourcePoint p
    let y := R.geometric.localSourcePoint q
    have hBase : b.val.2=c.val.2 := by
      change (R.geometric.context.baseMap p).val.2=(R.geometric.context.baseMap q).val.2
      rw [← R.geometric.residual_baseMap_at_preimage h00 hc hκ hs hv hCoeffMem z p hp,
        ← R.geometric.residual_baseMap_at_preimage h00 hc hκ hs hv hCoeffMem w q hq]
      exact Y.baseMap_labels z w hTags
    have hLocalTags : ((R.geometric.fibreComponents.component b).bijection x).val.2=
        ((R.geometric.fibreComponents.component c).bijection y).val.2 := by
      have h := congrArg (fun u => u ∘ centripetalLocalLabels R.geometric.component σ) hTags
      have hz := R.geometric.residual_local_at_preimage h00 hCoeffMem z p hp
      have hw := R.geometric.residual_local_at_preimage h00 hCoeffMem w q hq
      exact (congrArg Prod.snd hz).symm.trans (h.trans (congrArg Prod.snd hw))
    have hValue := R.family.values_eq_of_transition_labels b c hBase
      (R.geometric.fibreComponents.component b).bijection ((R.geometric.fibreComponents.component b).bijective h00)
      (R.geometric.fibreComponents.component c).bijection ((R.geometric.fibreComponents.component c).bijective h00)
      (R.geometric.fibreComponents.component_transition_graph b) (R.geometric.fibreComponents.component_transition_graph c)
      x y hLocalTags
    have hSource := (R.sourceForm p).symm.trans ((gammaFormExtension_at (R.family.forms b) x).trans
      (hValue.trans ((gammaFormExtension_at (R.family.forms c) y).symm.trans (R.sourceForm q))))
    exact (R.geometric.fusionResidualGammaMap_at_preimage h00 hCoeffMem ω z p hp).trans
      (hSource.trans (R.geometric.fusionResidualGammaMap_at_preimage h00 hCoeffMem ω w q hq).symm))
  exact ⟨F.changePieces (fun i => R.geometric.residual_piece_eq h00 hCoeffMem i),
    hF.changePieces (fun i => R.geometric.residual_piece_eq h00 hCoeffMem i)⟩

end DiamondIntegral.Section6.MeasuredCentripetalFusionRepair
