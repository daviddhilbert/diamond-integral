import «section 6».MeasuredSelectedProgramPrefixes

/-! A measured preparation after global regularization precomposes
with its literal protected images and retains the component form chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

theorem precompose_measured_regularization
    (h00 : M ⊨ Axioms.ACVF00)
    (X : SelectedProgramContext η A P C π σ)
    (hPA : ∀ b : B,∀ i,((P i).fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (F : MeasuredCoordinatePreparation (G := G) (regularizeMap C).image
      (fun i => rvLabelPullback (regularizeMap C).image
        (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
        (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i))))
      (fun i => rvLabelPullback_subset _ _ _) (regularizationGammaForm ω))
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) (regularizeMap C).image F.target F.map
      (fun i => rvLabelPullback (regularizeMap C).image
        (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
        (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i))))
      (regularizationGammaForm ω)) :
    ∃ J : MeasuredCoordinatePreparation (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) C J.target J.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let Q (i) := rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))
  have hQC (i) : (Q i).carrier ⊆ C.carrier := rvLabelPullback_subset C _ _
  have hImages (i) : ((regularization C).restrict (hQC i)).image.carrier ⊆ (regularizeMap C).image.carrier := by
    rintro z ⟨p,hp⟩
    exact hp ▸ ((regularization C).restrict (hQC i) p).property
  let F' : MeasuredCoordinatePreparation (G := G) (regularizeMap C).image
      (fun i => ((regularization C).restrict (hQC i)).image) hImages (regularizationGammaForm ω) :=
    F.changePieces (fun i => regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base)
  have hF' : FormCompatibleSynchronizedChain (G := G) (Fin k) (regularizeMap C).image F'.target F'.map
      (fun i => ((regularization C).restrict (hQC i)).image) (regularizationGammaForm ω) :=
    hF.changePieces (fun i => regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base)
  have hStage : SynchronizedCentripetalChain (G := G) (Fin k) C (regularizeMap C).image (regularization C) Q :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i))
  have hPhi : FormCompatibleSynchronizedChain (G := G) (Fin k) C (regularizeMap C).image (regularization C) Q ω :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i)) ω
  let J := MeasuredCoordinatePreparation.precompose h00 Q hQC (regularization C) hStage.toChain.toSpecial
    (fun i => ((hStage.atPiece i).literal_restriction h00 (hQC i))) hImages ω (regularizationGammaForm ω)
    (regularizationGammaForm_transport ω) F'
  exact ⟨J,.comp Q hQC hPhi (regularizationGammaForm ω) (regularizationGammaForm_transport ω) hF'⟩

end DiamondIntegral.Section6.SelectedProgramContext
