import «section 6».SelectedMeasuredTerminalPreparation

/-! A terminal regularization prepares all actual protected images and
makes the full ambient form constant on output labels. The complete
Gamma row compares parameters with the same retained base labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
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
variable {W : GammaFormParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

theorem measured_regularization_terminal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hBRP : IsRVPullback B.carrier)
    (U : UniformMeasuredProgramFamily (G := G) η (.regularize s) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSource : ∀ p : C,gammaFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∃ F : MeasuredCoordinatePreparation (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) C F.target F.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let Q (i) := rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))
  have hQC (i) : (Q i).carrier ⊆ C.carrier := rvLabelPullback_subset C _ _
  have hPA := fun b => (U.geometry b).subset
  let Y := X.afterRegularization h00 hc hκ hs hv hPA
  let F := Y.finish (G := G) hBRP U.toUniformProgramFamily.prepared_target_fibres
    (fun i => U.rows _ ((CentripetalProgramTemplate.regularize _).terminal_piece_data_mem A P i))
  let R (i) := rvLabelPullback (regularizeMap C).image
    (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
    (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i)))
  have hRC (i) : (R i).carrier ⊆ (regularizeMap C).image.carrier := rvLabelPullback_subset _ _ _
  have hPrepared (i) : IsRVPullback ((regularization C).restrict (hQC i)).image.carrier := by
    have h := F.prepared i
    have hIdentity : (F.map.restrict (hRC i)).image.carrier=(R i).carrier := by
      ext z
      exact ⟨fun ⟨p,hp⟩ => hp ▸ p.property,fun hp => ⟨⟨z,hp⟩,rfl⟩⟩
    rw [hIdentity] at h
    dsimp only [R] at h
    rw [regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base] at h
    exact h
  have hChain : SynchronizedCentripetalChain (G := G) (Fin k) C (regularizeMap C).image (regularization C) Q :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i))
  let J : PreparedSynchronizedFamily (G := G) C Q hQC := {
    arity := (n+1)+q
    target := (regularizeMap C).image
    map := regularization C
    chain := hChain
    proper := regularization_properInvariant h00 hc hκ hs hv C X.proper X.doublyBounded
    doublyBounded := regularized_vfDoublyBounded X.doublyBounded
    pullback := regularization_rvPullback C X.pullback
    prepared := hPrepared }
  have hPhi : FormCompatibleSynchronizedChain (G := G) (Fin k) C J.target J.map Q ω :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i)) ω
  apply J.measured_form_compatible_target h00 hc hκ hs hv ω hPhi
  intro p z hTags
  change (regularize p.val).2=(regularize z.val).2 at hTags
  have hOldTags : p.val.2=z.val.2 := by
    funext i
    have h := congrFun hTags (Fin.natAdd (n+1) i)
    change (regularize p.val).2 (Fin.natAdd (n+1) i)=(regularize z.val).2 (Fin.natAdd (n+1) i) at h
    simpa only [regularize,Fin.append_right] using h
  let b := X.baseMap p
  let c := X.baseMap z
  let x := X.localSourcePoint p
  let y := X.localSourcePoint z
  have hLocalTags : (regularization (A.fibre (unaryFamilyParameter η b)) x).val.2=
      (regularization (A.fibre (unaryFamilyParameter η c)) y).val.2 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have h := congrFun hTags (Fin.castAdd q j.succ)
      simp only [regularize,Fin.append_left] at h
      simp only [regularization_apply,regularize,Fin.append_left]
      change rv M (p.val.1 j.succ)=rv M (z.val.1 j.succ)
      exact h
    · simp only [regularization_apply,regularize,Fin.append_right]
      change p.val.2 (σ j)=z.val.2 (σ j)
      exact congrFun hOldTags (σ j)
  have hValue := U.values_eq_of_transition_labels b c (X.baseMap_labels p z hOldTags)
    (regularization (A.fibre (unaryFamilyParameter η b))) (regularization_bijective _)
    (regularization (A.fibre (unaryFamilyParameter η c))) (regularization_bijective _)
    (regularizationParameterTransition_at A _) (regularizationParameterTransition_at A _) x y hLocalTags
  have hExt := (gammaFormExtension_at (U.forms b) x).trans
    (hValue.trans (gammaFormExtension_at (U.forms c) y).symm)
  exact (hSource p).symm.trans (hExt.trans (hSource z))

end DiamondIntegral.Section6.SelectedProgramContext
