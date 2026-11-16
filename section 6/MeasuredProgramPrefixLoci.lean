import «section 6».SequentialMeasuredCentripetalPrograms
import «section 6».UniformProgramFamilies

/-! Removing a program prefix transports the complete Gamma graph and
retains the terminal constancy test and all remaining component guards.
The prefix itself needs its component guards, without terminal constancy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s t k : ℕ}

theorem gammaTransitionConstantParameterLocus_codes_iff
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)) (a : Fin p → M) :
    a ∈ gammaTransitionConstantParameterLocus R W ↔
      ∀ (x : Fin n ⊕ Fin r → M) (y : Fin n ⊕ Fin s → M) (c : (rawGammaPresentation (M := M)).Index → M)
        (x' : Fin n ⊕ Fin r → M) (y' : Fin n ⊕ Fin s → M) (c' : (rawGammaPresentation (M := M)).Index → M),
        Sum.elim a (Sum.elim x y) ∈ R → Sum.elim a (Sum.elim x c) ∈ W →
        Sum.elim a (Sum.elim x' y') ∈ R → Sum.elim a (Sum.elim x' c') ∈ W →
        (∀ j : Fin s,y (.inr j)=y' (.inr j)) →
        Sum.elim c c' ∈ (rawGammaPresentation (M := M)).relation rawGammaPresentation Eq := by
  constructor
  · intro h x y c x' y' c' hR hW hR' hW' hTags
    exact h (Sum.elim x (Sum.elim y c)) (Sum.elim x' (Sum.elim y' c')) ⟨hR,hW⟩ ⟨hR',hW'⟩ hTags
  · intro h z z' hz hz' hTags
    exact h (z ∘ Sum.inl) (fun i => z (.inr (.inl i))) (fun i => z (.inr (.inr i)))
      (z' ∘ Sum.inl) (fun i => z' (.inr (.inl i))) (fun i => z' (.inr (.inr i)))
      hz.1 hz.2 hz'.1 hz'.2 hTags

theorem gammaTransitionConstantParameterLocus_comp
    (F : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (H : Set (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ (Fin n ⊕ Fin t)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)) :
    gammaTransitionConstantParameterLocus (parameterRelationComp F H) W=
      gammaTransitionConstantParameterLocus H (gammaTransitionImage F W) := by
  ext a
  rw [gammaTransitionConstantParameterLocus_codes_iff,gammaTransitionConstantParameterLocus_codes_iff]
  constructor
  · intro h y z c y' z' c' hH hFW hH' hFW' hTags
    obtain ⟨x,hF,hW⟩ := hFW
    obtain ⟨x',hF',hW'⟩ := hFW'
    exact h x z c x' z' c' ⟨y,hF,hH⟩ hW ⟨y',hF',hH'⟩ hW' hTags
  · intro h x z c x' z' c' hFH hW hFH' hW' hTags
    obtain ⟨y,hF,hH⟩ := hFH
    obtain ⟨y',hF',hH'⟩ := hFH'
    exact h y z c y' z' c' hH ⟨x,hF,hW⟩ hH' ⟨x',hF',hW'⟩ hTags

theorem CentripetalProgramTemplate.preparedGood_comp_full_parameters
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (F.comp H).preparedGood A P=F.good A P ∩ H.preparedGood (F.target A) (fun i => F.pieceTarget A (P i)) := by
  simp only [CentripetalProgramTemplate.preparedGood,CentripetalProgramTemplate.good,
    CentripetalProgramTemplate.pieceTarget_comp,Set.inter_assoc]

theorem CentripetalProgramTemplate.measuredGood_comp
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) :
    (F.comp H).measuredGood A P W=F.good A P ∩
      H.measuredGood (F.target A) (fun i => F.pieceTarget A (P i)) (W.transport (F.transition A)) := by
  unfold CentripetalProgramTemplate.measuredGood
  rw [F.preparedGood_comp_full_parameters H A P]
  change (F.good A P ∩ H.preparedGood (F.target A) (fun i => F.pieceTarget A (P i))) ∩
      gammaTransitionConstantParameterLocus (parameterRelationComp (F.transition A).graph (H.transition (F.target A)).graph) W.graph=_
  rw [gammaTransitionConstantParameterLocus_comp]
  exact Set.inter_assoc _ _ _

theorem CentripetalProgramTemplate.measuredFormGood_comp
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) :
    (F.comp H).measuredFormGood A P W=(F.good A P ∩ F.coreFormGood A W) ∩
      H.measuredFormGood (F.target A) (fun i => F.pieceTarget A (P i)) (W.transport (F.transition A)) := by
  unfold CentripetalProgramTemplate.measuredFormGood
  rw [CentripetalProgramTemplate.measuredGood_comp]
  ext a
  change ((a ∈ F.good A P ∧ a ∈ H.measuredGood _ _ _) ∧
      a ∈ F.coreFormGood A W ∧ a ∈ H.coreFormGood _ _) ↔
    ((a ∈ F.good A P ∧ a ∈ F.coreFormGood A W) ∧ a ∈ H.measuredGood _ _ _ ∧ a ∈ H.coreFormGood _ _)
  tauto

theorem CentripetalProgramTemplate.measuredRVTrace_afterPrefix_subset
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) :
    ∀ D ∈ H.measuredRVTrace (F.target A) (fun i => F.pieceTarget A (P i)) (W.transport (F.transition A)),
      D ∈ (F.comp H).measuredRVTrace A P W := by
  intro D hD
  rcases List.mem_append.mp hD with hD | hD
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hD)))
  · have he : D=(⟨t+1,H.gammaRVTrace (F.target A) (W.transport (F.transition A))⟩ : RVDataTemplate (M := M) S p) :=
      List.mem_singleton.mp hD
    subst D
    have hTrace : H.gammaRVTrace (F.target A) (W.transport (F.transition A))=(F.comp H).gammaRVTrace A W := by
      unfold CentripetalProgramTemplate.gammaRVTrace
      rw [W.transport_program_comp]
    rw [hTrace]
    exact (F.comp H).gammaRVTrace_mem A P W

end DiamondIntegral.Section6
