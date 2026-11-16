import «section 6».SequentialCentripetalPrograms
import «section 6».MeasuredProgramRVTraces
import «section 6».FormCompatibleProgramLoci

/-! Sequential normalization retains each component form guard, the
full terminal Gamma graph and all measured admissibility tests. Gamma
graph transport composes by actual first-order existential projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s t v k : ℕ}

theorem gammaTransitionImage_comp
    (F : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (H : Set (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ (Fin n ⊕ Fin t)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)) :
    gammaTransitionImage (parameterRelationComp F H) W=gammaTransitionImage H (gammaTransitionImage F W) := by
  ext z
  constructor
  · rintro ⟨x,⟨y,hF,hH⟩,hW⟩
    exact ⟨y,hH,x,hF,hW⟩
  · rintro ⟨y,hH,x,hF,hW⟩
    exact ⟨x,⟨y,hF,hH⟩,hW⟩

theorem GammaFormParameterTemplate.transport_program_comp
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    W.transport ((F.comp H).transition A)=(W.transport (F.transition A)).transport (H.transition (F.target A)) := by
  apply GammaFormParameterTemplate.ext_graph
  exact gammaTransitionImage_comp _ _ _

structure CentripetalProgramTemplate.SameFormData
    (F H : CentripetalProgramTemplate (M := M) S p n r s) : Prop extends F.SameData H where
  coreFormGood : ∀ A W,F.coreFormGood A W=H.coreFormGood A W

namespace CentripetalProgramTemplate.SameFormData

theorem refl (F : CentripetalProgramTemplate (M := M) S p n r s) : F.SameFormData F :=
  ⟨.refl F,fun _ _ => rfl⟩

theorem trans {F H K : CentripetalProgramTemplate (M := M) S p n r s}
    (hFH : F.SameFormData H) (hHK : H.SameFormData K) : F.SameFormData K :=
  ⟨hFH.toSameData.trans hHK.toSameData,fun A W => (hFH.coreFormGood A W).trans (hHK.coreFormGood A W)⟩

theorem comp {F F' : CentripetalProgramTemplate (M := M) S p n r s}
    {H H' : CentripetalProgramTemplate (M := M) S p n s t}
    (hF : F.SameFormData F') (hH : H.SameFormData H') : (F.comp H).SameFormData (F'.comp H') := by
  refine ⟨hF.toSameData.comp hH.toSameData,?_⟩
  intro A W
  change F.coreFormGood A W ∩ H.coreFormGood (F.target A) (W.transport (F.transition A))=_
  rw [hF.coreFormGood,hF.toSameData.target,hF.toSameData.transition,hH.coreFormGood]
  rfl

theorem assoc (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (K : CentripetalProgramTemplate (M := M) S p n t v) :
    ((F.comp H).comp K).SameFormData (F.comp (H.comp K)) := by
  refine ⟨.assoc F H K,?_⟩
  intro A W
  change (F.coreFormGood A W ∩ H.coreFormGood (F.target A) (W.transport (F.transition A))) ∩
      K.coreFormGood ((F.comp H).target A) (W.transport ((F.comp H).transition A))=_
  rw [F.target_comp H A,W.transport_program_comp F H A]
  exact Set.inter_assoc _ _ _

theorem measuredGood {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameFormData H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : F.measuredGood A P W=H.measuredGood A P W := by
  unfold CentripetalProgramTemplate.measuredGood
  rw [h.toSameData.preparedGood A P,h.toSameData.transition A]

theorem measuredFormGood {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameFormData H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : F.measuredFormGood A P W=H.measuredFormGood A P W := by
  unfold CentripetalProgramTemplate.measuredFormGood
  rw [h.measuredGood A P W,h.coreFormGood A W]

theorem measuredRVTrace {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameFormData H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : F.measuredRVTrace A P W=H.measuredRVTrace A P W := by
  unfold CentripetalProgramTemplate.measuredRVTrace CentripetalProgramTemplate.gammaRVTrace
  rw [h.toSameData.rvTrace A P,h.toSameData.transition A]

end CentripetalProgramTemplate.SameFormData

theorem CentripetalProgramSequence.append_sameFormData
    (F : CentripetalProgramSequence (M := M) S p n r s)
    (H : CentripetalProgramSequence (M := M) S p n s t) :
    (F.toProgram.comp H.toProgram).SameFormData (F.append H).toProgram := by
  induction F with
  | single F => exact CentripetalProgramTemplate.SameFormData.refl _
  | cons F K ih =>
    exact (CentripetalProgramTemplate.SameFormData.assoc F.toProgram K.toProgram H.toProgram).trans
      ((CentripetalProgramTemplate.SameFormData.refl F.toProgram).comp (ih H))

theorem CentripetalProgramTemplate.toSequence_sameFormData
    (F : CentripetalProgramTemplate (M := M) S p n r s) : F.SameFormData F.toSequence.toProgram := by
  induction F with
  | identity r => exact CentripetalProgramTemplate.SameFormData.refl _
  | regularize r => exact CentripetalProgramTemplate.SameFormData.refl _
  | centripetal T => exact CentripetalProgramTemplate.SameFormData.refl _
  | comp F H ihF ihH => exact (ihF.comp ihH).trans (F.toSequence.append_sameFormData H.toSequence)

end DiamondIntegral.Section6
