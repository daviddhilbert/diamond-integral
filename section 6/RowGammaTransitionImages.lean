import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowMeasuredProgramSubstitution

/-! (Row-form version for Remark 6.20, translated from `GammaTransitionImages`.)
 Actual Gamma graphs are transported through an entire transition
by first-order projection. For a bijective transition this is exactly
inverse composition, including every Gamma representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r s : ℕ}

def gammaTransitionImageRow
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) :
    Set (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ Fin qR) → M) :=
  {z | ∃ x : Fin n ⊕ Fin r → M,
    Sum.elim (z ∘ Sum.inl) (Sum.elim x (fun i => z (.inr (.inl i)))) ∈ R ∧
      Sum.elim (z ∘ Sum.inl) (Sum.elim x (fun i => z (.inr (.inr i)))) ∈ W}

theorem gammaTransitionImage_definable_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) : S.Definable LRV (gammaTransitionImageRow R W) := by
  let Z := (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ Fin qR)) ⊕ (Fin n ⊕ Fin r)
  have h₁ : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i)))
        (Sum.elim (z ∘ Sum.inr) (fun i => z (.inl (.inr (.inl i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have h₂ : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i)))
        (Sum.elim (z ∘ Sum.inr) (fun i => z (.inl (.inr (.inr i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  exact ((hR.preimage_map h₁).inter (hW.preimage_map h₂)).exists_of_finite

theorem gammaTransitionImage_at_row
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (hf : Function.Bijective f)
    (ω : RowFormOn A qR)
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph) :
    {z | Sum.elim a z ∈ gammaTransitionImageRow R W}=
      (rawMixedSpace n s).relation (rawRVSpace (M := M) qR) (ω.comp (f.inverse hf)).graph := by
  ext z
  constructor
  · rintro ⟨x,hRx,hWx⟩
    obtain ⟨hx,hy,t,ht,hft⟩ := (Set.ext_iff.mp hR _).mp hRx
    obtain ⟨hx',hγ,u,hu,hωu⟩ := (Set.ext_iff.mp hW _).mp hWx
    have htu : t=u := Subtype.ext (ht.trans hu.symm)
    subst u
    refine ⟨hy,hγ,f t,hft,?_⟩
    change _ ∈ (ω (f.inverse hf (f t))).val ∨ _
    rw [Map.inverse_apply]
    exact hωu
  · rintro ⟨hy,hγ,t,ht,hηt⟩
    let u := f.inverse hf t
    refine ⟨mixedValues u.val,?_,?_⟩
    · apply (Set.ext_iff.mp hR _).mpr
      refine ⟨mixedValues_mem_domain _,hy,u,(decode_mixedValues _).symm,?_⟩
      have he := congrArg (fun x : B => x.val) (Map.apply_inverse f hf t)
      exact he.trans ht
    · apply (Set.ext_iff.mp hW _).mpr
      exact ⟨mixedValues_mem_domain _,hγ,u,(decode_mixedValues _).symm,hηt⟩

def GammaFormParameterTemplateRow.transportRow
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (R : MixedTransitionParameterTemplate (M := M) S p n r s) : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n s :=
  ⟨gammaTransitionImageRow R.graph W.graph,gammaTransitionImage_definable_row _ _ R.definable W.definable⟩

theorem GammaFormParameterTemplateRow.ext_graph
    {W U : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r} (he : W.graph=U.graph) : W=U := by
  cases W
  cases U
  cases he
  rfl

theorem GammaFormParameterTemplateRow.transport_substitute_row
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (R : MixedTransitionParameterTemplate (M := M) S p n r s)
    (R' : MixedTransitionParameterTemplate (M := M) S q n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (he : R'.graph=parameterSubstitution h R.graph) :
    (W.transportRow R).substitute h=(W.substitute h).transportRow R' := by
  apply GammaFormParameterTemplateRow.ext_graph
  change parameterSubstitution h (gammaTransitionImageRow R.graph W.graph)=
    gammaTransitionImageRow R'.graph (parameterSubstitution h W.graph)
  rw [he]
  rfl

end DiamondIntegral.Section6
