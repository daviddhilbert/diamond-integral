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
import «section 6».RowMeasuredProgramSubstitution
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
import «section 6».RowGammaFormFreezing
import «section 6».FibrePreparationBases

/-! (Row-form version for Remark 6.20, translated from `HeadGammaFormMaps`.)
 Actual Gamma forms on the head-coordinate fibres, over exactly the
original base with that VF head adjoined. Complete graphs and open level
sets are inherited without adjoining any Gamma or RV representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n r : ℕ}

variable {P : SpecialTransformations.DefinableGeometry.Space LRV M}

def gammaFormExtendParametersRow {A : DefSet (rawMixedSpace (M := M) n r) S}
    (ω : RowFormOn A qR) (hST : S ⊆ T) :
    RowFormOn (⟨A.carrier,Space.Definable.mono (rawMixedSpace (M := M) n r) A.definable hST⟩ : DefSet (rawMixedSpace (M := M) n r) T) qR :=
  ⟨fun p => ⟨(ω ⟨p.val,p.property⟩).val,Set.mem_univ _⟩,Space.RelationDefinable.mono (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) qR) ω.rows_definable hST,by obtain ⟨γ,hγ⟩ := ω.bounded; exact ⟨γ,fun a v hv => hγ _ v hv⟩⟩

def headFibreEmbeddingRow
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (a : VF M) :
    Map ((headFibreTemplate A).fibre (fun _ => a.val))
      (⟨A.carrier,Space.Definable.mono (rawMixedSpace (n+1) r) A.definable Set.subset_union_left⟩ :
        DefSet (rawMixedSpace (M := M) (n+1) r) (S ∪ Set.range (fun _ : Fin 1 => a.val))) := by
  let C := (headFibreTemplate A).fibre (fun _ => a.val)
  let U := S ∪ Set.range (fun _ : Fin 1 => a.val)
  let e (p : Mixed M n r) : Mixed M (n+1) r := (Fin.cons a p.1,p.2)
  let F (z : Fin n ⊕ Fin r → M) : Fin (n+1) ⊕ Fin r → M :=
    Sum.elim (Fin.cons a.val (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hF : U.DefinableMap LRV F := by
    rintro (i | i)
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self (0 : Fin 1)))
      · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have he (p : Mixed M n r) : mixedValues (e p)=F (mixedValues p) := by
    funext i
    cases i with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr i => rfl
  have hcode (z : (rawMixedSpace (M := M) n r).domain) :
      mixedValues (e ((rawMixedSpace n r).decode z))=F z.val :=
    (he _).trans (congrArg F (mixedValues_decode z))
  have hdom (z : (rawMixedSpace (M := M) n r).domain) :
      F z.val ∈ (rawMixedSpace (M := M) (n+1) r).domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  let g := Map.ofCodes (Q := rawMixedSpace (M := M) (n+1) r) C e F hF hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨F z.val,hdom z⟩).trans (hcode z).symm))
  exact g.corestrict (fun p => (mem_headFibreTemplate_iff A a p.val).mp p.property)

theorem headFibreEmbedding_value_row
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (a : VF M)
    (p : (headFibreTemplate A).fibre (fun _ => a.val)) :
    (headFibreEmbeddingRow A a p).val=(Fin.cons a p.val.1,p.val.2) := rfl

def headGammaFormMapRow {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : RowFormOn A qR) (a : VF M) :
    RowFormOn ((headFibreTemplate A).fibre (fun _ => a.val)) qR :=
  (gammaFormExtendParametersRow ω Set.subset_union_left).comp (headFibreEmbeddingRow A a)

theorem headGammaFormMap_value_row {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : RowFormOn A qR) (a : VF M)
    (p : (headFibreTemplate A).fibre (fun _ => a.val)) :
    (headGammaFormMapRow ω a p).val=(ω ⟨(Fin.cons a p.val.1,p.val.2),
      (mem_headFibreTemplate_iff A a p.val).mp p.property⟩).val := rfl

theorem headGammaFormMap_levels_open_row
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : RowFormOn A qR) (a : VF M)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier ∧
      rowFormExtension (headGammaFormMapRow ω a) (x,u)=γ} := by
  intro u γ
  have he : {x : Fin n → VF M | (x,u) ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier ∧
      rowFormExtension (headGammaFormMapRow ω a) (x,u)=γ}=
      (fun x : Fin n → VF M => Fin.cons a x) ⁻¹'
        {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ} := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      have hAx := (mem_headFibreTemplate_iff A a (x,u)).mp hx
      refine ⟨hAx,?_⟩
      rw [rowFormExtension_at _ ⟨_,hx⟩,headGammaFormMap_value_row] at hγ
      rw [rowFormExtension_at _ ⟨_,hAx⟩]
      exact hγ
    · rintro ⟨hx,hγ⟩
      have hCx := (mem_headFibreTemplate_iff A a (x,u)).mpr hx
      refine ⟨hCx,?_⟩
      rw [rowFormExtension_at _ ⟨_,hCx⟩,headGammaFormMap_value_row]
      rw [rowFormExtension_at _ ⟨_,hx⟩] at hγ
      exact hγ
  rw [he]
  exact (hLevels u γ).preimage (by fun_prop)

end DiamondIntegral.Section6
