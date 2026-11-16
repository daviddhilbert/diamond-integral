import «section 6».LeadingRVImageTemplates
import «section 6».CoefficientGraphTemplates
import «section 6».GammaNameParameterTemplates

/-! Coefficients and Gamma names enter the complete RV-data relation
as original-base templates. Their admissible rows are doubly bounded;
no uniform bound over the VF parameter family is presumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p m : ℕ}

def coefficientRVParameterCodes (z : Fin p ⊕ Fin 1 → M) : Fin 1 → M := fun _ => iRv (z (.inr 0))

theorem coefficientRVParameterCodes_definable :
    S.DefinableMap LRV (coefficientRVParameterCodes (M := M) (p := p)) := fun _ =>
  rv_scalarCode_definable (Set.DefinableFun.proj LRV)

def coefficientRVDataTemplate (C : ContinuousVFGraphTemplate (M := M) S p 0 1) :
    RVSetParameterTemplate (M := M) S p 1 :=
  ⟨parameterCodeImage (coefficientParameterGraph C) coefficientRVParameterCodes,
    parameterCodeImage_definable _ (coefficientParameterGraph_definable C) _ coefficientRVParameterCodes_definable⟩

theorem coefficientRVDataTemplate_fibre
    (C : ContinuousVFGraphTemplate (M := M) S p 0 1) (a : Fin p → M) (ha : a ∈ C.good) :
    ((coefficientRVDataTemplate C).fibre a).carrier={fun _ : Fin 1 => rv M (vfScalarTemplateValue C a ha)} := by
  ext u
  change rvValues u ∈ {z | Sum.elim a z ∈ parameterCodeImage (coefficientParameterGraph C) coefficientRVParameterCodes} ↔ _
  rw [parameterCodeImage_at]
  constructor
  · rintro ⟨c,hc,hOut⟩
    have hValue := (coefficientParameterGraph_at C a ha c).mp hc
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i
    apply Subtype.ext
    have h := congrFun hOut 0
    change iRv (c 0)=(u 0).val at h
    rw [hValue] at h
    exact h.symm
  · intro hu
    have h := Set.mem_singleton_iff.mp hu
    subst u
    refine ⟨(fun _ => (vfScalarTemplateValue C a ha).val),
      (coefficientParameterGraph_at C a ha _).mpr rfl,?_⟩
    rfl

theorem rvValueDoublyBounded_of_constant_value
    (U : Set (Fin m → RVInfinity M)) (γ : Gamma M)
    (hValue : ∀ u ∈ U,∀ i,Values.vrv (u i)=γ.val) : RVValueDoublyBounded U := by
  let δ := max γ γ⁻¹
  have hLow : (δ⁻¹).val ≤ γ.val := by
    have h : δ⁻¹ ≤ γ := by simpa only [inv_inv] using inv_le_inv' (le_max_right γ γ⁻¹)
    exact h
  refine ⟨δ,fun u hu i => ?_⟩
  rw [hValue u hu i]
  exact ⟨hLow,le_max_left _ _⟩

theorem nonzero_scalar_rv_singleton_doublyBounded (t : RVInfinity M) (ht : t ≠ rvZero M) :
    RVValueDoublyBounded ({fun _ : Fin 1 => t} : Set (Fin 1 → RVInfinity M)) := by
  apply rvValueDoublyBounded_of_constant_value _ (GammaParameters.codeValue t.val)
  rintro u hu i
  rw [Set.mem_singleton_iff.mp hu]
  exact (nonzero_rv_codeValue_val t ht).symm

theorem coefficientRVDataTemplate_doublyBounded
    (C : ContinuousVFGraphTemplate (M := M) S p 0 1) (a : Fin p → M) (ha : a ∈ C.good)
    (hc0 : vfScalarTemplateValue C a ha ≠ 0) : RVValueDoublyBounded ((coefficientRVDataTemplate C).fibre a).carrier := by
  rw [coefficientRVDataTemplate_fibre C a ha]
  exact nonzero_scalar_rv_singleton_doublyBounded _ (fun h => hc0 ((rv_eq_zero_iff _).mp h))

def gammaRVDataTemplate (B : GammaNameParameterTemplate (M := M) S p) : RVSetParameterTemplate (M := M) S p 1 :=
  ⟨B.graph,B.definable⟩

theorem gammaRVDataTemplate_doublyBounded
    (B : GammaNameParameterTemplate (M := M) S p) (a : Fin p → M) (ha : a ∈ B.good) :
    RVValueDoublyBounded ((gammaRVDataTemplate B).fibre a).carrier := by
  apply rvValueDoublyBounded_of_constant_value _ (B.value a ha)
  intro u hu i
  fin_cases i
  have hNZ := B.proper _ hu
  have hNe : u 0 ≠ rvZero M := fun h => hNZ.2 (congrArg Subtype.val h)
  have hValue := B.value_of_entry a ha (rvValues u) hu
  exact (nonzero_rv_codeValue_val (u 0) hNe).symm.trans (congrArg Subtype.val hValue)

end DiamondIntegral.Section6
