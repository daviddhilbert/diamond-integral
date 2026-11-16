import «section 6».ProgramRVDataTraces

/-! Every complete program trace contains the full initial ambient
and protected leading-term data, including empty coordinate fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}

theorem CentripetalProgramTemplate.initial_data_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    ∀ D ∈ sourceRVDataTrace A P,D ∈ T.rvTrace A P := by
  induction T with
  | identity r =>
    intro D hD
    exact List.mem_append.mpr (Or.inl hD)
  | regularize r =>
    intro D hD
    exact List.mem_append.mpr (Or.inl hD)
  | centripetal T =>
    intro D hD
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hD)))
  | comp F H ihF ihH =>
    intro D hD
    exact List.mem_append.mpr (Or.inl (ihF A P D hD))

theorem CentripetalProgramTemplate.initial_ambient_data_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (⟨n+r,leadingRVImageTemplate A⟩ : RVDataTemplate S p) ∈ T.rvTrace A P := by
  apply T.initial_data_mem A P
  simp [sourceRVDataTrace]

theorem CentripetalProgramTemplate.initial_piece_data_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (i : Fin k) :
    (⟨n+r,leadingRVImageTemplate (P i)⟩ : RVDataTemplate S p) ∈ T.rvTrace A P := by
  apply T.initial_data_mem A P
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

end DiamondIntegral.Section6
