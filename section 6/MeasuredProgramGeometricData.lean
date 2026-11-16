import «section 6».MeasuredCoordinateProgramData

/-! The complete measured record recovers the exact older geometric
record. This lets the existing actual fusion constructions be reused
while the additional full Gamma graph remains available. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k l : ℕ}

theorem packedRVTrace_eq_of_rows_eq
    (D : List (RVDataTemplate (M := M) S p)) (a b : Fin p → M)
    (he : ∀ T ∈ D,(T.2.fibre a).carrier=(T.2.fibre b).carrier) :
    ((packedRVTrace D).fibre a).carrier=((packedRVTrace D).fibre b).carrier := by
  unfold packedRVTrace packedRVDataFamily
  rw [RVSetParameterTemplate.finiteUnion_fibre,RVSetParameterTemplate.finiteUnion_fibre]
  congr 1
  funext i
  rw [packedRVDataTemplate_fibre,packedRVDataTemplate_fibre,he (D.get i) (List.get_mem D i)]

theorem choiceProgramRVTrace_subset_measured
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) :
    ∀ D ∈ choiceProgramRVTrace T A P C hC,D ∈ measuredChoiceProgramRVTrace T A P W C hC := by
  intro D hD
  obtain ⟨E,hE,hDE⟩ := List.mem_flatten.mp hD
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE
  obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hDE
  exact measuredChoiceProgramRVTrace_entry_mem T A P W C hC i F (List.mem_append.mpr (Or.inl hF))

theorem geometric_data_eq_of_measured_data_eq
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((measuredChoiceProgramRVData T A P W C hC).fibre a).carrier=
      ((measuredChoiceProgramRVData T A P W C hC).fibre b).carrier) :
    ((choiceProgramRVData T A P C hC).fibre a).carrier=((choiceProgramRVData T A P C hC).fibre b).carrier := by
  apply packedRVTrace_eq_of_rows_eq
  intro D hD
  exact trace_rows_eq_of_packed_eq h00 _ a b he D (choiceProgramRVTrace_subset_measured T A P W C hC D hD)

def FiniteMeasuredCoordinateProgramData.forget
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F : FiniteMeasuredCoordinateProgramData A P ω) : FiniteCoordinateProgramData A P := {
  count := F.count
  programs := F.programs
  choices := F.choices
  choices_definable := F.choices_definable
  choices_subset := fun i a ha => ⟨(F.choices_subset i ha).1,(F.choices_subset i ha).2.1.1⟩
  cover := F.cover
  disjoint := F.disjoint
  geometry := F.geometry }

end DiamondIntegral.Section6
