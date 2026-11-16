import «section 6».PackedRVDataTraces
import «section 6».FiniteProgramChoicePartitions

/-! One complete data relation for a finite formula-choice family.
Unit markers retain the choice even on empty fibres. Packed-row
constancy recovers the choice and every datum of its selected program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramTemplate.rvTrace_unit_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (⟨1,unitRVDataTemplate S p⟩ : RVDataTemplate (M := M) S p) ∈ T.rvTrace A P := by
  induction T with
  | identity r => simp [rvTrace,boundaryRVTrace,sourceRVDataTrace]
  | regularize r => simp [rvTrace,boundaryRVTrace,sourceRVDataTrace]
  | centripetal T => simp [rvTrace,boundaryRVTrace,sourceRVDataTrace]
  | comp F H ihF ihH => exact List.mem_append.mpr (Or.inl (ihF A P))

def choiceProgramRVTrace
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) : List (RVDataTemplate (M := M) S p) :=
  (List.ofFn (fun i => restrictRVTrace ((T i).2.rvTrace A P) (C i) (hC i))).flatten

theorem choiceProgramRVTrace_entry_mem
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (i : Fin l) (D : RVDataTemplate (M := M) S p) (hD : D ∈ (T i).2.rvTrace A P) :
    (⟨D.1,D.2.restrictParameters (C i) (hC i)⟩ : RVDataTemplate (M := M) S p) ∈ choiceProgramRVTrace T A P C hC := by
  apply List.mem_flatten.mpr
  refine ⟨restrictRVTrace ((T i).2.rvTrace A P) (C i) (hC i),List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
  exact List.mem_map.mpr ⟨D,hD,rfl⟩

theorem choiceProgramRVTrace_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hValid : ∀ i,∀ a ∈ C i,a ∈ (T i).2.good A P ∧ TemplateFibreGeometry A P a)
    (a : Fin p → M) : RVTraceRowsBounded a (choiceProgramRVTrace T A P C hC) := by
  intro D hD
  obtain ⟨E,hE,hDE⟩ := List.mem_flatten.mp hD
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE
  exact restrictRVTrace_bounded ((T i).2.rvTrace A P) (C i) (hC i) a
    (fun ha => (T i).2.rvTrace_bounded h00 hc hκ hs hv A P a (hValid i a ha).1 (hValid i a ha).2) D hDE

def choiceProgramRVData
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) :=
  packedRVTrace (choiceProgramRVTrace T A P C hC)

theorem choiceProgramRVData_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hValid : ∀ i,∀ a ∈ C i,a ∈ (T i).2.good A P ∧ TemplateFibreGeometry A P a)
    (a : Fin p → M) : RVValueDoublyBounded ((choiceProgramRVData T A P C hC).fibre a).carrier :=
  packedRVTrace_doublyBounded _ a (choiceProgramRVTrace_bounded h00 hc hκ hs hv T A P C hC hValid a)

theorem restricted_unit_nonempty_iff
    (X : Set (Fin p → M)) (hX : S.Definable LRV X) (a : Fin p → M) :
    (((unitRVDataTemplate (M := M) S p).restrictParameters X hX).fibre a).carrier.Nonempty ↔ a ∈ X := by
  rw [RVSetParameterTemplate.restrictParameters_fibre,unitRVDataTemplate_fibre]
  constructor
  · rintro ⟨u,ha,hu⟩
    exact ha
  · intro ha
    exact ⟨(fun _ => branchTag false),ha,rfl⟩

theorem choices_eq_of_program_data_eq
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((choiceProgramRVData T A P C hC).fibre a).carrier=((choiceProgramRVData T A P C hC).fibre b).carrier) :
    ∀ i,a ∈ C i ↔ b ∈ C i := by
  intro i
  have hRows := trace_rows_eq_of_packed_eq h00 (choiceProgramRVTrace T A P C hC) a b he
    ⟨1,(unitRVDataTemplate S p).restrictParameters (C i) (hC i)⟩
    (choiceProgramRVTrace_entry_mem T A P C hC i _ ((T i).2.rvTrace_unit_mem A P))
  rw [← restricted_unit_nonempty_iff (C i) (hC i) a,← restricted_unit_nonempty_iff (C i) (hC i) b,hRows]

theorem selected_trace_rows_eq_of_program_data_eq
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((choiceProgramRVData T A P C hC).fibre a).carrier=((choiceProgramRVData T A P C hC).fibre b).carrier)
    (i : Fin l) (ha : a ∈ C i) :
    ∀ D ∈ (T i).2.rvTrace A P,(D.2.fibre a).carrier=(D.2.fibre b).carrier := by
  intro D hD
  have hb := (choices_eq_of_program_data_eq h00 T A P C hC a b he i).mp ha
  have hRows := trace_rows_eq_of_packed_eq h00 (choiceProgramRVTrace T A P C hC) a b he
    ⟨D.1,D.2.restrictParameters (C i) (hC i)⟩ (choiceProgramRVTrace_entry_mem T A P C hC i D hD)
  rw [RVSetParameterTemplate.restrictParameters_fibre,RVSetParameterTemplate.restrictParameters_fibre] at hRows
  ext u
  have hAt := Set.ext_iff.mp hRows u
  simpa only [Set.mem_setOf_eq,ha,hb,true_and] using hAt

end DiamondIntegral.Section6
