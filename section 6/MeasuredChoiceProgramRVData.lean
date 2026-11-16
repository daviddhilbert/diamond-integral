import «section 6».ChoiceProgramRVData
import «section 6».MeasuredProgramRVTraces
import «section 6».FiniteProgramChoicePartitions

/-! One complete measured data relation for a finite formula-choice family.
Unit markers retain the choice even on empty fibres. Packed-row
constancy recovers the choice, every geometric datum, and the full terminal Gamma graph of its selected program. -/

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

theorem CentripetalProgramTemplate.measuredRVTrace_unit_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) :
    (⟨1,unitRVDataTemplate S p⟩ : RVDataTemplate (M := M) S p) ∈ T.measuredRVTrace A P W :=
  List.mem_append.mpr (Or.inl (T.rvTrace_unit_mem A P))

def measuredChoiceProgramRVTrace
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) : List (RVDataTemplate (M := M) S p) :=
  (List.ofFn (fun i => restrictRVTrace ((T i).2.measuredRVTrace A P W) (C i) (hC i))).flatten

theorem measuredChoiceProgramRVTrace_entry_mem
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (i : Fin l) (D : RVDataTemplate (M := M) S p) (hD : D ∈ (T i).2.measuredRVTrace A P W) :
    (⟨D.1,D.2.restrictParameters (C i) (hC i)⟩ : RVDataTemplate (M := M) S p) ∈ measuredChoiceProgramRVTrace T A P W C hC := by
  apply List.mem_flatten.mpr
  refine ⟨restrictRVTrace ((T i).2.measuredRVTrace A P W) (C i) (hC i),List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
  exact List.mem_map.mpr ⟨D,hD,rfl⟩

theorem measuredChoiceProgramRVTrace_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hValid : ∀ i,∀ a ∈ C i,a ∈ (T i).2.good A P ∧ TemplateFibreGeometry A P a)
    (hForm : ∀ i,∀ a ∈ C i,∃ ω : Map (A.fibre a)
      (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)),
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph ∧
      ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ gammaFormExtension ω (x,u)=γ})
    (a : Fin p → M) : RVTraceRowsBounded a (measuredChoiceProgramRVTrace T A P W C hC) := by
  intro D hD
  obtain ⟨E,hE,hDE⟩ := List.mem_flatten.mp hD
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE
  apply restrictRVTrace_bounded ((T i).2.measuredRVTrace A P W) (C i) (hC i) a _ D hDE
  intro ha
  obtain ⟨ω,hW,hLevels⟩ := hForm i a ha
  exact (T i).2.measuredRVTrace_bounded h00 hc linear hκ hs hv hsmall hΓ A P W a
    (hValid i a ha).1 (hValid i a ha).2 ω hW hLevels

def measuredChoiceProgramRVData
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) :=
  packedRVTrace (measuredChoiceProgramRVTrace T A P W C hC)

theorem measuredChoiceProgramRVData_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hValid : ∀ i,∀ a ∈ C i,a ∈ (T i).2.good A P ∧ TemplateFibreGeometry A P a)
    (hForm : ∀ i,∀ a ∈ C i,∃ ω : Map (A.fibre a)
      (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)),
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph ∧
      ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ gammaFormExtension ω (x,u)=γ})
    (a : Fin p → M) : RVValueDoublyBounded ((measuredChoiceProgramRVData T A P W C hC).fibre a).carrier :=
  packedRVTrace_doublyBounded _ a (measuredChoiceProgramRVTrace_bounded h00 hc hκ hs hv linear hsmall hΓ T A P W C hC hValid hForm a)

theorem choices_eq_of_measured_program_data_eq
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((measuredChoiceProgramRVData T A P W C hC).fibre a).carrier=((measuredChoiceProgramRVData T A P W C hC).fibre b).carrier) :
    ∀ i,a ∈ C i ↔ b ∈ C i := by
  intro i
  have hRows := trace_rows_eq_of_packed_eq h00 (measuredChoiceProgramRVTrace T A P W C hC) a b he
    ⟨1,(unitRVDataTemplate S p).restrictParameters (C i) (hC i)⟩
    (measuredChoiceProgramRVTrace_entry_mem T A P W C hC i _ ((T i).2.measuredRVTrace_unit_mem A P W))
  rw [← restricted_unit_nonempty_iff (C i) (hC i) a,← restricted_unit_nonempty_iff (C i) (hC i) b,hRows]

theorem selected_trace_rows_eq_of_measured_program_data_eq
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((measuredChoiceProgramRVData T A P W C hC).fibre a).carrier=((measuredChoiceProgramRVData T A P W C hC).fibre b).carrier)
    (i : Fin l) (ha : a ∈ C i) :
    ∀ D ∈ (T i).2.measuredRVTrace A P W,(D.2.fibre a).carrier=(D.2.fibre b).carrier := by
  intro D hD
  have hb := (choices_eq_of_measured_program_data_eq h00 T A P W C hC a b he i).mp ha
  have hRows := trace_rows_eq_of_packed_eq h00 (measuredChoiceProgramRVTrace T A P W C hC) a b he
    ⟨D.1,D.2.restrictParameters (C i) (hC i)⟩ (measuredChoiceProgramRVTrace_entry_mem T A P W C hC i D hD)
  rw [RVSetParameterTemplate.restrictParameters_fibre,RVSetParameterTemplate.restrictParameters_fibre] at hRows
  ext u
  have hAt := Set.ext_iff.mp hRows u
  simpa only [Set.mem_setOf_eq,ha,hb,true_and] using hAt

end DiamondIntegral.Section6
