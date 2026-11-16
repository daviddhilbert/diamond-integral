import «section 6».BinaryGraphParameterLoci

/-! First-order templates for parameter-definable Gamma values. The
name retains all proper representatives and never names a chosen RV
representative as an additional real parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

structure GammaNameParameterTemplate (S : Set M) (p : ℕ) where
  graph : Set (Fin p ⊕ Fin 1 → M)
  definable : S.Definable LRV graph
  proper : ∀ z ∈ graph,GammaParameters.NonzeroRV (z (.inr 0))

def gammaSameValueCodeCondition (p : ℕ) : Set (Fin p ⊕ (Fin 1 ⊕ Fin 1) → M) :=
  {z | ![z (.inr (.inl 0)),z (.inr (.inr 0))] ∈
    {w : Fin 2 → M | GammaParameters.NonzeroRV (w 0) ∧ GammaParameters.NonzeroRV (w 1) ∧
      iLe (w 0) (w 1) ∧ iLe (w 1) (w 0)}}

theorem gammaSameValueCodeCondition_definable :
    S.Definable LRV (gammaSameValueCodeCondition (M := M) p) := by
  have h := (GammaParameters.same_scalar_definable S).preimage_comp
    (![Sum.inr (Sum.inl 0),Sum.inr (Sum.inr 0)] : Fin 2 → Fin p ⊕ (Fin 1 ⊕ Fin 1))
  convert h using 1
  ext z
  rfl

namespace GammaNameParameterTemplate
def good (T : GammaNameParameterTemplate (M := M) S p) : Set (Fin p → M) :=
  {a | ∃ z : Fin 1 → M,Sum.elim a z ∈ T.graph} ∩
    binaryGraphConditionLocus T.graph (gammaSameValueCodeCondition p)

theorem good_definable (T : GammaNameParameterTemplate (M := M) S p) : S.Definable LRV T.good :=
  T.definable.exists_of_finite.inter
    (binaryGraphConditionLocus_definable _ _ T.definable gammaSameValueCodeCondition_definable)

def value (T : GammaNameParameterTemplate (M := M) S p) (a : Fin p → M) (ha : a ∈ T.good) : Gamma M :=
  GammaParameters.codeValue (ha.1.choose 0)

theorem value_of_entry (T : GammaNameParameterTemplate (M := M) S p)
    (a : Fin p → M) (ha : a ∈ T.good) (z : Fin 1 → M) (hz : Sum.elim a z ∈ T.graph) :
    GammaParameters.codeValue (z 0)=T.value a ha := by
  have h := ha.2 z ha.1.choose hz ha.1.choose_spec
  change GammaParameters.NonzeroRV (z 0) ∧ GammaParameters.NonzeroRV (ha.1.choose 0) ∧
    iLe (z 0) (ha.1.choose 0) ∧ iLe (ha.1.choose 0) (z 0) at h
  exact le_antisymm ((GammaParameters.original_le_codeValue_iff _ _ h.1 h.2.1).mp h.2.2.1)
    ((GammaParameters.original_le_codeValue_iff _ _ h.2.1 h.1).mp h.2.2.2)

theorem value_named (T : GammaNameParameterTemplate (M := M) S p)
    (a : Fin p → M) (ha : a ∈ T.good) :
    (S ∪ Set.range a).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {T.value a ha}} := by
  let Z := (Fin p ⊕ Fin 1) ⊕ Fin 1
  have hCompare := (GammaParameters.same_scalar_definable S).preimage_comp
    (![Sum.inr 0,Sum.inl (Sum.inr 0)] : Fin 2 → Z)
  have hCodes : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i))) (z ∘ Sum.inr)) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hEntry := T.definable.preimage_map hCodes
  have hExists := (hEntry.inter hCompare).exists_of_finite
  let fix (z : Fin 1 → M) : Fin p ⊕ Fin 1 → M := Sum.elim a z
  have hFix : (S ∪ Set.range a).DefinableMap LRV fix := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  convert (hExists.mono Set.subset_union_left).preimage_map hFix using 1
  ext z
  change z 0 ∈ Values.gammaPullback {T.value a ha} ↔
    ∃ w : Fin 1 → M,Sum.elim a w ∈ T.graph ∧
      GammaParameters.NonzeroRV (w 0) ∧ GammaParameters.NonzeroRV (z 0) ∧
        iLe (w 0) (z 0) ∧ iLe (z 0) (w 0)
  constructor
  · intro hz
    have ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    have hw := T.proper _ ha.1.choose_spec
    have hEq := (T.value_of_entry a ha ha.1.choose ha.1.choose_spec).trans
      ((GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz).symm
    exact ⟨ha.1.choose,ha.1.choose_spec,hw,ht,
      (GammaParameters.original_le_codeValue_iff _ _ hw ht).mpr hEq.le,
      (GammaParameters.original_le_codeValue_iff _ _ ht hw).mpr hEq.ge⟩
  · rintro ⟨w,hw,hwnz,hznz,hle,hge⟩
    apply (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hznz).mpr
    exact (le_antisymm ((GammaParameters.original_le_codeValue_iff _ _ hznz hwnz).mp hge)
      ((GammaParameters.original_le_codeValue_iff _ _ hwnz hznz).mp hle)).trans (T.value_of_entry a ha w hw)

end GammaNameParameterTemplate
end DiamondIntegral.Section6
