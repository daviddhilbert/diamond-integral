import «section 6».ConstrainedContinuousVFTemplates

/-! Named VF coefficients use the zero-input case of the checked
continuous graph templates. Their actual values retain complete names
over the original base and the existing real parameter tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

def vfScalarTemplateValue (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (a : Fin p → M) (ha : a ∈ T.good) : VF M := T.value a ha Fin.elim0 0

theorem vfScalarTemplateValue_named (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (a : Fin p → M) (ha : a ∈ T.good) :
    (S ∪ Set.range a).Definable₁ LRV {(vfScalarTemplateValue T a ha).val} := by
  let fix (z : Fin 1 → M) := Sum.elim a (Sum.elim (Fin.elim0 : Fin 0 → M) z)
  have hFix : (S ∪ Set.range a).DefinableMap LRV fix := by
    rintro (i | (i | i))
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact i.elim0
    · exact Set.DefinableFun.proj LRV
  change (S ∪ Set.range a).Definable LRV {z : Fin 1 → M | z 0=(vfScalarTemplateValue T a ha).val}
  convert (T.definable.mono Set.subset_union_left).preimage_map hFix using 1
  ext z
  change z 0=(vfScalarTemplateValue T a ha).val ↔ Sum.elim a (Sum.elim Fin.elim0 z) ∈ T.graph
  constructor
  · intro hz
    apply (Set.ext_iff.mp (T.value_graph a ha) _).mpr
    refine ⟨Fin.elim0,?_⟩
    funext i
    cases i with
    | inl i => exact i.elim0
    | inr i => fin_cases i; exact hz.symm
  · intro hz
    obtain ⟨x,hx⟩ := (Set.ext_iff.mp (T.value_graph a ha) _).mp hz
    have hInput : x=Fin.elim0 := funext (fun i => i.elim0)
    subst x
    exact (congrFun hx (.inr 0)).symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_vf_scalar_name_template
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) (c : VF M) (hc : (S ∪ Set.range a).Definable₁ LRV {c.val}) :
    ∃ T : ContinuousVFGraphTemplate (M := M) S p 0 1,∃ ha : a ∈ T.good,
      vfScalarTemplateValue T a ha=c := by
  let f (_ : Fin 0 → VF M) : Fin 1 → VF M := fun _ => c
  have hGraph : (S ∪ Set.range a).Definable LRV (vfGraph f) := by
    have hcRaw : (S ∪ Set.range a).Definable LRV {z : Fin 1 → M | z 0=c.val} := hc
    convert hcRaw.preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : Fin 0 ⊕ Fin 1)) using 1
    ext z
    constructor
    · rintro ⟨x,hx⟩
      exact (congrFun hx (.inr 0)).symm
    · intro hz
      refine ⟨Fin.elim0,?_⟩
      funext i
      cases i with
      | inl i => exact i.elim0
      | inr i => fin_cases i; exact hz.symm
  obtain ⟨T,ha,hSection⟩ := exists_promoted_continuous_vf_graph_template hv a f hGraph continuous_const
  have hChosen := (Set.ext_iff.mp hSection _).mp (T.value_mem a ha Fin.elim0)
  obtain ⟨x,hx⟩ := hChosen
  exact ⟨T,ha,Subtype.ext (congrFun hx (.inr 0)).symm⟩

end DiamondIntegral.Section6
