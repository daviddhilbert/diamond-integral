import «section 6».StageShearChartFullDiscs
import «section 6».ScalarRVTemplateLevels

/-! The two entire continuous chart graphs of a local stage promote
to templates over the original base. The actual parameter tuple and
both full graph sections are retained, with unchanged RV selectors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

structure BranchedShearChartTemplate (S : Set M) (p n r s : ℕ) where
  indicator : ContinuousRVGraphTemplate (M := M) S p (r+s) (n+1) 1
  offset : ContinuousRVGraphTemplate (M := M) S p (r+s) n 1
  labels : Fin r → Fin s
  labels_injective : Function.Injective labels
  leading : Fin s

def BranchedShearChartTemplate.goodFunctions (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin p → M) :=
  T.indicator.good ∩ T.offset.good

theorem BranchedShearChartTemplate.goodFunctions_definable
    (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.goodFunctions :=
  T.indicator.good_definable.inter T.offset.good_definable

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_branched_shear_charts
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) {A : DefSet (rawMixedSpace (M := M) (n+1) r) (S ∪ Set.range a)}
    (D : BranchedShearData (G := G) A) :
    ∃ T : BranchedShearChartTemplate (M := M) S p n r D.arity,T.labels=D.labels ∧ T.leading=D.leading ∧
      a ∈ T.goodFunctions ∧
      {z : Fin (r+D.arity) ⊕ (Fin (n+1) ⊕ Fin 1) → M | Sum.elim a z ∈ T.indicator.graph}=rvVFGraph D.indicator ∧
      {z : Fin (r+D.arity) ⊕ (Fin n ⊕ Fin 1) → M | Sum.elim a z ∈ T.offset.graph}=rvVFGraph D.offset := by
  obtain ⟨I,hI,hIGraph⟩ := exists_promoted_continuous_rv_graph_template hv a D.indicator D.indicator_definable D.indicator_continuous
  obtain ⟨O,hO,hOGraph⟩ := exists_promoted_continuous_rv_graph_template hv a D.offset D.offset_definable D.offset_continuous
  exact ⟨⟨I,O,D.labels,D.labels_injective,D.leading⟩,rfl,rfl,⟨hI,hO⟩,hIGraph,hOGraph⟩

theorem exists_unary_branched_shear_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier) :
    Nonempty (BranchedShearData (G := G) A) := by
  obtain ⟨T⟩ := exists_unary_shear_contraction_stage h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA
  exact ⟨T.toBranchedData hc hv⟩

end DiamondIntegral.Section6
