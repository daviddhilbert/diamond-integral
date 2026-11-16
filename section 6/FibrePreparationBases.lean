import «section 6».CoordinateFibreTemplates
import Section3.SmallFiniteParameters

/-! The field support and nontrivial valuation required by preparation
persist after adjoining the actual finite VF coordinate parameters.
The original smallness and definable Gamma hypotheses suffice. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S V : Set M} {p : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem preparation_algebraic_fields_mono {W : Set M} (hVW : V ⊆ W) :
    vfAlgebraicClosureField V ≤ vfAlgebraicClosureField W := by
  intro x hx
  exact (mem_vfAlgebraicClosureField W x).mpr
    (((mem_vfAlgebraicClosureField V x).mp hx).mono hVW)

theorem preparation_nontrivial_subfield_mono {K L : Subfield (VF M)} (hKL : K ≤ L)
    (hnt : ∃ x : K,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    ∃ x : L,x ≠ 0 ∧ Valued.v x.val ≠ 1 := by
  obtain ⟨x,hx0,hxv⟩ := hnt
  refine ⟨⟨x.val,hKL x.property⟩,?_,hxv⟩
  intro he
  exact hx0 (Subtype.ext (congrArg (fun y : L => y.val) he))

theorem vf_preparation_support_adjoin_tuple
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (a : Fin p → M) (ha : ∀ i,iVF (a i)) :
    (∀ x ∈ V ∪ Set.range a,iVF x) ∧ (V ∪ Set.range a ⊆ S ∪ Set.range a) ∧
      (S ∪ Set.range a ⊆ algebraicClosureSet (V ∪ Set.range a)) ∧
      (∃ x : vfAlgebraicClosureField (V ∪ Set.range a),x ≠ 0 ∧ Valued.v x.val ≠ 1) ∧
      Cardinal.mk ↥(S ∪ Set.range a) < κ ∧
      NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M) := by
  refine ⟨?_,Set.union_subset_union hVS (Set.Subset.rfl),?_,?_,
    small_union_range hκ S hsmall a,hΓ.mono Set.subset_union_left (Set.Subset.rfl)⟩
  · rintro x (hx | ⟨i,rfl⟩)
    · exact hV x hx
    · exact ha i
  · rintro x (hx | hx)
    · exact algebraicClosureSet_mono Set.subset_union_left (hSV hx)
    · exact subset_algebraicClosureSet _ (Or.inr hx)
  · exact preparation_nontrivial_subfield_mono
      (preparation_algebraic_fields_mono Set.subset_union_left) hnt

end DiamondIntegral.Section6
