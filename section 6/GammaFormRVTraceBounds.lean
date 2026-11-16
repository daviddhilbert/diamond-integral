import «section 6».GammaFormRVTraces
import «section 6».MeasuredRVLiftData
import «section 6».GammaFormBounds
import Section3.SmallFiniteParameters

/-! Complete Gamma RV traces have bounded individual rows. The actual
form's value bounds follow from its proper source and open levels; a
finite Gamma image or an initial uniform bound over VF parameters is
not assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaForm_value_bounds
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ β : Gamma M,∀ t : A,β⁻¹ ≤ gammaMapValue ω t ∧ gammaMapValue ω t ≤ β := by
  obtain ⟨δ,hδ,hδ1,hConst⟩ := gammaFunction_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA
    (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  obtain ⟨β,hβ⟩ := locally_constant_gamma_bounded_named h00 hc linear hκ hs hv hsmall hΓ hA
    (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) δ hδ1 hδ hConst
  refine ⟨β,fun t => ?_⟩
  have h := hβ t.val t.property
  rw [gammaFormExtension_at ω t] at h
  exact h

theorem GammaFormParameterTemplate.rvTrace_doublyBounded_of_bounds
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hRV : RVSupportDoublyBounded A.carrier)
    (hBounds : ∃ δ : Gamma M,∀ t : A,δ⁻¹ ≤ gammaMapValue ω t ∧ gammaMapValue ω t ≤ δ) :
    RVValueDoublyBounded (W.rvTrace.fibre a).carrier := by
  obtain ⟨β,hβ⟩ := hRV
  obtain ⟨δ,hδ⟩ := hBounds
  let ρ := max β δ
  have hβρ : β ≤ ρ := le_max_left _ _
  have hδρ : δ ≤ ρ := le_max_right _ _
  refine ⟨ρ,?_⟩
  intro v hv i
  obtain ⟨t,hTags,hNZ,hCode⟩ := (W.rvTrace_entries a ω hW v).mp hv
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h := hβ t.val t.property j
    rw [hTags] at h
    exact ⟨(show (ρ⁻¹).val ≤ (β⁻¹).val from inv_le_inv' hβρ).trans h.1,
      h.2.trans (show β.val ≤ ρ.val from hβρ)⟩
  · fin_cases j
    let tag := v (Fin.natAdd r (0 : Fin 1))
    have hTag0 : tag ≠ rvZero M := by
      intro he
      exact hNZ.2 (congrArg Subtype.val he)
    have hValue : Values.vrv tag=(gammaMapValue ω t).val :=
      (nonzero_rv_codeValue_val tag hTag0).symm.trans (congrArg (fun γ : Gamma M => γ.val) hCode)
    change (ρ⁻¹).val ≤ Values.vrv tag ∧ Values.vrv tag ≤ ρ.val
    rw [hValue]
    have hBound : (δ⁻¹).val ≤ (gammaMapValue ω t).val ∧ (gammaMapValue ω t).val ≤ δ.val := hδ t
    exact ⟨(show (ρ⁻¹).val ≤ (δ⁻¹).val from inv_le_inv' hδρ).trans hBound.1,
      hBound.2.trans (show δ.val ≤ ρ.val from hδρ)⟩

theorem GammaFormParameterTemplate.rvTrace_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (hA : ProperInvariant (S ∪ Set.range a) A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    RVValueDoublyBounded (W.rvTrace.fibre a).carrier := by
  apply W.rvTrace_doublyBounded_of_bounds a ω hW hA.rvBounded
  exact gammaForm_value_bounds h00 hc linear hκ hs hv (small_union_range hκ.le S hsmall a)
    (hΓ.mono Set.subset_union_left (Set.Subset.rfl)) hA ω hLevels

end DiamondIntegral.Section6
