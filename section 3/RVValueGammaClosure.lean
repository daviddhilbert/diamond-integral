import «section 3».ResidueTupleGammaClosure
import «section 3».RVFiniteValueGammaImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- RV angular parameters do not enlarge Gamma acl after their values are
named. All code representatives are removed from the output base. -/
theorem rv_tuple_gamma_algebraic_depends_on_values {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (c : Fin n → Code (M := M)) (δ : Values.Gamma (M := M))
    (hδ : GammaAlgebraicAtBase ⟨B.real ∪ Set.range (rawTuple c),B.gamma⟩ δ) :
    GammaDefinableClosureAtBase ⟨B.real,B.gamma ∪ Set.range (values c)⟩ δ := by
  let C : Base (M := M) := ⟨B.real,B.gamma ∪ Set.range (values c)⟩
  let D (i : Fin n) := Values.gammaPullback {values c i}
  have hD (i : Fin n) : DefinableAtBase C .rv (D i) :=
    gamma_name_definable C (values c i) (Or.inr (Set.mem_range_self i))
  have hvalues (i : Fin n) : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite := by
    apply (Set.finite_singleton (values c i).val).subset
    rintro _ ⟨t,ht,rfl⟩
    exact (rv_mem_value_fibre_iff (values c i) t).mp ht
  have ha (i : Fin n) : rawTuple c i ∈ D i :=
    (mem_gammaPullback_code {values c i} (c i)).mpr (by rfl)
  have hdC : GammaAlgebraicAtBase ⟨C.real ∪ Set.range (rawTuple c),C.gamma⟩ δ :=
    hδ.mono Set.Subset.rfl Set.subset_union_left
  exact residue_tuple_gamma_algebraic_elimination hκ hs h00 C hsmall D hD hvalues (rawTuple c) ha δ hdC
end DiamondIntegral.Section3
