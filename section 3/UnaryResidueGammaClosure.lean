import «section 3».GoodGammaRVRelations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Naming a unary RV element of a ground-definable finite-value-support
set adds no new Gamma-algebraic values. The actual code-name extension is
eliminated from the conclusion. -/
theorem unary_residue_gamma_algebraic_elimination {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (hD : DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite)
    (a : M) (ha : a ∈ D) (δ : Values.Gamma (M := M))
    (hδ : GammaAlgebraicAtBase ⟨B.real ∪ Set.range ![a],B.gamma⟩ δ) :
    GammaDefinableClosureAtBase B δ := by
  have hasort : ∀ i : Fin 1, sortEval (SortTag.rv) (![a] i) := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hD.proper a ha
  obtain ⟨G,hG⟩ := good_base_gamma_relation_of_algebraic B (fun _ : Fin 1 => .rv) ![a] hasort δ hδ
  have hr : goodUnaryGammaRelation G δ a := hG
  exact rv_finite_value_gamma_correspondence_named hκ hs h00 B hsmall (goodUnaryGammaRelation G)
    (goodUnaryGammaRelation_sorted G) (goodUnaryGammaRelation_definable G) D hD hvalues
    (fun t _ => G.finite ![t]) a ha δ hr

theorem unary_residue_gamma_definable_elimination {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (hD : DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite)
    (a : M) (ha : a ∈ D) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase ⟨B.real ∪ Set.range ![a],B.gamma⟩ δ) :
    GammaDefinableClosureAtBase B δ :=
  unary_residue_gamma_algebraic_elimination hκ hs h00 B hsmall D hD hvalues a ha δ
    ((gamma_algebraic_iff_definable_base _ δ).mpr hδ)
end DiamondIntegral.Section3
