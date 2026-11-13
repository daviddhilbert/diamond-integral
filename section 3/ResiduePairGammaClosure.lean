import «section 3».ResidueTupleGammaClosure
import «section 3».RVFiniteValueGammaClosure
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]



/-- Two finite tuples of residue parameters add no Gamma-algebraic value. -/
theorem residue_pair_gamma_algebraic_elimination {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n m : ℕ} (D : Fin n → Set M) (E : Fin m → Set M)
    (hD : ∀ i, DefinableAtBase B .rv (D i)) (hE : ∀ i, DefinableAtBase B .rv (E i))
    (hDv : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hEv : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ E i}).Finite)
    (a : Fin n → M) (ha : ∀ i, a i ∈ D i) (b : Fin m → M) (hb : ∀ i, b i ∈ E i)
    (δ : Values.Gamma (M := M))
    (hδ : GammaAlgebraicAtBase ⟨(B.real ∪ Set.range a) ∪ Set.range b,B.gamma⟩ δ) :
    GammaDefinableClosureAtBase B δ := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range a,B.gamma⟩
  have hcsmall := small_union_range hκ B.real hsmall a
  have hδC : GammaDefinableClosureAtBase C δ :=
    residue_tuple_gamma_algebraic_elimination hκ hs h00 C hcsmall E
      (fun i => (hE i).mono Set.subset_union_left Set.Subset.rfl) hEv b hb δ hδ
  exact residue_tuple_gamma_algebraic_elimination hκ hs h00 B hsmall D hD hDv a ha δ
    ((gamma_algebraic_iff_definable_base C δ).mpr hδC)
end DiamondIntegral.Section3
