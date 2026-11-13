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

/-- Proof-only common RV representatives do not create new definable
Gamma values. The conclusion returns to the original real/Gamma ground. -/
theorem common_names_gamma_definable_elimination {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (δ : Values.Gamma (M := M))
    (hδ : Values.GammaDefinable (commonRealNames B) {δ}) : GammaDefinableClosureAtBase B δ := by
  obtain ⟨p,φ,hφ,he⟩ := hδ.1
  have hnames (i : Fin p.length) : ∃ γ : Values.Gamma (M := M), GammaDefinableClosureAtBase B γ ∧
      (p.values i ∈ B.real ∨ p.values i = raw (representative γ)) := by
    rcases p.mem_base i with hi | ⟨γ,hγ,he⟩
    · exact ⟨1,nativeGamma_named_of_full_scalar B 1 (FullGammaSyntax.one_definable _),Or.inl hi⟩
    · exact ⟨γ,gamma_name_definable B γ hγ,Or.inr he.symm⟩
  choose γ hγ hp using hnames
  let a : Fin p.length → M := fun i => raw (representative (γ i))
  let C : Base (M := M) := ⟨B.real ∪ Set.range a,B.gamma⟩
  let p' : Parameters C.real :=
    { length := p.length
      values := p.values
      sorts := p.sorts
      sorted := p.sorted
      mem_base := by
        intro i
        rcases hp i with hi | hi
        · exact Or.inl hi
        · exact Or.inr ⟨i,hi.symm⟩ }
  have hreal : Values.GammaDefinable C.real {δ} := ⟨⟨p',φ,hφ,he⟩,hδ.2⟩
  have hδC : GammaDefinableClosureAtBase C δ := real_definableAtBase C .rv _ hreal
  let D : Fin p.length → Set M := fun i => Values.gammaPullback {γ i}
  have hD : ∀ i, DefinableAtBase B .rv (D i) := hγ
  have hv : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite := by
    intro i
    apply (Set.finite_singleton (γ i).val).subset
    rintro _ ⟨t,ht,rfl⟩
    exact (rv_mem_value_fibre_iff (γ i) t).mp ht
  have ha : ∀ i, a i ∈ D i := fun i =>
    (mem_gammaPullback_code {γ i} (representative (γ i))).mpr (representative_value (γ i))
  exact residue_tuple_gamma_algebraic_elimination hκ hs h00 B hsmall D hD hv a ha δ
    ((gamma_algebraic_iff_definable_base C δ).mpr hδC)
end DiamondIntegral.Section3
