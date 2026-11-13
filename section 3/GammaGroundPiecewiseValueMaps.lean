import «section 3».RVGammaFormValuePartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Finite original-ground Gamma functions glue on an actual definable
partition to an interpreted Gamma map. No RV lift is asserted here. -/
theorem gammaGroundGamma_piecewise_value_map {ι : Type} [Finite ι]
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (P : ι → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (hsub : ∀ i, (P i).carrier ⊆ G.carrier)
    (hpart : ∀ γ ∈ G.carrier, ∃! i, γ ∈ (P i).carrier)
    (F : ι → GammaValueFunctionData B n) :
    ∃ f : GammaGroundMap G (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)),
      ∀ i (γ : G), γ.val ∈ (P i).carrier → (f γ).val = (F i).val γ.val := by
  let Q := (volumeGammaSpace hc).power (Fin n)
  let R := volumeGammaSpace hc
  let c : G → ι := fun γ => Classical.choose (hpart γ.val γ.property)
  have hc' (γ : G) : γ.val ∈ (P (c γ)).carrier := (Classical.choose_spec (hpart γ.val γ.property)).1
  have hchoice (γ : G) (i : ι) (hi : γ.val ∈ (P i).carrier) : i = c γ :=
    (Classical.choose_spec (hpart γ.val γ.property)).2 i hi
  let g : G → GammaGroundDefSet.univ hc B R := fun γ => ⟨(F (c γ)).val γ.val,Set.mem_univ _⟩
  have hRi (i : ι) : GammaGroundDefinable hc B (Q.prod R)
      {z | z.1 ∈ (P i).carrier ∧ (F i).val z.1 = z.2} := by
    let f := fullGammaFunctionMap (hc := hc) (F i).val (F i).property
    have hp := (P i).definable.preimage (universalProductFst Q R B.real)
    apply (hp.inter f.graph_definable).congr
    intro z
    constructor
    · rintro ⟨hz,a,ha,hf⟩
      exact ⟨hz,(congrArg (F i).val ha).symm.trans hf⟩
    · rintro ⟨hz,hf⟩
      exact ⟨hz,⟨z.1,Set.mem_univ _⟩,rfl,hf⟩
  have hU : GammaGroundDefinable hc B (Q.prod R)
      {z | ∃ i, z.1 ∈ (P i).carrier ∧ (F i).val z.1 = z.2} := by
    apply (GammaGroundDefinable.iUnion hRi).congr
    intro z
    simp only [Set.mem_iUnion,Set.mem_setOf_eq]
  let f : GammaGroundMap G (GammaGroundDefSet.univ hc B R) := {
    toFun := g
    graph_definable := by
      apply hU.congr
      intro z
      constructor
      · rintro ⟨i,hi,hf⟩
        let γ : G := ⟨z.1,hsub i hi⟩
        refine ⟨γ,rfl,?_⟩
        change (F (c γ)).val z.1 = z.2
        rw [← hchoice γ i hi]
        exact hf
      · rintro ⟨γ,ha,hf⟩
        refine ⟨c γ,ha ▸ hc' γ,?_⟩
        exact (congrArg (F (c γ)).val ha).symm.trans hf }
  refine ⟨f,?_⟩
  intro i γ hi
  change (F (c γ)).val γ.val = (F i).val γ.val
  rw [hchoice γ i hi]

end DiamondIntegral.Section3
