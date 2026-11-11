import «section 2».MixedGammaFibres
import «section 2».RVIndexedGammaBounds

/-! The full mixed-coordinate Lemma 2.53. The pure VF argument bounds
each named fibre. Its full original-base Gamma image family has a uniform
bound by 2.41 and definable completeness. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def IsMixedOpenDiscPartition (A : Set (Mixed M n m)) (p : Mixed M n m → Gamma M) : Prop :=
  ∀ t : Fin m → RVInfinity M, IsOpenDiscPartition (vfFibre A t) (fun a => p (a,t))

/-- Lemma 2.53 for arbitrary finite VF and RV arities, including zero.
Only the Gamma piecewise-linearity background is an accepted input. -/
theorem lemma_2_53
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : Set (Mixed M n m)) (hA : S.Definable LRV (mixedTuple '' A))
    (hRV : RVValueDoublyBounded (Prod.snd '' A))
    (hclosed : ∀ t ∈ Prod.snd '' A, IsClosed (vfFibre A t))
    (hbounded : ∀ t ∈ Prod.snd '' A, ∃ η : Gamma M,
      ∀ a ∈ vfFibre A t, ∀ i, η.val ≤ vfValue (a i))
    (p : Mixed M n m → Gamma M) (hp : IsMixedOpenDiscPartition A p)
    (hpdef : S.Definable LRV (mixedGammaGraph A p)) :
    ∃ γ : Gamma M, ∀ x ∈ A, γ⁻¹ ≤ p x ∧ p x ≤ γ := by
  let D := rvInputValues '' (Prod.snd '' A)
  have hD : S.Definable LRV D := mixed_rv_domain_definable S A hA
  have hNZ : ∀ y ∈ D, ∀ i, GammaParameters.NonzeroRV (y i) := by
    rintro y ⟨t,ht,rfl⟩ i
    exact ⟨(t i).property,fun he => hRV.nonzero t ht i (Subtype.ext he)⟩
  have hDBound : RVCodeDoublyBounded D := by
    obtain ⟨β,hβ⟩ := hRV
    refine ⟨β,?_⟩
    rintro y ⟨t,ht,rfl⟩ i
    change (β⁻¹).val ≤ (GammaParameters.codeValue (t i).val).val ∧
      (GammaParameters.codeValue (t i).val).val ≤ β.val
    rw [nonzero_rv_codeValue_val (t i) (RVValueDoublyBounded.nonzero ⟨β,hβ⟩ t ht i)]
    exact hβ t ht i
  have hpoint (y : Fin m → M) (hy : y ∈ D) :
      (mixedGammaFamily A p y).Nonempty ∧
        BddBelow (mixedGammaFamily A p y) ∧ BddAbove (mixedGammaFamily A p y) := by
    obtain ⟨t,ht,rfl⟩ := hy
    rw [mixedGammaFamily_fibre_eq]
    have hne : (vfFibre A t).Nonempty := by
      obtain ⟨x,hx,rfl⟩ := ht
      exact ⟨x.1,hx⟩
    refine ⟨hne.image _,?_⟩
    exact lemma_2_53_vf h00 hc hκ hs hv (vfFibre A t) (mixed_vf_fibre_definable S A hA t)
      (hclosed t ht) (hbounded t ht) (fun a => p (a,t)) (hp t) (mixedGammaGraph_fibre_definable S A p hpdef t)
  obtain ⟨γ,hγ⟩ := rv_indexed_gamma_family_bounded hc h00 linear hκ.le hs S hsmall hΓ D hD hNZ
    (mixedGammaFamily A p) (mixedGammaFamily_graph_definable S A p hpdef) hDBound hpoint
  refine ⟨γ,fun x hx => ?_⟩
  exact hγ (rvInputValues x.2) ⟨x.2,⟨x,hx,rfl⟩,rfl⟩ (p x) ⟨x,hx,rfl,rfl⟩

theorem lemma_2_53_image_bounds
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : Set (Mixed M n m)) (hA : S.Definable LRV (mixedTuple '' A))
    (hRV : RVValueDoublyBounded (Prod.snd '' A))
    (hclosed : ∀ t ∈ Prod.snd '' A, IsClosed (vfFibre A t))
    (hbounded : ∀ t ∈ Prod.snd '' A, ∃ η : Gamma M,
      ∀ a ∈ vfFibre A t, ∀ i, η.val ≤ vfValue (a i))
    (p : Mixed M n m → Gamma M) (hp : IsMixedOpenDiscPartition A p)
    (hpdef : S.Definable LRV (mixedGammaGraph A p)) :
    BddBelow (p '' A) ∧ BddAbove (p '' A) := by
  obtain ⟨γ,hγ⟩ := lemma_2_53 h00 hc linear hκ hs hv S hsmall hΓ A hA hRV hclosed hbounded p hp hpdef
  exact ⟨⟨γ⁻¹,by rintro _ ⟨x,hx,rfl⟩; exact (hγ x hx).1⟩,
    ⟨γ,by rintro _ ⟨x,hx,rfl⟩; exact (hγ x hx).2⟩⟩

end DiamondIntegral.Section2
