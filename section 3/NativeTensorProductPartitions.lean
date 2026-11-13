import «section 3».TensorBooleanCells
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r n N : ℕ}

/-- A positive product partition in the native unit chart retains the
original RES labels by taking actual definable preimages. Free coordinates
come first, matching the local monomial and chart-transition formulae. -/
theorem GammaGroundRESUnitChart.disjoint_full_preimage_partition
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.native.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint
      ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier
      ((gammaGroundRVUnitGammaPreimage (H j)).prod (A j)).carrier)
    (hcov : ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier, ∀ a ∈ X.native.carrier,
      ∃ i, u ∈ (gammaGroundRVUnitGammaPreimage (H i)).carrier ∧ a ∈ (A i).carrier) :
    gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      ∑ i, gammaGroundRESDirectSumClass (X.restrict (A i) (hA i)).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (H i)) := by
  let AR := fun i => X.bijection.inverseImage (A i)
  have hAR : ∀ i, (AR i).carrier ⊆ X.object.obj.domain.carrier := fun i => X.bijection.inverseImage_subset (A i)
  have hdR : ∀ i j, i ≠ j → Disjoint
      ((AR i).prod (gammaGroundRVUnitGammaPreimage (H i))).carrier
      ((AR j).prod (gammaGroundRVUnitGammaPreimage (H j))).carrier := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨a,ha,hai⟩,hui⟩ ⟨⟨b,hb,hbj⟩,huj⟩
    have hab : b = a := Subtype.ext (hb.trans ha.symm)
    subst b
    have h1 : (z.2,(X.bijection.map a).val) ∈ ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier := ⟨hui,hai⟩
    have h2 : (z.2,(X.bijection.map a).val) ∈ ((gammaGroundRVUnitGammaPreimage (H j)).prod (A j)).carrier := ⟨huj,hbj⟩
    exact Set.disjoint_left.mp (hd i j hij) h1 h2
  have hcovR : ∀ a ∈ X.object.obj.domain.carrier, ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier,
      ∃ i, a ∈ (AR i).carrier ∧ u ∈ (gammaGroundRVUnitGammaPreimage (H i)).carrier := by
    intro a ha u hu
    let x : X.object.obj.domain := ⟨a,ha⟩
    obtain ⟨i,hui,hai⟩ := hcov u hu (X.bijection.map x).val (X.bijection.map x).property
    exact ⟨i,⟨x,rfl,hai⟩,hui⟩
  exact gammaGroundUnmeasuredTensor_disjoint_full_preimage_partition X.object G AR H hAR hH hdR hcovR

/-- The native partition identity is independent of the chosen finite
index presentation. -/
theorem GammaGroundRESUnitChart.finite_disjoint_full_preimage_partition {ι : Type} [Fintype ι]
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : ι → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.native.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint
      ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier
      ((gammaGroundRVUnitGammaPreimage (H j)).prod (A j)).carrier)
    (hcov : ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier, ∀ a ∈ X.native.carrier,
      ∃ i, u ∈ (gammaGroundRVUnitGammaPreimage (H i)).carrier ∧ a ∈ (A i).carrier) :
    gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      ∑ i, gammaGroundRESDirectSumClass (X.restrict (A i) (hA i)).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (H i)) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcovFin : ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier, ∀ a ∈ X.native.carrier,
      ∃ j : Fin (Fintype.card ι), u ∈ (gammaGroundRVUnitGammaPreimage (H (e j))).carrier ∧ a ∈ (A (e j)).carrier := by
    intro u hu a ha
    obtain ⟨i,hui,hai⟩ := hcov u hu a ha
    exact ⟨e.symm i,by simpa only [Equiv.apply_symm_apply] using hui,
      by simpa only [Equiv.apply_symm_apply] using hai⟩
  have h := X.disjoint_full_preimage_partition G (fun j => A (e j)) (fun j => H (e j))
    (fun j => hA (e j)) (fun j => hH (e j))
    (fun i j hij => hd (e i) (e j) (fun he => hij (e.injective he))) hcovFin
  exact h.trans (e.sum_comp (fun i => gammaGroundRESDirectSumClass (X.restrict (A i) (hA i)).object
    ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (H i))))
end DiamondIntegral.Section3
