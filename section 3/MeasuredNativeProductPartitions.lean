import «section 3».MeasuredTensorBooleanCells
import «section 3».MeasuredNativeRESPartitions
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
theorem GammaGroundRESUnitChart.measured_disjoint_full_preimage_partition
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.native.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint
      ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier
      ((gammaGroundRVUnitGammaPreimage (H j)).prod (A j)).carrier)
    (hcov : ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier, ∀ a ∈ X.native.carrier,
      ∃ i, u ∈ (gammaGroundRVUnitGammaPreimage (H i)).carrier ∧ a ∈ (A i).carrier) :
    gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ i, gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)).measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) := by
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
  have hraw := gammaGroundMeasuredTensor_disjoint_full_preimage_partition f hf X.measured G AR H hAR hH hdR hcovR
  calc
    _ = ∑ i, gammaGroundMeasuredRESDirectSumClass (X.measured.restrict (AR i) (hAR i))
        ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) := hraw
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun a => a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf))
      apply gammaGroundMeasuredRESDirectSumClass_weight_bijection _ _ (GammaGroundBijection.id (AR i))
      intro a
      change X.measured.obj.combinedWeight ⟨a.val,hAR i a.property⟩ =
        (X.restrict (A i) (hA i)).measured.obj.combinedWeight a
      rw [X.measured_weight,(X.restrict (A i) (hA i)).measured_weight]

/-- The native partition identity is independent of the chosen finite
index presentation. -/
theorem GammaGroundRESUnitChart.measured_finite_disjoint_full_preimage_partition {ι : Type} [Fintype ι]
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : ι → GammaGroundGammaPiece hc B n)
    (hA : ∀ i, (A i).carrier ⊆ X.native.carrier) (hH : ∀ i, (H i).carrier ⊆ G.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint
      ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier
      ((gammaGroundRVUnitGammaPreimage (H j)).prod (A j)).carrier)
    (hcov : ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier, ∀ a ∈ X.native.carrier,
      ∃ i, u ∈ (gammaGroundRVUnitGammaPreimage (H i)).carrier ∧ a ∈ (A i).carrier) :
    gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ i, gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)).measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcovFin : ∀ u ∈ (gammaGroundRVUnitGammaPreimage G).carrier, ∀ a ∈ X.native.carrier,
      ∃ j : Fin (Fintype.card ι), u ∈ (gammaGroundRVUnitGammaPreimage (H (e j))).carrier ∧ a ∈ (A (e j)).carrier := by
    intro u hu a ha
    obtain ⟨i,hui,hai⟩ := hcov u hu a ha
    exact ⟨e.symm i,by simpa only [Equiv.apply_symm_apply] using hui,
      by simpa only [Equiv.apply_symm_apply] using hai⟩
  have h := X.measured_disjoint_full_preimage_partition G f hf (fun j => A (e j)) (fun j => H (e j))
    (fun j => hA (e j)) (fun j => hH (e j))
    (fun i j hij => hd (e i) (e j) (fun he => hij (e.injective he))) hcovFin
  exact h.trans (e.sum_comp (fun i => gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)).measured
    ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (H i) f hf)))
end DiamondIntegral.Section3
