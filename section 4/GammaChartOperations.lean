import «section 4».GammaWeightedCharts

/-! Actual products and the degree-zero unit for weighted Gamma charts.
Partial volume forms are normalized only outside their actual domains. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaChartOperations
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaWeightedCharts GammaObjectPolynomial
open GammaObjectRelations GammaObjectMultiplication GammaProfileProducts GammaSumMap FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ofTotal (B : Base (M := M)) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : Chart B n where
  support := I
  support_definable := hI
  volume := μ
  volume_definable := by
    have hd := GammaRelationLogic.preimage_definable_base B I hI Fin.succ
    have hg := graph_of_mapDefinable B μ hμ
    have h := GammaRelationLogic.inter_definable_base B _ _ hd hg
    convert h using 1
    ext z
    change (Fin.tail z ∈ I ∧ z 0 = μ (Fin.tail z)) ↔ (z ∘ Fin.succ ∈ I ∧ z 0 = μ (Fin.tail z))
    have he : Fin.tail z = z ∘ Fin.succ := by funext i; rfl
    rw [he]

theorem chartPolynomial_ofTotal (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    chartPolynomial h00 hκ hs B hr hγ k (ofTotal B n I hI μ hμ) = objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ := by
  apply objectPolynomial_eq_on_domain
  intro u hu
  exact (ofTotal B n I hI μ hμ).normalizedVolume_on u hu

def product {B : Base (M := M)} {n m : ℕ} (a : Chart B m) (b : Chart B n) : Chart B (n + m) :=
  ofTotal B (n + m) (productSet a.support b.support)
    (productSet_definable B a.support a.support_definable b.support b.support_definable)
    (sumMap a.normalizedVolume b.normalizedVolume)
    (sumMap_definable B _ _ a.normalizedVolume_definable b.normalizedVolume_definable)

theorem product_volume_join {B : Base (M := M)} {n m : ℕ} (a : Chart B m) (b : Chart B n)
    (u : Fin m → Values.Gamma (M := M)) (hu : u ∈ a.support)
    (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ b.support) :
    (product a b).volume (join n m u y) = a.volume u * b.volume y := by
  change sumMap a.normalizedVolume b.normalizedVolume (join n m u y) = _
  rw [sumMap_join, a.normalizedVolume_on u hu, b.normalizedVolume_on y hy]

def unit (B : Base (M := M)) : Chart B 0 :=
  ofTotal B 0 Set.univ (GammaIntegerFamilies.univ_definable_base B 0) (fun _ => 1)
    (constant_definable B 1 (GammaGroupNames.one_definable_base B))

theorem chartPolynomial_product (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n m : ℕ} (a : Chart B m) (b : Chart B n) :
    chartPolynomial h00 hκ hs B hr hγ k (product a b) =
      chartPolynomial h00 hκ hs B hr hγ k a * chartPolynomial h00 hκ hs B hr hγ k b := by
  change chartPolynomial h00 hκ hs B hr hγ k (ofTotal B (n + m) _ _ _ _) = _
  rw [chartPolynomial_ofTotal]
  exact objectPolynomial_product h00 linear hκ hs B hr hγ hΓ k n m
    a.support a.support_definable b.support b.support_definable
    a.normalizedVolume a.normalizedVolume_definable b.normalizedVolume b.normalizedVolume_definable

theorem chartPolynomial_unit (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind) :
    chartPolynomial h00 hκ hs B hr hγ k (unit B) = 1 := by
  change chartPolynomial h00 hκ hs B hr hγ k (ofTotal B 0 _ _ _ _) = 1
  rw [chartPolynomial_ofTotal]
  exact objectPolynomial_one h00 hκ hs B hr hγ k

end DiamondIntegral.Section4.GammaChartOperations
