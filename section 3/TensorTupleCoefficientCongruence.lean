import «section 3».GammaNativeTranslations
import «section 3».RVUnitCoordinateTuples
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

theorem gammaGroundRESAvailableValue_of_tuple (X : GammaGroundRESObject hc B r)
    (δ : Fin n → Values.Gamma (M := M)) (h : GammaGroundRESAvailableValueTuple X δ) (i : Fin n) :
    GammaGroundRESAvailableValue X (δ i) := by
  obtain ⟨c,hcval⟩ := h
  refine ⟨(gammaGroundRVUnitCoordinateTupleMap _ i).comp c,?_⟩
  intro a
  funext j
  change rvUnitValueHom (((gammaGroundRVUnitCoordinateTupleMap _ i) (c a)).val j) = δ i
  rw [gammaGroundRVUnitCoordinateTupleMap_value]
  exact congrFun (hcval a) i

theorem gammaSparseValueTuple_definable (i : Fin n) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) :
    ∀ j, GammaDefinableClosureAtBase B (gammaGroundSparseValueTuple i δ j) := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa [gammaGroundSparseValueTuple] using hδ
  · simpa only [gammaGroundSparseValueTuple,ite_eq_right hj] using gammaDefinableClosure_one B

theorem gammaValuePrefix_succ_sparse (δ : Fin n → Values.Gamma (M := M)) (i : Fin n) :
    gammaValuePrefix δ (i.val+1) =
      fun j => gammaGroundSparseValueTuple i (δ i) j * gammaValuePrefix δ i.val j := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [gammaValuePrefix,gammaGroundSparseValueTuple]
  · have hne : j.val ≠ i.val := fun he => hj (Fin.ext he)
    have hlt : j.val < i.val+1 ↔ j.val < i.val := by omega
    simp only [gammaValuePrefix,gammaGroundSparseValueTuple,ite_eq_right hj,one_mul,hlt]

theorem gammaGroundGammaTranslate_prefix_step (G : GammaGroundGammaPiece hc B n)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j))
    (i : Fin n) (γ : Fin n → Values.Gamma (M := M)) :
    γ ∈ (gammaGroundGammaTranslate G (gammaValuePrefix δ i.val)
      (gammaValuePrefix_definable δ hδ i.val)).carrier ↔
      (fun j => gammaGroundSparseValueTuple i (δ i) j * γ j) ∈
        (gammaGroundGammaTranslate G (gammaValuePrefix δ (i.val+1))
          (gammaValuePrefix_definable δ hδ (i.val+1))).carrier := by
  change ((fun j => (gammaValuePrefix δ i.val j)⁻¹ * γ j) ∈ G.carrier) ↔
    (fun j => (gammaValuePrefix δ (i.val+1) j)⁻¹ *
      (gammaGroundSparseValueTuple i (δ i) j * γ j)) ∈ G.carrier
  have he : (fun j => (gammaValuePrefix δ (i.val+1) j)⁻¹ *
      (gammaGroundSparseValueTuple i (δ i) j * γ j)) =
      fun j => (gammaValuePrefix δ i.val j)⁻¹ * γ j := by
    funext j
    rw [congrFun (gammaValuePrefix_succ_sparse δ i) j]
    simp only [mul_inv_rev,mul_assoc,inv_mul_cancel_left]
  rw [he]

theorem gammaGroundUnmeasuredCoefficientCongruence_prefix_step
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j))
    (havailable : GammaGroundRESAvailableValueTuple X δ) (i : Fin n) :
    gammaGroundUnmeasuredCoefficientCongruence
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single
          (gammaGroundGammaTranslate G (gammaValuePrefix δ i.val) (gammaValuePrefix_definable δ hδ i.val))))
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single
          (gammaGroundGammaTranslate G (gammaValuePrefix δ (i.val+1)) (gammaValuePrefix_definable δ hδ (i.val+1))))) := by
  apply RingCon.le_ringConGen
  refine ⟨r,n,i,X,_,_,gammaGroundSparseValueTuple i (δ i),?_,
    gammaSparseValueTuple_definable i (δ i) (hδ i),?_,?_,rfl,rfl⟩
  · intro j hj
    exact ite_eq_right hj
  · exact (gammaGroundRESAvailableValueTuple_sparse_iff X i (δ i)).mpr
      (gammaGroundRESAvailableValue_of_tuple X δ havailable i)
  · exact gammaGroundGammaTranslate_prefix_step G δ hδ i

/-- Every available constant-value tuple translation is already generated
by the displayed one-coordinate positive pairs. -/
theorem gammaGroundUnmeasuredCoefficientCongruence_tuple_translation
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j))
    (havailable : GammaGroundRESAvailableValueTuple X δ) :
    gammaGroundUnmeasuredCoefficientCongruence
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G))
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaTranslate G δ hδ))) := by
  let K (k : ℕ) := gammaGroundGammaTranslate G (gammaValuePrefix δ k) (gammaValuePrefix_definable δ hδ k)
  let t (k : ℕ) := gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (K k))
  let C := gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)
  have hstage : ∀ k, k ≤ n → C (t 0) (t k) := by
    intro k
    induction k with
    | zero => intro _; exact C.refl _
    | succ k ih =>
      intro hk
      let i : Fin n := ⟨k,Nat.lt_of_succ_le hk⟩
      exact C.trans (ih (Nat.le_of_succ_le hk))
        (gammaGroundUnmeasuredCoefficientCongruence_prefix_step X G δ hδ havailable i)
  have h0 : K 0 = G := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    ext γ
    change Fin n → Values.Gamma (M := M) at γ
    change ((fun i => (gammaValuePrefix δ 0 i)⁻¹ * γ i) ∈ G.carrier) ↔ γ ∈ G.carrier
    rw [gammaValuePrefix_zero]
    simp only [inv_one,one_mul]
  have hn : K n = gammaGroundGammaTranslate G δ hδ := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    ext γ
    change Fin n → Values.Gamma (M := M) at γ
    change ((fun i => (gammaValuePrefix δ n i)⁻¹ * γ i) ∈ G.carrier) ↔
      (fun i => (δ i)⁻¹ * γ i) ∈ G.carrier
    rw [gammaValuePrefix_all]
  have h := hstage n (Nat.le_refl n)
  change gammaGroundUnmeasuredCoefficientCongruence
    (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (K 0)))
    (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (K n))) at h
  rw [h0,hn] at h
  exact h
end DiamondIntegral.Section3
