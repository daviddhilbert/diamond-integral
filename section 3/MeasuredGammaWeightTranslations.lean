import «section 3».MeasuredTensorCoefficientRelations
import «section 3».TensorTupleCoefficientCongruence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaGroundTranslatedGammaWeight
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (δ : Fin n → Values.Gamma (M := M)) (γ : Fin n → Values.Gamma (M := M)) :=
  f (fun j => (δ j)⁻¹ * γ j)

theorem gammaGroundTranslatedGammaWeight_definable
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j)) :
    FullGammaFunction (integrationGammaBase B) (gammaGroundTranslatedGammaWeight f δ) :=
  hf.comp (fun j γ => (δ j)⁻¹ * γ j) (fun j =>
    (FullGammaFunction.constant (δ j) (integrationGammaDefinable (hδ j))).inv.mul (FullGammaFunction.proj _ j))

theorem gammaGroundTranslatedGammaWeight_prefix_step
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (δ : Fin n → Values.Gamma (M := M)) (i : Fin n) (γ : Fin n → Values.Gamma (M := M)) :
    gammaGroundTranslatedGammaWeight f (gammaValuePrefix δ i.val) γ =
      gammaGroundTranslatedGammaWeight f (gammaValuePrefix δ (i.val+1))
        (fun j => gammaGroundSparseValueTuple i (δ i) j * γ j) := by
  apply congrArg f
  funext j
  rw [congrFun (gammaValuePrefix_succ_sparse δ i) j]
  simp only [mul_inv_rev,mul_assoc,inv_mul_cancel_left]

/-- Two prescribed full combined weights equal on the actual Gamma
domain define the same positive measured Gamma class. -/
theorem gammaGroundMeasuredGammaSingleWeight_class_eqOn (G : GammaGroundGammaPiece hc B n)
    (f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (hg : FullGammaFunction (integrationGammaBase B) g)
    (he : ∀ γ ∈ G.carrier, f γ = g γ) :
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G g hg) := by
  let h : GammaGroundMeasuredGammaHom (gammaGroundMeasuredGammaSingleWeight G f hf)
      (gammaGroundMeasuredGammaSingleWeight G g hg) :=
    { underlying := GammaGroundGammaHom.id (GammaGroundGammaObject.single G)
      preserves := by
        intro a
        rw [gammaGroundMeasuredGammaSingleWeight_combined,gammaGroundMeasuredGammaSingleWeight_combined]
        exact he a.2.val a.2.property }
  exact gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from h))

def gammaGroundMeasuredGammaTranslatedPiece (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j)) :=
  gammaGroundMeasuredGammaSingleWeight (gammaGroundGammaTranslate G δ hδ)
    (gammaGroundTranslatedGammaWeight f δ) (gammaGroundTranslatedGammaWeight_definable f hf δ hδ)

theorem gammaGroundMeasuredGammaTranslatedPiece_tuple_eq (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ η : Fin n → Values.Gamma (M := M))
    (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j)) (hη : ∀ j, GammaDefinableClosureAtBase B (η j))
    (he : δ = η) : gammaGroundMeasuredGammaTranslatedPiece G f hf δ hδ =
      gammaGroundMeasuredGammaTranslatedPiece G f hf η hη := by
  subst η
  rfl

variable {r : ℕ}

theorem gammaGroundMeasuredCoefficientCongruence_prefix_step
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j))
    (havailable : GammaGroundRESAvailableValueTuple ⟨X.obj.underlying,X.property⟩ δ) (i : Fin n) :
    gammaGroundMeasuredCoefficientCongruence
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf
          (gammaValuePrefix δ i.val) (gammaValuePrefix_definable δ hδ i.val)))
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf
          (gammaValuePrefix δ (i.val+1)) (gammaValuePrefix_definable δ hδ (i.val+1)))) := by
  apply RingCon.le_ringConGen
  refine ⟨r,n,i,X,_,_,_,_,_,_,gammaGroundSparseValueTuple i (δ i),?_,
    gammaSparseValueTuple_definable i (δ i) (hδ i),?_,?_,?_,rfl,rfl⟩
  · intro j hj
    exact ite_eq_right hj
  · exact (gammaGroundRESAvailableValueTuple_sparse_iff ⟨X.obj.underlying,X.property⟩ i (δ i)).mpr
      (gammaGroundRESAvailableValue_of_tuple ⟨X.obj.underlying,X.property⟩ δ havailable i)
  · exact gammaGroundGammaTranslate_prefix_step G δ hδ i
  · intro γ _
    exact gammaGroundTranslatedGammaWeight_prefix_step f δ i γ

/-- Full tuple translations with transported combined weights follow
from the one-coordinate elementary measured semiring pairs. -/
theorem gammaGroundMeasuredCoefficientCongruence_tuple_translation
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j))
    (havailable : GammaGroundRESAvailableValueTuple ⟨X.obj.underlying,X.property⟩ δ) :
    gammaGroundMeasuredCoefficientCongruence
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf))
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf δ hδ)) := by
  let C := gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)
  let t (k : ℕ) := gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf
      (gammaValuePrefix δ k) (gammaValuePrefix_definable δ hδ k))
  have hstage : ∀ k, k ≤ n → C (t 0) (t k) := by
    intro k
    induction k with
    | zero => intro _; exact C.refl _
    | succ k ih =>
      intro hk
      let i : Fin n := ⟨k,Nat.lt_of_succ_le hk⟩
      exact C.trans (ih (Nat.le_of_succ_le hk))
        (gammaGroundMeasuredCoefficientCongruence_prefix_step X G f hf δ hδ havailable i)
  have h0 : gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf
      (gammaValuePrefix δ 0) (gammaValuePrefix_definable δ hδ 0)) =
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) := by
    have hG : gammaGroundGammaTranslate G (gammaValuePrefix δ 0) (gammaValuePrefix_definable δ hδ 0) = G := by
      apply gammaGroundDefSet_eq_of_carrier_eq
      ext γ
      change (Fin n → Values.Gamma (M := M)) at γ
      change ((fun j => (gammaValuePrefix δ 0 j)⁻¹ * γ j) ∈ G.carrier) ↔ γ ∈ G.carrier
      rw [gammaValuePrefix_zero]
      simp only [inv_one,one_mul]
    unfold gammaGroundMeasuredGammaTranslatedPiece
    rw [hG]
    apply gammaGroundMeasuredGammaSingleWeight_class_eqOn
    intro γ _
    change (Fin n → Values.Gamma (M := M)) at γ
    change f (fun j => (gammaValuePrefix δ 0 j)⁻¹ * γ j) = f γ
    rw [gammaValuePrefix_zero]
    simp only [inv_one,one_mul]
  have hn := congrArg gammaGroundMeasuredGammaSemiringClass
    (gammaGroundMeasuredGammaTranslatedPiece_tuple_eq G f hf (gammaValuePrefix δ n) δ
      (gammaValuePrefix_definable δ hδ n) hδ (gammaValuePrefix_all δ))
  have h := hstage n (Nat.le_refl n)
  change gammaGroundMeasuredCoefficientCongruence
    (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf
        (gammaValuePrefix δ 0) (gammaValuePrefix_definable δ hδ 0)))
    (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece G f hf
        (gammaValuePrefix δ n) (gammaValuePrefix_definable δ hδ n))) at h
  rw [h0,hn] at h
  exact h
end DiamondIntegral.Section3
