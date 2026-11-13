import «section 3».MeasuredGammaPieceWeights
import «section 3».MeasuredGammaPieceSums
import «section 3».MeasuredTensorRESNormalization
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

/-- A positive measured piece retains both original degrees, has RES
combined weight one, and has a full Gamma combined-weight function. -/
structure GammaGroundNormalizedMeasuredTensorPiece (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  residueDegree : ℕ
  gammaDegree : ℕ
  residue : GammaGroundMeasuredRESObject hc B residueDegree
  residue_normalized : ∀ a, residue.obj.combinedWeight a = 1
  gamma : GammaGroundGammaPiece hc B gammaDegree
  weight : (Fin gammaDegree → Values.Gamma (M := M)) → Values.Gamma (M := M)
  weight_definable : FullGammaFunction (integrationGammaBase B) weight

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

def GammaGroundNormalizedMeasuredTensorPiece.value (t : GammaGroundNormalizedMeasuredTensorPiece hc B) :
    GammaGroundMeasuredPositiveTensor hc B :=
  gammaGroundMeasuredRESDirectSumClass t.residue ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight t.gamma t.weight t.weight_definable)

theorem gammaGroundMeasuredGammaObject_full_piece_weights (A : GammaGroundMeasuredGammaObject hc B n) :
    ∃ f : Fin A.underlying.tags → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M),
      ∃ hf : ∀ i, FullGammaFunction (integrationGammaBase B) (f i),
      gammaGroundMeasuredGammaSemiringClass A = ∑ i,
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (A.underlying.piece i) (f i) (hf i)) := by
  have hp (i : Fin A.underlying.tags) := gammaGroundMeasuredGammaSingleForm_full_weight (A.underlying.piece i) (A.form i)
  choose f hf hclass using hp
  refine ⟨f,hf,?_⟩
  calc
    _ = ∑ i, gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleForm (A.underlying.piece i) (A.form i)) :=
      gammaGroundMeasuredGammaSemiringClass_finite_pieces A.underlying.tags A.underlying.piece A.form
    _ = _ := Finset.sum_congr rfl (fun i _ => hclass i)

/-- Normalization of one arbitrary measured pure object tensor is a
positive finite sum of normalized single-piece tensors of the same degrees. -/
theorem gammaGroundMeasuredTensor_pure_normalized_pieces {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (X : GammaGroundMeasuredRESObject hc B r) (A : GammaGroundMeasuredGammaObject hc B n) :
    ∃ l : List (GammaGroundNormalizedMeasuredTensorPiece hc B),
      gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass A =
          (l.map GammaGroundNormalizedMeasuredTensorPiece.value).sum ∧
      ∀ t ∈ l, t.residueDegree = r ∧ t.gammaDegree = n := by
  obtain ⟨N,Y,H,hY,hvalue⟩ := gammaGroundMeasuredTensor_RES_weight_normalization hκ hs h00 hsmall hγsmall X A
  have hp (i : Fin N) := gammaGroundMeasuredGammaObject_full_piece_weights (H i)
  choose f hf hclass using hp
  let I := Σ i : Fin N, Fin (H i).underlying.tags
  let Z : I → GammaGroundNormalizedMeasuredTensorPiece hc B := fun c =>
    ⟨r,n,Y c.1,hY c.1,(H c.1).underlying.piece c.2,f c.1 c.2,hf c.1 c.2⟩
  have hv : gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass A = ∑ c : I, (Z c).value := by
    have hsum := Fintype.sum_sigma (fun c : I => (Z c).value)
    rw [hvalue,hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hclass i,TensorProduct.tmul_sum]
    rfl
  let q := (Fintype.equivFin I).symm
  refine ⟨List.ofFn (fun a => Z (q a)),?_,?_⟩
  · rw [List.map_ofFn,List.sum_ofFn]
    exact hv.trans (Equiv.sum_comp q (fun c => (Z c).value)).symm
  · intro t ht
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨rfl,rfl⟩

/-- Every positive measured tensor has an actual normalized finite
single-piece normal form before any kernel quotient or groupification. -/
theorem gammaGroundMeasuredTensor_normalized_piece_normal_form {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (t : GammaGroundMeasuredPositiveTensor hc B) :
    ∃ l : List (GammaGroundNormalizedMeasuredTensorPiece hc B),
      t = (l.map GammaGroundNormalizedMeasuredTensorPiece.value).sum := by
  obtain ⟨q,rfl⟩ := gammaGroundMeasuredTensor_object_normal_form t
  induction q with
  | nil => exact ⟨[],rfl⟩
  | cons a q ih =>
    obtain ⟨p,hp,_⟩ := gammaGroundMeasuredTensor_pure_normalized_pieces hκ hs h00 hsmall hγsmall a.residue a.gamma
    obtain ⟨l,hl⟩ := ih
    refine ⟨p++l,?_⟩
    change a.value = _ at hp
    change a.value+(q.map GammaGroundMeasuredTensorTerm.value).sum = _
    rw [hp,hl,List.map_append,List.sum_append]
end DiamondIntegral.Section3
