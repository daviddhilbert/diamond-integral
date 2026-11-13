import «section 3».TensorObjectNormalForm
import «section 3».GammaPieceSums
import Mathlib.Data.List.OfFn
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

/-- A positive product term with one native Gamma piece and its original
RES label. Neither factor carries a finite-family Gamma tag. -/
structure GammaGroundUnmeasuredTensorPiece (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  residueDegree : ℕ
  gammaDegree : ℕ
  residue : GammaGroundRESObject hc B residueDegree
  gamma : GammaGroundGammaPiece hc B gammaDegree

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def GammaGroundUnmeasuredTensorPiece.asTerm (t : GammaGroundUnmeasuredTensorPiece hc B) :
    GammaGroundUnmeasuredTensorTerm hc B :=
  ⟨t.residueDegree,t.gammaDegree,t.residue,GammaGroundGammaObject.single t.gamma⟩

def GammaGroundUnmeasuredTensorPiece.value (t : GammaGroundUnmeasuredTensorPiece hc B) :
    GammaGroundUnmeasuredPositiveTensor hc B := t.asTerm.value

def GammaGroundUnmeasuredTensorTerm.pieces (t : GammaGroundUnmeasuredTensorTerm hc B) :
    List (GammaGroundUnmeasuredTensorPiece hc B) :=
  List.ofFn (fun i : Fin t.gamma.tags => ⟨t.residueDegree,t.gammaDegree,t.residue,t.gamma.piece i⟩)

theorem GammaGroundUnmeasuredTensorTerm.value_pieces (t : GammaGroundUnmeasuredTensorTerm hc B) :
    t.value = (t.pieces.map GammaGroundUnmeasuredTensorPiece.value).sum := by
  rw [GammaGroundUnmeasuredTensorTerm.pieces,List.map_ofFn,List.sum_ofFn]
  change gammaGroundRESDirectSumClass t.residue ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass t.gamma =
    ∑ i : Fin t.gamma.tags, gammaGroundRESDirectSumClass t.residue ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (t.gamma.piece i))
  rw [gammaGroundGammaSemiringClass_tag_sum,TensorProduct.tmul_sum]

/-- All Gamma family tags can be separated by positive sums before the
geometric comparison. Degrees and RES labels are retained term by term. -/
theorem gammaGroundUnmeasuredTensor_piece_normal_form (t : GammaGroundUnmeasuredPositiveTensor hc B) :
    ∃ l : List (GammaGroundUnmeasuredTensorPiece hc B),
      t = (l.map GammaGroundUnmeasuredTensorPiece.value).sum := by
  obtain ⟨q,rfl⟩ := gammaGroundUnmeasuredTensor_object_normal_form t
  induction q with
  | nil => exact ⟨[],rfl⟩
  | cons a q ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨a.pieces++l,?_⟩
    change a.value+(q.map GammaGroundUnmeasuredTensorTerm.value).sum = _
    rw [a.value_pieces,hl,List.map_append,List.sum_append]
end DiamondIntegral.Section3
