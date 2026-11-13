import «section 3».RESUnitCoordinates
import «section 3».TensorPieceNormalForm
import «section 3».RVProductFiniteMonomialCover
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

/-- A homogeneous positive tensor chart with native free coordinates,
a retained RES label, and an explicit equality of total degrees. -/
structure GammaGroundNativeTensorChart (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (k : ℕ) where
  residueDegree : ℕ
  gammaDegree : ℕ
  degree_eq : residueDegree+gammaDegree = k
  residue : GammaGroundRESUnitChart hc B residueDegree
  gamma : GammaGroundGammaPiece hc B gammaDegree

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
namespace GammaGroundNativeTensorChart

def source (Z : GammaGroundNativeTensorChart hc B k) :=
  (gammaGroundRVUnitGammaPreimage Z.gamma).prod Z.residue.native

def value (Z : GammaGroundNativeTensorChart hc B k) : GammaGroundUnmeasuredPositiveTensor hc B :=
  gammaGroundRESDirectSumClass Z.residue.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single Z.gamma)

def object (Z : GammaGroundNativeTensorChart hc B k) : GammaGroundRVObject hc B k :=
  Z.degree_eq ▸ Z.residue.object.obj.product (GammaGroundGammaObject.single Z.gamma).rvLift

/-- Native product coordinates present the actual RV object, including
its original label degree and finite Gamma tags. -/
def bijection (Z : GammaGroundNativeTensorChart hc B k) :
    GammaGroundBijection Z.source Z.object.domain := by
  rcases Z with ⟨r,n,h,X,G⟩
  subst k
  exact (gammaGroundTensorNativeProductBijection X.object.obj G).comp
    ((X.bijection.symm.prodMap (GammaGroundBijection.id (gammaGroundRVUnitGammaPreimage G))).comp
      (gammaGroundProductSwap (gammaGroundRVUnitGammaPreimage G) X.native))

theorem value_image (Z : GammaGroundNativeTensorChart hc B k) :
    gammaGroundUnmeasuredTensorMap Z.value = gammaGroundRVSemiringClass Z.object := by
  rcases Z with ⟨r,n,h,X,G⟩
  subst k
  exact gammaGroundUnmeasuredTensorMap_objects X.object (GammaGroundGammaObject.single G)

/-- A native chart can be built for each single-piece normal-form term
in its actual total degree. -/
def ofPiece (h00 : M ⊨ Axioms.ACVF00) (t : GammaGroundUnmeasuredTensorPiece hc B)
    (hdegree : t.residueDegree+t.gammaDegree = k) : GammaGroundNativeTensorChart hc B k :=
  ⟨t.residueDegree,t.gammaDegree,hdegree,gammaGroundRESUnitChart h00 t.residue,t.gamma⟩

@[simp] theorem ofPiece_value (h00 : M ⊨ Axioms.ACVF00) (t : GammaGroundUnmeasuredTensorPiece hc B)
    (hdegree : t.residueDegree+t.gammaDegree = k) : (ofPiece h00 t hdegree).value = t.value := rfl
end GammaGroundNativeTensorChart
end DiamondIntegral.Section3
