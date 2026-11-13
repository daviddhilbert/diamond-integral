import «section 3».NormalizedMeasuredTensorPieces
import «section 3».MeasuredLocalMonomialCongruence
import «section 3».NativeTensorImagePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundMeasuredNativeTensorChart (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (k : ℕ) where
  underlying : GammaGroundNativeTensorChart hc B k
  weight : (Fin underlying.gammaDegree → Values.Gamma (M := M)) → Values.Gamma (M := M)
  weight_definable : FullGammaFunction (integrationGammaBase B) weight

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}
namespace GammaGroundMeasuredNativeTensorChart

def residue (Z : GammaGroundMeasuredNativeTensorChart hc B k) : GammaGroundMeasuredRESObject hc B Z.underlying.residueDegree :=
  Z.underlying.residue.object.withCombinedWeight (gammaGroundOneForm Z.underlying.residue.object.obj.domain)

@[simp] theorem residue_weight (Z : GammaGroundMeasuredNativeTensorChart hc B k) (a : Z.residue.obj.underlying.domain) :
    Z.residue.obj.combinedWeight a = 1 :=
  (Z.underlying.residue.object.obj.withCombinedWeight_value _ a).trans (gammaGroundOneForm_value _ a)

def gamma (Z : GammaGroundMeasuredNativeTensorChart hc B k) :=
  gammaGroundMeasuredGammaSingleWeight Z.underlying.gamma Z.weight Z.weight_definable

def value (Z : GammaGroundMeasuredNativeTensorChart hc B k) : GammaGroundMeasuredPositiveTensor hc B :=
  gammaGroundMeasuredRESDirectSumClass Z.residue ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass Z.gamma

def object (Z : GammaGroundMeasuredNativeTensorChart hc B k) : GammaGroundMeasuredRVObject hc B k :=
  Z.underlying.degree_eq ▸ Z.residue.obj.product Z.gamma.rvLift

def bijection (Z : GammaGroundMeasuredNativeTensorChart hc B k) :
    GammaGroundBijection Z.underlying.source Z.object.underlying.domain := by
  rcases Z with ⟨⟨r,n,h,X,G⟩,f,hf⟩
  subst k
  exact (show GammaGroundNativeTensorChart hc B (r+n) from ⟨r,n,rfl,X,G⟩).bijection

/-- The actual measured product uses the existing native RV bijection;
its whole combined weight is the retained Gamma function. -/
theorem native_weight (Z : GammaGroundMeasuredNativeTensorChart hc B k) (z : Z.underlying.source) :
    Z.object.combinedWeight (Z.bijection.map z) = Z.weight (rvUnitTupleValues z.val.1) := by
  rcases Z with ⟨⟨r,n,h,X,G⟩,f,hf⟩
  subst k
  let A := X.object.withCombinedWeight (gammaGroundOneForm X.object.obj.domain)
  let a : X.object.obj.domain := X.bijection.symm.map ⟨z.val.2,z.property.2⟩
  let u : gammaGroundRVUnitGammaPreimage G := ⟨z.val.1,z.property.1⟩
  change (A.obj.product (gammaGroundMeasuredGammaSingleWeight G f hf).rvLift).combinedWeight
    ((gammaGroundTensorNativeProductBijection X.object.obj G).map ⟨(a.val,u.val),a.property,u.property⟩) = f (rvUnitTupleValues u.val)
  have hp := gammaGroundMeasuredTensorNativeProduct_weight A.obj G f hf a u
  have ha : A.obj.combinedWeight a = 1 :=
    (X.object.obj.withCombinedWeight_value _ a).trans (gammaGroundOneForm_value _ a)
  exact hp.trans (by rw [ha,one_mul])

theorem value_image (Z : GammaGroundMeasuredNativeTensorChart hc B k) :
    gammaGroundMeasuredTensorMap Z.value = gammaGroundMeasuredRVSemiringClass Z.object := by
  rcases Z with ⟨⟨r,n,h,X,G⟩,f,hf⟩
  subst k
  exact gammaGroundMeasuredTensorMap_objects (X.object.withCombinedWeight (gammaGroundOneForm X.object.obj.domain))
    (gammaGroundMeasuredGammaSingleWeight G f hf)

def ofPiece (h00 : M ⊨ Axioms.ACVF00) (t : GammaGroundNormalizedMeasuredTensorPiece hc B)
    (hdegree : t.residueDegree+t.gammaDegree = k) : GammaGroundMeasuredNativeTensorChart hc B k :=
  ⟨⟨t.residueDegree,t.gammaDegree,hdegree,
    gammaGroundRESUnitChart h00 ⟨t.residue.obj.underlying,t.residue.property⟩,t.gamma⟩,t.weight,t.weight_definable⟩

@[simp] theorem ofPiece_value (h00 : M ⊨ Axioms.ACVF00) (t : GammaGroundNormalizedMeasuredTensorPiece hc B)
    (hdegree : t.residueDegree+t.gammaDegree = k) : (ofPiece h00 t hdegree).value = t.value := by
  let Z := ofPiece h00 t hdegree
  have he := gammaGroundMeasuredRESDirectSumClass_weight_bijection Z.residue t.residue
    (GammaGroundBijection.id t.residue.obj.underlying.domain)
    (fun a => (Z.residue_weight a).trans (t.residue_normalized a).symm)
  change gammaGroundMeasuredRESDirectSumClass Z.residue ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass Z.gamma = t.value
  rw [he]
  rfl

def restrictBox (Z : GammaGroundMeasuredNativeTensorChart hc B k)
    (E : GammaGroundTensorBox Z.underlying.residue Z.underlying.gamma) : GammaGroundMeasuredNativeTensorChart hc B k :=
  ⟨E.toNativeChart Z.underlying.degree_eq,Z.weight,Z.weight_definable⟩
end GammaGroundMeasuredNativeTensorChart
end DiamondIntegral.Section3
