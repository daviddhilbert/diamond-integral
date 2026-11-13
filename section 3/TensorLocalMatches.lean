import «section 3».NativeTensorProductPartitions
import «section 3».RVMonomialPatchTargetCuts
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}

def gammaGroundNativeProductDomain (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m) :=
  (gammaGroundRVUnitGammaPreimage G).prod X.native

/-- A native product subrectangle with the original labelled RES
coefficient and original Gamma domain as its parents. -/
structure GammaGroundTensorBox (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m) where
  residue : GammaGroundDefSet hc B (rawRVUnitSpace X.arity)
  residue_subset : residue.carrier ⊆ X.native.carrier
  gamma : GammaGroundGammaPiece hc B m
  gamma_subset : gamma.carrier ⊆ G.carrier

namespace GammaGroundTensorBox
variable {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}

def source (L : GammaGroundTensorBox X G) := (gammaGroundRVUnitGammaPreimage L.gamma).prod L.residue

def value (L : GammaGroundTensorBox X G) : GammaGroundUnmeasuredPositiveTensor hc B :=
  gammaGroundRESDirectSumClass (X.restrict L.residue L.residue_subset).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single L.gamma)

def inclusion (L : GammaGroundTensorBox X G) : GammaGroundMap L.source (gammaGroundNativeProductDomain X G) :=
  (GammaGroundMap.inclusion (show (gammaGroundRVUnitGammaPreimage L.gamma).carrier ⊆
    (gammaGroundRVUnitGammaPreimage G).carrier from fun _ h => L.gamma_subset h)).prodMap
      (GammaGroundMap.inclusion L.residue_subset)

@[ext] theorem ext {L R : GammaGroundTensorBox X G} (hA : L.residue = R.residue) (hG : L.gamma = R.gamma) : L = R := by
  cases L
  cases R
  cases hA
  cases hG
  rfl
end GammaGroundTensorBox

variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- A concrete product match records the actual RV bijection and its
agreement with the given global map, together with the positive congruence. -/
structure GammaGroundTensorBoxMatch (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : GammaGroundRESUnitChart hc B r) (H : GammaGroundGammaPiece hc B m)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (L : GammaGroundTensorBox X G) (R : GammaGroundTensorBox Y H) where
  bijection : GammaGroundBijection L.source R.source
  agrees : ∀ z : L.source, t (R.inclusion (bijection.map z)) = F.map (s (L.inclusion z))
  congruence : gammaGroundUnmeasuredCoefficientCongruence L.value R.value

namespace GammaGroundTensorBoxMatch
variable {F : GammaGroundBijection U0 V0}
variable {X Y : GammaGroundRESUnitChart hc B r} {G H : GammaGroundGammaPiece hc B m}
variable {s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0}
variable {L : GammaGroundTensorBox X G} {R : GammaGroundTensorBox Y H}

def symm (E : GammaGroundTensorBoxMatch F X G s Y H t L R) :
    GammaGroundTensorBoxMatch F.symm Y H t X G s R L where
  bijection := E.bijection.symm
  congruence := gammaGroundUnmeasuredCoefficientCongruence.symm E.congruence
  agrees := by
    intro z
    have h := E.agrees (E.bijection.symm.map z)
    have he : E.bijection.map (E.bijection.symm.map z) = z :=
      E.bijection.map.apply_inverse E.bijection.bijective z
    rw [he] at h
    change s (L.inclusion (E.bijection.symm.map z)) = F.map.inverse F.bijective (t (R.inclusion z))
    rw [h,GammaGroundMap.inverse_apply]
end GammaGroundTensorBoxMatch

/-- Product matches that can be cut from either side. The cut data are
actual product bijections and positive congruences, so reversing a cover
retains the information required for finite matching. -/
structure GammaGroundTensorLocalMatch (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : GammaGroundRESUnitChart hc B r) (H : GammaGroundGammaPiece hc B m)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) where
  source : GammaGroundTensorBox X G
  target : GammaGroundTensorBox Y H
  data : GammaGroundTensorBoxMatch F X G s Y H t source target
  sourceCuts : ∀ L : GammaGroundTensorBox X G,
    L.residue.carrier ⊆ source.residue.carrier → L.gamma.carrier ⊆ source.gamma.carrier →
    L.residue.carrier.Nonempty → L.gamma.carrier.Nonempty →
      ∃ R : GammaGroundTensorBox Y H, Nonempty (GammaGroundTensorBoxMatch F X G s Y H t L R)
  targetCuts : ∀ R : GammaGroundTensorBox Y H,
    R.residue.carrier ⊆ target.residue.carrier → R.gamma.carrier ⊆ target.gamma.carrier →
    R.residue.carrier.Nonempty → R.gamma.carrier.Nonempty →
      ∃ L : GammaGroundTensorBox X G, Nonempty (GammaGroundTensorBoxMatch F X G s Y H t L R)

namespace GammaGroundTensorLocalMatch
variable {F : GammaGroundBijection U0 V0}
variable {X Y : GammaGroundRESUnitChart hc B r} {G H : GammaGroundGammaPiece hc B m}
variable {s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0}

def symm (E : GammaGroundTensorLocalMatch F X G s Y H t) :
    GammaGroundTensorLocalMatch F.symm Y H t X G s where
  source := E.target
  target := E.source
  data := E.data.symm
  sourceCuts := by
    intro L hA hG hneA hneG
    obtain ⟨R,⟨d⟩⟩ := E.targetCuts L hA hG hneA hneG
    exact ⟨R,⟨d.symm⟩⟩
  targetCuts := by
    intro R hA hG hneA hneG
    obtain ⟨L,⟨d⟩⟩ := E.sourceCuts R hA hG hneA hneG
    exact ⟨L,⟨d.symm⟩⟩
end GammaGroundTensorLocalMatch
end DiamondIntegral.Section3
