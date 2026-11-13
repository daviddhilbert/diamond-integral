import «section 3».CompletedKernelPresentation
import «section 3».TensorPresentationContext
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

section
/-- The actual ring tensor, with the original finite-Gamma coefficient ring. -/
abbrev GammaGroundUnmeasuredGroupTensor (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) :=
  RingCompletion (GammaGroundRESDirectSum (M := M) hc B) ⊗[GammaGroundFiniteGammaGrothendieckRing (M := M) hc B]
    GammaGroundGammaGrothendieckRing (M := M) hc B


local instance gammaGroundUnmeasuredPositiveGammaSemiring : CommSemiring (GammaGroundGammaPositiveSemiring (M := M) hc B) :=
  inferInstance
local instance gammaGroundUnmeasuredPositiveFiniteGammaSemiring : CommSemiring (GammaGroundFiniteGammaPositiveSemiring (M := M) hc B) :=
  inferInstance
local instance gammaGroundUnmeasuredTensorGammaRing : CommRing (GammaGroundGammaGrothendieckRing (M := M) hc B) :=
  inferInstance
local instance gammaGroundUnmeasuredTensorFiniteGammaRing : CommRing (GammaGroundFiniteGammaGrothendieckRing (M := M) hc B) :=
  inferInstance
local instance gammaGroundUnmeasuredTensorRVRing : CommRing (GammaGroundRVGrothendieckRing (M := M) hc B) :=
  inferInstance
instance gammaGroundUnmeasuredTensorRing : CommRing (GammaGroundUnmeasuredGroupTensor (M := M) hc B) :=
  inferInstance

def gammaGroundUnmeasuredTensorCompletionEquiv :
    RingCompletion (GammaGroundUnmeasuredPositiveTensor (M := M) hc B) ≃+* GammaGroundUnmeasuredGroupTensor (M := M) hc B :=
  ringCompletionTensorEquiv

/-- Generators are the differences of the explicit positive coefficient
translation pairs, in the actual ring tensor. The witness remains existential. -/
def gammaGroundUnmeasuredTensorRelationIdeal : Ideal (GammaGroundUnmeasuredGroupTensor (M := M) hc B) :=
  transportedRelationIdeal (S := GammaGroundUnmeasuredGroupTensor (M := M) hc B) (gammaGroundUnmeasuredTensorCompletionEquiv (M := M) (hc := hc) (B := B))
    (gammaGroundUnmeasuredCoefficientPair (hc := hc) (B := B))

@[simp] theorem gammaGroundUnmeasuredTensorCompletionEquiv_tmul
    (a : GammaGroundRESDirectSum (M := M) hc B) (b : GammaGroundGammaPositiveSemiring (M := M) hc B) :
    gammaGroundUnmeasuredTensorCompletionEquiv
      (of (a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring (M := M) hc B] b)) =
        (of a) ⊗ₜ[GammaGroundFiniteGammaGrothendieckRing (M := M) hc B] (of b) :=
  ringCompletionTensorEquiv_tmul a b

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hκ hs h00 hsmall hγsmall hΓ

theorem gammaGroundUnmeasuredGroupTensor_kernel :
    RingHom.ker (R := GammaGroundUnmeasuredGroupTensor (M := M) hc B) (S := GammaGroundRVGrothendieckRing (M := M) hc B) (gammaGroundUnmeasuredGroupTensorMap (M := M) (hc := hc) (ground := B)) =
      gammaGroundUnmeasuredTensorRelationIdeal (hc := hc) (B := B) := by
  exact (transportedRelationIdeal_eq_kernel (S := GammaGroundUnmeasuredGroupTensor (M := M) hc B) (gammaGroundUnmeasuredTensorMap (M := M) (hc := hc) (ground := B))
    (gammaGroundUnmeasuredTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    gammaGroundUnmeasuredCoefficientPair
    (gammaGroundUnmeasuredCoefficientCongruence_eq_ker hκ hs h00 hsmall hγsmall hΓ)
    gammaGroundUnmeasuredTensorCompletionEquiv).symm

/-- The groupified comparison is the quotient by the complete displayed
ideal, with no cancellation assumption and no claim of tensor injectivity. -/
def gammaGroundUnmeasuredGroupTensorQuotientEquiv :
    GammaGroundUnmeasuredGroupTensor (M := M) hc B ⧸ (gammaGroundUnmeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) ≃+*
      GammaGroundRVGrothendieckRing (M := M) hc B :=
  (Ideal.quotEquivOfEq (gammaGroundUnmeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (gammaGroundUnmeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ))

@[simp] theorem gammaGroundUnmeasuredGroupTensorQuotientEquiv_mk
    (a : GammaGroundUnmeasuredGroupTensor (M := M) hc B) :
    gammaGroundUnmeasuredGroupTensorQuotientEquiv hκ hs h00 hsmall hγsmall hΓ
      (Ideal.Quotient.mk (gammaGroundUnmeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) a) =
        gammaGroundUnmeasuredGroupTensorMap a := by
  change (gammaGroundUnmeasuredGroupTensorMap (M := M) (hc := hc) (ground := B)).quotientKerEquivOfSurjective
    (gammaGroundUnmeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    (Ideal.quotEquivOfEq (gammaGroundUnmeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ).symm
      (Ideal.Quotient.mk (gammaGroundUnmeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) a)) =
        gammaGroundUnmeasuredGroupTensorMap a
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end

section
/-- The actual ring tensor, with the original finite-Gamma coefficient ring. -/
abbrev GammaGroundMeasuredGroupTensor (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) :=
  RingCompletion (GammaGroundMeasuredRESDirectSum (M := M) hc B) ⊗[GammaGroundMeasuredFiniteGammaGrothendieckRing (M := M) hc B]
    GammaGroundMeasuredGammaGrothendieckRing (M := M) hc B


local instance gammaGroundMeasuredPositiveGammaSemiring : CommSemiring (GammaGroundMeasuredGammaPositiveSemiring (M := M) hc B) :=
  inferInstance
local instance gammaGroundMeasuredPositiveFiniteGammaSemiring : CommSemiring (GammaGroundMeasuredFiniteGammaPositiveSemiring (M := M) hc B) :=
  inferInstance
local instance gammaGroundMeasuredTensorGammaRing : CommRing (GammaGroundMeasuredGammaGrothendieckRing (M := M) hc B) :=
  inferInstance
local instance gammaGroundMeasuredTensorFiniteGammaRing : CommRing (GammaGroundMeasuredFiniteGammaGrothendieckRing (M := M) hc B) :=
  inferInstance
local instance gammaGroundMeasuredTensorRVRing : CommRing (GammaGroundMeasuredRVGrothendieckRing (M := M) hc B) :=
  inferInstance
instance gammaGroundMeasuredTensorRing : CommRing (GammaGroundMeasuredGroupTensor (M := M) hc B) :=
  inferInstance

def gammaGroundMeasuredTensorCompletionEquiv :
    RingCompletion (GammaGroundMeasuredPositiveTensor (M := M) hc B) ≃+* GammaGroundMeasuredGroupTensor (M := M) hc B :=
  ringCompletionTensorEquiv

/-- Generators are the differences of the explicit positive coefficient
translation pairs, in the actual ring tensor. The witness remains existential. -/
def gammaGroundMeasuredTensorRelationIdeal : Ideal (GammaGroundMeasuredGroupTensor (M := M) hc B) :=
  transportedRelationIdeal (S := GammaGroundMeasuredGroupTensor (M := M) hc B) (gammaGroundMeasuredTensorCompletionEquiv (M := M) (hc := hc) (B := B))
    (gammaGroundMeasuredCoefficientPair (hc := hc) (B := B))

@[simp] theorem gammaGroundMeasuredTensorCompletionEquiv_tmul
    (a : GammaGroundMeasuredRESDirectSum (M := M) hc B) (b : GammaGroundMeasuredGammaPositiveSemiring (M := M) hc B) :
    gammaGroundMeasuredTensorCompletionEquiv
      (of (a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring (M := M) hc B] b)) =
        (of a) ⊗ₜ[GammaGroundMeasuredFiniteGammaGrothendieckRing (M := M) hc B] (of b) :=
  ringCompletionTensorEquiv_tmul a b

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hκ hs h00 hsmall hγsmall hΓ

theorem gammaGroundMeasuredGroupTensor_kernel :
    RingHom.ker (R := GammaGroundMeasuredGroupTensor (M := M) hc B) (S := GammaGroundMeasuredRVGrothendieckRing (M := M) hc B) (gammaGroundMeasuredGroupTensorMap (M := M) (hc := hc) (ground := B)) =
      gammaGroundMeasuredTensorRelationIdeal (hc := hc) (B := B) := by
  exact (transportedRelationIdeal_eq_kernel (S := GammaGroundMeasuredGroupTensor (M := M) hc B) (gammaGroundMeasuredTensorMap (M := M) (hc := hc) (ground := B))
    (gammaGroundMeasuredTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    gammaGroundMeasuredCoefficientPair
    (gammaGroundMeasuredCoefficientCongruence_eq_ker hκ hs h00 hsmall hγsmall hΓ)
    gammaGroundMeasuredTensorCompletionEquiv).symm

/-- The groupified comparison is the quotient by the complete displayed
ideal, with no cancellation assumption and no claim of tensor injectivity. -/
def gammaGroundMeasuredGroupTensorQuotientEquiv :
    GammaGroundMeasuredGroupTensor (M := M) hc B ⧸ (gammaGroundMeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) ≃+*
      GammaGroundMeasuredRVGrothendieckRing (M := M) hc B :=
  (Ideal.quotEquivOfEq (gammaGroundMeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (gammaGroundMeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ))

@[simp] theorem gammaGroundMeasuredGroupTensorQuotientEquiv_mk
    (a : GammaGroundMeasuredGroupTensor (M := M) hc B) :
    gammaGroundMeasuredGroupTensorQuotientEquiv hκ hs h00 hsmall hγsmall hΓ
      (Ideal.Quotient.mk (gammaGroundMeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) a) =
        gammaGroundMeasuredGroupTensorMap a := by
  change (gammaGroundMeasuredGroupTensorMap (M := M) (hc := hc) (ground := B)).quotientKerEquivOfSurjective
    (gammaGroundMeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    (Ideal.quotEquivOfEq (gammaGroundMeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ).symm
      (Ideal.Quotient.mk (gammaGroundMeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) a)) =
        gammaGroundMeasuredGroupTensorMap a
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end
end DiamondIntegral.Section3
