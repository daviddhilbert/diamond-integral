import «section 3».RVCoefficientTranslations
import «section 3».GammaGroundUnmeasuredTensorMap
import «section 3».GammaGroundMeasuredGammaUnitLift
import «section 3».GammaGroundRVProductMorphisms
import «section 3».GammaGroundRVPackPairs
import «section 3».UnmeasuredTensorSurjectivity
import Mathlib.RingTheory.Congruence.Hom
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

/-- Native full-preimage coordinates for the packed product object. -/
def gammaGroundTensorNativeProductBijection (X : GammaGroundRVObject hc B r)
    (G : GammaGroundGammaPiece hc B n) :
    GammaGroundBijection (X.domain.prod (gammaGroundRVUnitGammaPreimage G))
      (X.product (GammaGroundGammaObject.single G).rvLift).domain :=
  (gammaGroundRVPackBijection X.domain (GammaGroundGammaObject.single G).rvLift.domain).comp
    ((GammaGroundBijection.id X.domain).prodMap (gammaGroundGammaUnitLiftBijection G))

@[simp] theorem gammaGroundTensorNativeProductBijection_pair (X : GammaGroundRVObject hc B r)
    (G : GammaGroundGammaPiece hc B n) (a : X.domain) (u : gammaGroundRVUnitGammaPreimage G) :
    (gammaGroundTensorNativeProductBijection X G).map
      ⟨(a.val,u.val),a.property,u.property⟩ =
      gammaGroundRVPackPair X.domain (GammaGroundGammaObject.single G).rvLift.domain
        a ((gammaGroundGammaUnitLiftBijection G).map u) := rfl

/-- The native coefficient translation induces an isomorphism of the
actual product RV objects, including their original finite labels. -/
def gammaGroundTensorCoefficientBijection (X : GammaGroundRESObject hc B r)
    (G H : GammaGroundGammaPiece hc B n)
    (c : GammaGroundMap X.obj.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (delta : Fin n → Values.Gamma (M := M))
    (hcval : ∀ a : X.obj.domain, rvUnitTupleValues (c a).val = delta)
    (hshift : ∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier ↔ (fun i => delta i * g i) ∈ H.carrier) :
    GammaGroundBijection (X.obj.product (GammaGroundGammaObject.single G).rvLift).domain
      (X.obj.product (GammaGroundGammaObject.single H).rvLift).domain :=
  (gammaGroundTensorNativeProductBijection X.obj H).comp
    ((gammaGroundRVUnitCoefficientTranslation X.obj.domain G H c delta hcval hshift).comp
      (gammaGroundTensorNativeProductBijection X.obj G).symm)

theorem gammaGroundUnmeasuredTensor_coefficient_pair (X : GammaGroundRESObject hc B r)
    (G H : GammaGroundGammaPiece hc B n)
    (c : GammaGroundMap X.obj.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (delta : Fin n → Values.Gamma (M := M))
    (hcval : ∀ a : X.obj.domain, rvUnitTupleValues (c a).val = delta)
    (hshift : ∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier ↔ (fun i => delta i * g i) ∈ H.carrier) :
    gammaGroundUnmeasuredTensorMap
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G)) =
    gammaGroundUnmeasuredTensorMap
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single H)) := by
  rw [gammaGroundUnmeasuredTensorMap_objects,gammaGroundUnmeasuredTensorMap_objects]
  exact gammaGroundRVSemiringClass_iso
    (asIso (show _ ⟶ _ from gammaGroundTensorCoefficientBijection X G H c delta hcval hshift))

/-- Availability of a constant value tuple on a RES coefficient is an
existence condition; the chosen function is not part of the pair of classes. -/
def GammaGroundRESAvailableValueTuple (X : GammaGroundRESObject hc B r)
    (delta : Fin n → Values.Gamma (M := M)) : Prop :=
  ∃ c : GammaGroundMap X.obj.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)),
    ∀ a : X.obj.domain, rvUnitTupleValues (c a).val = delta

/-- Elementary positive pairs translate one Gamma coordinate, retaining
the whole RES coefficient and its chosen grading. -/
def gammaGroundUnmeasuredCoefficientPair (a b : GammaGroundUnmeasuredPositiveTensor hc B) : Prop :=
  ∃ (r n : ℕ) (i : Fin n) (X : GammaGroundRESObject hc B r)
      (G H : GammaGroundGammaPiece hc B n) (delta : Fin n → Values.Gamma (M := M)),
    (∀ j, j ≠ i → delta j = 1) ∧
    (∀ j, GammaDefinableClosureAtBase B (delta j)) ∧
    GammaGroundRESAvailableValueTuple X delta ∧
    (∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier ↔ (fun j => delta j * g j) ∈ H.carrier) ∧
    a = gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) ∧
    b = gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single H)

def gammaGroundUnmeasuredCoefficientCongruence : RingCon (GammaGroundUnmeasuredPositiveTensor hc B) :=
  ringConGen (gammaGroundUnmeasuredCoefficientPair (hc := hc) (B := B))

theorem gammaGroundUnmeasuredCoefficientPair_valid
    {a b : GammaGroundUnmeasuredPositiveTensor hc B}
    (h : gammaGroundUnmeasuredCoefficientPair a b) :
    gammaGroundUnmeasuredTensorMap a = gammaGroundUnmeasuredTensorMap b := by
  obtain ⟨r,n,i,X,G,H,delta,_,_,⟨c,hcval⟩,hshift,rfl,rfl⟩ := h
  exact gammaGroundUnmeasuredTensor_coefficient_pair X G H c delta hcval hshift

theorem gammaGroundUnmeasuredCoefficientCongruence_le_ker :
    gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B) ≤
      RingCon.ker (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := B)) := by
  apply RingCon.ringConGen_le.mpr
  intro a b hab
  exact gammaGroundUnmeasuredCoefficientPair_valid hab

abbrev GammaGroundUnmeasuredCoefficientQuotient (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) :=
  (gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).Quotient

def gammaGroundUnmeasuredCoefficientQuotientMap :
    GammaGroundUnmeasuredCoefficientQuotient hc B →+* GammaGroundRVPositiveSemiring hc B :=
  (gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).lift
    (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := B))
    gammaGroundUnmeasuredCoefficientCongruence_le_ker

@[simp] theorem gammaGroundUnmeasuredCoefficientQuotientMap_class
    (a : GammaGroundUnmeasuredPositiveTensor hc B) :
    gammaGroundUnmeasuredCoefficientQuotientMap
      ((gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a) =
        gammaGroundUnmeasuredTensorMap a := rfl

/-- The geometrically proved positive surjectivity also holds after the
explicit elementary relations. Injectivity is the remaining kernel theorem. -/
theorem gammaGroundUnmeasuredCoefficientQuotientMap_surjective {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (gammaGroundUnmeasuredCoefficientQuotientMap (hc := hc) (B := B)) := by
  intro v
  obtain ⟨a,ha⟩ := gammaGroundUnmeasuredTensorMap_surjective (hc := hc) hκ hs h00 hsmall hγsmall hΓ v
  exact ⟨(gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a,ha⟩
end DiamondIntegral.Section3
