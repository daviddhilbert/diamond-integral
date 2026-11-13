import «section 3».RVMonomialPatchRestrictions
import «section 3».GammaAffineImageRestrictions
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m p r : ℕ}
namespace GammaGroundRVProductMonomialPatch
variable {R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
variable {T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n))}
variable {D : GammaGroundDefSet hc B (rawRVUnitSpace m)} {S : GammaGroundDefSet hc B (rawRVUnitSpace p)}
variable {f : GammaGroundMap T D} {g : GammaGroundMap T S}

theorem target_residue_preimage_nonempty (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace p)) (hA : A.carrier ⊆ P.residueMap.image.carrier)
    (hneA : A.carrier.Nonempty) : (P.residueMap.preimage A).carrier.Nonempty := by
  obtain ⟨a,ha⟩ := hneA
  obtain ⟨b,hb⟩ := hA ha
  change (P.residueMap b).val = a at hb
  have hm : (P.residueMap b).val ∈ A.carrier := hb.symm ▸ ha
  exact ⟨b.val,b,rfl,hm⟩

theorem target_gamma_preimage_nonempty (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (V : GammaGroundGammaPiece hc B m) (hV : V.carrier ⊆ P.targetGamma.carrier)
    (hneV : V.carrier.Nonempty) :
    (P.gamma.inter (gammaGroundGammaAffinePreimage V P.matrix P.value P.value_definable)).carrier.Nonempty := by
  obtain ⟨η,hη⟩ := hneV
  obtain ⟨γ,hγ,hφ⟩ := (gammaGroundGammaAffineImage_mem P.gamma P.matrix P.value P.value_definable η).mp (hV hη)
  have hm : gammaAffineValue P.matrix P.value γ ∈ V.carrier := hφ.symm ▸ hη
  exact ⟨γ,hγ,hm⟩

/-- A target product cut pulls back to a product source restriction of
the same monomial patch. It keeps the original coefficient function. -/
def restrictTarget (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace p)) (hA : A.carrier ⊆ P.residueMap.image.carrier)
    (hneA : A.carrier.Nonempty) (V : GammaGroundGammaPiece hc B m)
    (hV : V.carrier ⊆ P.targetGamma.carrier) (hneV : V.carrier.Nonempty) :
    GammaGroundRVProductMonomialPatch R T D S f g :=
  P.restrict (P.residueMap.preimage A) (P.residueMap.preimage_subset A)
    (P.target_residue_preimage_nonempty A hA hneA)
    (P.gamma.inter (gammaGroundGammaAffinePreimage V P.matrix P.value P.value_definable))
    (fun _ h => h.1) (P.target_gamma_preimage_nonempty V hV hneV)

theorem restrictTarget_residue_image (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace p)) (hA : A.carrier ⊆ P.residueMap.image.carrier)
    (hneA : A.carrier.Nonempty) (V : GammaGroundGammaPiece hc B m)
    (hV : V.carrier ⊆ P.targetGamma.carrier) (hneV : V.carrier.Nonempty) :
    (P.restrictTarget A hA hneA V hV hneV).residueMap.image = A :=
  P.residueMap.image_restrict_preimage A hA

theorem restrictTarget_gamma_image (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace p)) (hA : A.carrier ⊆ P.residueMap.image.carrier)
    (hneA : A.carrier.Nonempty) (V : GammaGroundGammaPiece hc B m)
    (hV : V.carrier ⊆ P.targetGamma.carrier) (hneV : V.carrier.Nonempty) :
    (P.restrictTarget A hA hneA V hV hneV).targetGamma = V :=
  gammaGroundGammaAffineImage_restrict_target P.gamma V P.matrix P.value P.value_definable hV
end GammaGroundRVProductMonomialPatch

/-- The explicit positive congruence also applies after a target cut.
This permits the inverse cover to enter the forward finite matching. -/
theorem gammaGroundMonomialPatch_target_cut_congruence
    (X Y : GammaGroundRESUnitChart hc B r)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (f : GammaGroundMap T D) (g : GammaGroundMap T Y.native)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (P : GammaGroundRVProductMonomialPatch X.native T D Y.native f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace Y.arity)) (hA : A.carrier ⊆ P.residueMap.image.carrier)
    (hneA : A.carrier.Nonempty) (V : GammaGroundGammaPiece hc B m)
    (hV : V.carrier ⊆ P.targetGamma.carrier) (hneV : V.carrier.Nonempty) :
    let Q := P.restrictTarget A hA hneA V hV hneV
    gammaGroundUnmeasuredCoefficientCongruence
      (gammaGroundRESDirectSumClass (X.restrict Q.residue Q.residue_subset).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single Q.gamma))
      (gammaGroundRESDirectSumClass (Y.restrict A (hA.trans P.residueMap_image_subset)).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single V)) := by
  let Q := P.restrictTarget A hA hneA V hV hneV
  have hQA : Q.residueMap.image = A := P.restrictTarget_residue_image A hA hneA V hV hneV
  have hQG : Q.targetGamma = V := P.restrictTarget_gamma_image A hA hneA V hV hneV
  have hres : gammaGroundRESDirectSumClass (Y.restrict Q.residueMap.image Q.residueMap_image_subset).object =
      gammaGroundRESDirectSumClass (Y.restrict A (hA.trans P.residueMap_image_subset)).object := by
    apply gammaGroundRESDirectSumClass_bijection
    exact GammaGroundBijection.ofCarrierEq
      (congrArg GammaGroundDefSet.carrier (congrArg Y.bijection.inverseImage hQA))
  have hC := gammaGroundMonomialPatch_tensor_congruence X Y T D f g hjoint Q
  rw [hres,hQG] at hC
  exact hC
end DiamondIntegral.Section3
