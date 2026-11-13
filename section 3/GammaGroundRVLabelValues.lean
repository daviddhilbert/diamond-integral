import «section 3».GammaGroundRVUnitRES
import «section 3».GammaGroundMeasuredRVCategories
import «section 3».RVUnitGammaMaps
import «section 3».FullGammaFunctionMaps
import «section 3».GammaGroundVolumeForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

def GammaGroundRVObject.unitLabelMap (U : GammaGroundRVObject hc B k) :
    GammaGroundMap U.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) k)) := by
  let T := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) k)
  let e := gammaGroundRVUnitPresentationBijection T
  have h : ∀ a, (U.volume a).val ∈ (gammaGroundRVUnitToRVMap T).image.carrier := by
    intro a
    let x : Fin k → (CanonicalRV.RVSort M)ˣ := fun i => Units.mk0 ((U.volume a).val i)
      (fun he => U.nonzero a i ((congrArg Subtype.val he).trans RVOperations.zero_val))
    exact ⟨⟨x,Set.mem_univ _⟩,rfl⟩
  exact e.symm.map.comp (U.volume.corestrict h)

theorem GammaGroundRVObject.unitLabelMap_coe (U : GammaGroundRVObject hc B k) (a : U.domain) :
    (fun i => ((U.unitLabelMap a).val i : CanonicalRV.RVSort M)) = (U.volume a).val := by
  let T := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) k)
  let e := gammaGroundRVUnitPresentationBijection T
  have he := e.map.apply_inverse e.bijective
    (show (gammaGroundRVUnitToRVMap T).image from ⟨(U.volume a).val,by
      let x : Fin k → (CanonicalRV.RVSort M)ˣ := fun i => Units.mk0 ((U.volume a).val i)
        (fun he => U.nonzero a i ((congrArg Subtype.val he).trans RVOperations.zero_val))
      exact ⟨⟨x,Set.mem_univ _⟩,rfl⟩⟩)
  exact congrArg Subtype.val he

def GammaGroundRVObject.labelValueMap (U : GammaGroundRVObject hc B k) :
    GammaGroundMap U.domain (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin k))) :=
  (GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real k) (fun _ => Set.mem_univ _)).comp U.unitLabelMap

theorem GammaGroundRVObject.labelValueMap_value (U : GammaGroundRVObject hc B k) (a : U.domain) (i : Fin k) :
    (U.labelValueMap a).val i = Section2.rvFiniteValue (U.target a i) := by
  apply Subtype.ext
  change Values.vrv ((U.unitLabelMap a).val i : CanonicalRV.RVSort M) = Values.vrv ((U.volume a).val i)
  exact congrArg Values.vrv (congrFun (U.unitLabelMap_coe a) i)

def GammaGroundRVObject.labelWeightForm (U : GammaGroundRVObject hc B k) :
    GammaGroundVolumeForm hc B U.domain :=
  (fullGammaFunctionMap (fun γ : Fin k → Values.Gamma (M := M) => ∏ i, γ i)
    (FullGammaFunction.prod Finset.univ (fun i γ => γ i) (fun i _ => FullGammaFunction.proj _ i))).comp U.labelValueMap

theorem GammaGroundRVObject.labelWeightForm_value (U : GammaGroundRVObject hc B k) (a : U.domain) :
    gammaGroundFormValue U.labelWeightForm a = ∏ i, Section2.rvFiniteValue (U.target a i) := by
  change (∏ i, cast (gammaCarrier hc) ((U.labelValueMap a).val i)) = _
  exact Finset.prod_congr rfl (fun i _ => U.labelValueMap_value a i)

def GammaGroundMeasuredRVObject.combinedWeightForm (U : GammaGroundMeasuredRVObject hc B k) :
    GammaGroundVolumeForm hc B U.underlying.domain := U.form.mul U.underlying.labelWeightForm

theorem GammaGroundMeasuredRVObject.combinedWeightForm_value (U : GammaGroundMeasuredRVObject hc B k)
    (a : U.underlying.domain) :
    gammaGroundFormValue U.combinedWeightForm a = U.combinedWeight a := by
  rw [combinedWeightForm,GammaGroundVolumeForm.mul_value,U.underlying.labelWeightForm_value]
  rfl
end DiamondIntegral.Section3
