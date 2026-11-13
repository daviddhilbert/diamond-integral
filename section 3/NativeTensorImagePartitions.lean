import «section 3».NativeTensorListAtlas
import «section 3».TensorLocalMatches
import «section 3».GammaGroundRVFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m k : ℕ}

theorem GammaGroundMap.image_subset_target {P Q : Space LRV M}
    {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q} (f : GammaGroundMap A D) :
    f.image.carrier ⊆ D.carrier := by
  rintro z ⟨a,ha⟩
  exact ha ▸ (f a).property

theorem GammaGroundMap.corestrict_injective {P Q : Space LRV M}
    {A : GammaGroundDefSet hc B P} {D E : GammaGroundDefSet hc B Q} (f : GammaGroundMap A D)
    (hE : ∀ a, (f a).val ∈ E.carrier) (hf : Function.Injective f) :
    Function.Injective (f.corestrict hE) := by
  intro a b h
  apply hf
  exact Subtype.ext (congrArg (fun z : E => z.val) h)

namespace GammaGroundTensorBox
variable {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}

def toNativeChart (L : GammaGroundTensorBox X G) (hdegree : r+m = k) : GammaGroundNativeTensorChart hc B k :=
  ⟨r,m,hdegree,X.restrict L.residue L.residue_subset,L.gamma⟩

@[simp] theorem toNativeChart_value (L : GammaGroundTensorBox X G) (hdegree : r+m = k) :
    (L.toNativeChart hdegree).value = L.value := rfl

theorem inclusion_injective (L : GammaGroundTensorBox X G) : Function.Injective L.inclusion := by
  intro a b h
  apply Subtype.ext
  have hv := congrArg (fun z : gammaGroundNativeProductDomain X G => z.val) h
  exact Prod.ext (congrArg Prod.fst hv) (congrArg Prod.snd hv)
end GammaGroundTensorBox

/-- An injectively presented native product has the positive RV class
of the actual ambient image, in its original total degree. -/
theorem gammaGroundNativeTensorChart_restrict_image_class
    (Z : GammaGroundNativeTensorChart hc B k) (U : GammaGroundRVObject hc B k)
    (f : GammaGroundMap Z.source U.domain) (hf : Function.Injective f) :
    gammaGroundRVSemiringClass (U.restrict f.image f.image_subset_target) = gammaGroundUnmeasuredTensorMap Z.value := by
  let e : GammaGroundBijection Z.source f.image := ⟨f.toImage,f.toImage_bijective hf⟩
  let E : Z.object ≅ U.restrict f.image f.image_subset_target :=
    asIso (show _ ⟶ _ from e.comp Z.bijection.symm)
  exact (gammaGroundRVSemiringClass_iso E).symm.trans Z.value_image.symm

/-- A disjoint actual native image partition identifies the residual
positive tensor image with its inherited RV object. No matched classes
are cancelled to obtain the residual comparison. -/
theorem gammaGroundNativeTensorCharts_RV_image_partition {ι : Type} [Fintype ι]
    (U : GammaGroundRVObject hc B k) (Z : ι → GammaGroundNativeTensorChart hc B k)
    (f : ∀ i, GammaGroundMap (Z i).source U.domain) (hf : ∀ i, Function.Injective (f i))
    (hd : ∀ i j, i ≠ j → Disjoint (f i).image.carrier (f j).image.carrier)
    (hcov : ∀ x, x ∈ U.domain.carrier ↔ ∃ i, x ∈ (f i).image.carrier) :
    gammaGroundRVSemiringClass U = gammaGroundUnmeasuredTensorMap (∑ i, (Z i).value) := by
  calc
    _ = ∑ i, gammaGroundRVSemiringClass
        (U.restrict (f i).image (fun x hx => (hcov x).mpr ⟨i,hx⟩)) :=
      gammaGroundRVSemiringClass_finite_partition U (fun i => (f i).image) hd hcov
    _ = ∑ i, gammaGroundUnmeasuredTensorMap (Z i).value := by
      apply Finset.sum_congr rfl
      intro i _
      exact gammaGroundNativeTensorChart_restrict_image_class (Z i) U (f i) (hf i)
    _ = _ := (map_sum gammaGroundUnmeasuredTensorMap (fun i => (Z i).value) Finset.univ).symm
end DiamondIntegral.Section3
