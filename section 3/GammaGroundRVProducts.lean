import «section 3».GammaGroundRVScissors
import «section 3».GammaGroundFiniteProducts
import «section 3».RVSemiring

/-! Actual cartesian RV products over the entire Gamma ground retain
nonzero labels and finite fibres in the summed degree. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n m k l : ℕ}

def gammaGroundRVPack (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    GammaGroundMap (A.prod B) (GammaGroundDefSet.univ hc ground (rawRVSpace (n + m))) :=
  GammaGroundMap.ofGlobal (A.prod B) (GammaGroundDefSet.univ hc ground (rawRVSpace (n + m)))
    (rvAppendMap ground.real n m) (fun _ => Set.mem_univ _)

theorem gammaGroundRVPack_injective (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) : Function.Injective (gammaGroundRVPack A B) := by
  intro a b he
  exact Subtype.ext (rvAppend_injective (congrArg Subtype.val he))

def gammaGroundRVProductDomain (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) := (gammaGroundRVPack A B).image

def gammaGroundRVUnpack (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    GammaGroundMap (gammaGroundRVProductDomain A B) (A.prod B) :=
  (gammaGroundRVPack A B).toImage.inverse ((gammaGroundRVPack A B).toImage_bijective (gammaGroundRVPack_injective A B))

def gammaGroundRVAppendTargets :
    GammaGroundMap ((GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)).prod
      (GammaGroundDefSet.univ hc ground (rawRVSpace l)))
      (GammaGroundDefSet.univ hc ground (rawRVSpace (k + l))) :=
  GammaGroundMap.ofGlobal _ _ (rvAppendMap ground.real k l) (fun _ => Set.mem_univ _)

theorem gammaGroundRVAppendTargets_injective :
    Function.Injective (gammaGroundRVAppendTargets (M := M) (hc := hc) (ground := ground) (k := k) (l := l)) := by
  intro a b he
  exact Subtype.ext (rvAppend_injective (congrArg Subtype.val he))

def GammaGroundRVObject.product (U : GammaGroundRVObject hc ground k) (V : GammaGroundRVObject hc ground l) :
    GammaGroundRVObject hc ground (k + l) where
  arity := U.arity + V.arity
  domain := gammaGroundRVProductDomain U.domain V.domain
  volume := gammaGroundRVAppendTargets.comp ((U.volume.prodMap V.volume).comp (gammaGroundRVUnpack U.domain V.domain))
  finite := (GammaGroundMap.finiteFibres_of_injective gammaGroundRVAppendTargets_injective).comp
    ((U.finite.prodMap V.finite).comp (GammaGroundMap.finiteFibres_of_injective
      (Equiv.ofBijective (gammaGroundRVPack U.domain V.domain).toImage
        ((gammaGroundRVPack U.domain V.domain).toImage_bijective (gammaGroundRVPack_injective U.domain V.domain))).symm.injective))
  nonzero a i := by
    let ab := gammaGroundRVUnpack U.domain V.domain a
    change (rvAppend (U.volume ⟨ab.val.1, ab.property.1⟩).val (V.volume ⟨ab.val.2, ab.property.2⟩).val i).val ≠ iRVZero
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [rvAppend, Fin.append_left] using U.nonzero ⟨ab.val.1, ab.property.1⟩ j
    · simpa only [rvAppend, Fin.append_right] using V.nonzero ⟨ab.val.2, ab.property.2⟩ j

def GammaGroundRVObject.unit (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundRVObject hc ground 0 := .ofReal (RVObject.unit ground.real)

end DiamondIntegral.Section3
