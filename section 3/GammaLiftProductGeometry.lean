import «section 3».GammaMeasuredClassLift
import «section 3».GammaGroundMeasuredVFProducts

/-! Literal product geometry for the full-label Gamma-ground lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n m r s : ℕ}

theorem gammaRVUnpack_value
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) s)) (a : gammaGroundRVProductDomain A D) :
    (gammaGroundRVUnpack A D a).val = (a.val ∘ Fin.castAdd s,a.val ∘ Fin.natAdd r) := by
  let p := (gammaGroundRVPack A D).toImage
  have he := congrArg (fun z : gammaGroundRVProductDomain A D => z.val)
    (p.apply_inverse ((gammaGroundRVPack A D).toImage_bijective (gammaGroundRVPack_injective A D)) a)
  change rvAppend (gammaGroundRVUnpack A D a).val.1 (gammaGroundRVUnpack A D a).val.2 = a.val at he
  apply Prod.ext
  · funext i
    exact (Fin.append_left _ _ i).symm.trans (congrFun he (Fin.castAdd s i))
  · funext i
    exact (Fin.append_right _ _ i).symm.trans (congrFun he (Fin.natAdd r i))

theorem gammaMixedUnpack_value
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)) (a : gammaGroundMixedProductDomain A D) :
    (gammaGroundMixedUnpack A D a).val =
      ((a.val.1 ∘ Fin.castAdd m,a.val.2 ∘ Fin.castAdd s),(a.val.1 ∘ Fin.natAdd n,a.val.2 ∘ Fin.natAdd r)) := by
  let p := (gammaGroundMixedPack A D).toImage
  have he := congrArg (fun z : gammaGroundMixedProductDomain A D => z.val)
    (p.apply_inverse ((gammaGroundMixedPack A D).toImage_bijective (gammaGroundMixedPack_injective A D)) a)
  change (vfAppend (gammaGroundMixedUnpack A D a).val.1.1 (gammaGroundMixedUnpack A D a).val.2.1,
    rvAppend (gammaGroundMixedUnpack A D a).val.1.2 (gammaGroundMixedUnpack A D a).val.2.2) = a.val at he
  apply Prod.ext <;> apply Prod.ext <;> funext i
  · exact (Fin.append_left _ _ i).symm.trans (congrArg (fun z => z.1 (Fin.castAdd m i)) he)
  · exact (Fin.append_left _ _ i).symm.trans (congrArg (fun z => z.2 (Fin.castAdd s i)) he)
  · exact (Fin.append_right _ _ i).symm.trans (congrArg (fun z => z.1 (Fin.natAdd n i)) he)
  · exact (Fin.append_right _ _ i).symm.trans (congrArg (fun z => z.2 (Fin.natAdd r i)) he)

theorem gammaObjectLift_product_carrier
    (U : GammaGroundRVObject hc B n) (V : GammaGroundRVObject hc B m) :
    (gammaGroundObjectLift (U.product V)).carrier =
      (gammaGroundMixedProductDomain (gammaGroundObjectLift U) (gammaGroundObjectLift V)).carrier := by
  ext p
  rw [mem_gammaGroundMixedProductDomain]
  constructor
  · rintro ⟨a,ha,hv⟩
    let z := gammaGroundRVUnpack U.domain V.domain a
    let u : U.domain := ⟨z.val.1,z.property.1⟩
    let v : V.domain := ⟨z.val.2,z.property.2⟩
    have hza := gammaRVUnpack_value U.domain V.domain a
    have huv : rvAppend (U.volume u).val (V.volume v).val = Section2.tupleRV M p.1 := hv
    constructor
    · refine ⟨u,?_,?_⟩
      · exact (congrArg Prod.fst hza).trans (congrArg (fun t => t ∘ Fin.castAdd V.arity) ha)
      · funext i
        exact (Fin.append_left _ _ i).symm.trans (congrFun huv (Fin.castAdd m i))
    · refine ⟨v,?_,?_⟩
      · exact (congrArg Prod.snd hza).trans (congrArg (fun t => t ∘ Fin.natAdd U.arity) ha)
      · funext i
        exact (Fin.append_right _ _ i).symm.trans (congrFun huv (Fin.natAdd n i))
  · rintro ⟨⟨u,hu,hvu⟩,v,hv,hvv⟩
    let z : U.domain.prod V.domain := ⟨(u.val,v.val),u.property,v.property⟩
    let a := (gammaGroundRVPack U.domain V.domain).toImage z
    have hza : gammaGroundRVUnpack U.domain V.domain a = z :=
      (gammaGroundRVPack U.domain V.domain).toImage.inverse_apply
        ((gammaGroundRVPack U.domain V.domain).toImage_bijective (gammaGroundRVPack_injective U.domain V.domain)) z
    refine ⟨a,?_,?_⟩
    · change rvAppend u.val v.val = p.2
      rw [hu,hv]
      exact Fin.append_castAdd_natAdd
    · change rvAppend (U.volume ⟨(gammaGroundRVUnpack U.domain V.domain a).val.1,_⟩).val
        (V.volume ⟨(gammaGroundRVUnpack U.domain V.domain a).val.2,_⟩).val = _
      rw [hza]
      change rvAppend (U.volume u).val (V.volume v).val = _
      rw [hvu,hvv]
      change Fin.append ((Section2.tupleRV M p.1) ∘ Fin.castAdd m)
        ((Section2.tupleRV M p.1) ∘ Fin.natAdd n) = _
      exact Fin.append_castAdd_natAdd

end DiamondIntegral.Section3
