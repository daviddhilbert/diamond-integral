import «section 3».GammaGroundRVPackPairs

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l j : ℕ}

theorem gammaGroundRVProductCommBijection_pair (U : GammaGroundRVObject hc ground k)
    (V : GammaGroundRVObject hc ground l) (a : U.domain) (b : V.domain) :
    (gammaGroundRVProductCommBijection U V).map (gammaGroundRVPackPair U.domain V.domain a b) =
      gammaGroundRVPackPair V.domain U.domain b a := by
  change (gammaGroundRVPack V.domain U.domain).toImage
    ((GammaGroundBijection.prodSwap U.domain V.domain).map
      (gammaGroundRVUnpack U.domain V.domain (gammaGroundRVPackPair U.domain V.domain a b))) = _
  rw [gammaGroundRVUnpack_pair]
  rfl

theorem gammaGroundRVProductAssocBijection_pair (U : GammaGroundRVObject hc ground k)
    (V : GammaGroundRVObject hc ground l) (W : GammaGroundRVObject hc ground j)
    (a : U.domain) (b : V.domain) (c : W.domain) :
    (gammaGroundRVProductAssocBijection U V W).map
      (gammaGroundRVPackPair (U.product V).domain W.domain
        (gammaGroundRVPackPair U.domain V.domain a b) c) =
      gammaGroundRVPackPair U.domain (V.product W).domain a (gammaGroundRVPackPair V.domain W.domain b c) := by
  change (gammaGroundRVPack U.domain (V.product W).domain).toImage
    (((GammaGroundBijection.id U.domain).prodMap (gammaGroundRVPackBijection V.domain W.domain)).map
      ((GammaGroundBijection.prodAssoc U.domain V.domain W.domain).map
        (((gammaGroundRVPackBijection U.domain V.domain).symm.prodMap (GammaGroundBijection.id W.domain)).map
          (gammaGroundRVUnpack (U.product V).domain W.domain
            (gammaGroundRVPackPair (U.product V).domain W.domain
              (gammaGroundRVPackPair U.domain V.domain a b) c))))) = _
  rw [gammaGroundRVUnpack_pair]
  have he : ((gammaGroundRVPackBijection U.domain V.domain).symm.prodMap (GammaGroundBijection.id W.domain)).map
      ⟨((gammaGroundRVPackPair U.domain V.domain a b).val, c.val),
        (gammaGroundRVPackPair U.domain V.domain a b).property, c.property⟩ =
      (⟨((a.val, b.val), c.val), ⟨a.property, b.property⟩, c.property⟩ : (U.domain.prod V.domain).prod W.domain) := by
    apply Subtype.ext
    change ((gammaGroundRVUnpack U.domain V.domain (gammaGroundRVPackPair U.domain V.domain a b)).val, c.val) = _
    rw [gammaGroundRVUnpack_pair]
  rw [he]
  rfl

end DiamondIntegral.Section3
