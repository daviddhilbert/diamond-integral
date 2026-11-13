import «section 3».GammaGroundBijectionProducts
import «section 3».GammaGroundRVProducts
import «section 3».GammaGroundRVProductMorphisms
import Section4.RVReindexing
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
variable {P Q R : Space LRV M}

def GammaGroundBijection.prodSwap (A : GammaGroundDefSet hc ground P) (B : GammaGroundDefSet hc ground Q) :
    GammaGroundBijection (A.prod B) (B.prod A) where
  map := (GammaGroundMap.prodSnd A B).pair (GammaGroundMap.prodFst A B)
  bijective := by
    constructor
    · intro a b hab
      have he := congrArg (fun z : B.prod A => z.val) hab
      exact Subtype.ext (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))
    · intro z
      exact ⟨⟨(z.val.2, z.val.1), z.property.2, z.property.1⟩, rfl⟩

def GammaGroundBijection.prodAssoc (A : GammaGroundDefSet hc ground P)
    (B : GammaGroundDefSet hc ground Q) (D : GammaGroundDefSet hc ground R) :
    GammaGroundBijection ((A.prod B).prod D) (A.prod (B.prod D)) where
  map := ((GammaGroundMap.prodFst A B).comp (GammaGroundMap.prodFst (A.prod B) D)).pair
    (((GammaGroundMap.prodSnd A B).comp (GammaGroundMap.prodFst (A.prod B) D)).pair
      (GammaGroundMap.prodSnd (A.prod B) D))
  bijective := by
    constructor
    · intro a b hab
      have he := congrArg (fun z : A.prod (B.prod D) => z.val) hab
      change (a.val.1.1, (a.val.1.2, a.val.2)) = (b.val.1.1, (b.val.1.2, b.val.2)) at he
      have h1 : a.val.1.1 = b.val.1.1 := congrArg (fun z : P.Carrier × (Q.Carrier × R.Carrier) => z.1) he
      have h2 : a.val.1.2 = b.val.1.2 := congrArg (fun z : P.Carrier × (Q.Carrier × R.Carrier) => z.2.1) he
      have h3 : a.val.2 = b.val.2 := congrArg (fun z : P.Carrier × (Q.Carrier × R.Carrier) => z.2.2) he
      exact Subtype.ext (Prod.ext (Prod.ext h1 h2) h3)
    · intro z
      exact ⟨⟨((z.val.1, z.val.2.1), z.val.2.2), ⟨z.property.1, z.property.2.1⟩, z.property.2.2⟩, rfl⟩

variable {k l j n : ℕ}

def GammaGroundRVObject.reindexVolume (U : GammaGroundRVObject hc ground k) (e : Fin n ≃ Fin k) :
    GammaGroundRVObject hc ground n where
  arity := U.arity
  domain := U.domain
  volume := (GammaGroundMap.ofReal (rvReindexMap ground.real e)).comp U.volume
  finite := (GammaGroundMap.finiteFibres_of_injective (rvReindexMap_bijective ground.real e).1).comp U.finite
  nonzero a i := U.nonzero a (e i)

def gammaGroundRVProductCommBijection (U : GammaGroundRVObject hc ground k) (V : GammaGroundRVObject hc ground l) :
    GammaGroundBijection (U.product V).domain (V.product U).domain :=
  (gammaGroundRVPackBijection V.domain U.domain).comp
    ((GammaGroundBijection.prodSwap U.domain V.domain).comp (gammaGroundRVPackBijection U.domain V.domain).symm)

def gammaGroundRVProductAssocBijection (U : GammaGroundRVObject hc ground k)
    (V : GammaGroundRVObject hc ground l) (W : GammaGroundRVObject hc ground j) :
    GammaGroundBijection ((U.product V).product W).domain (U.product (V.product W)).domain :=
  (gammaGroundRVPackBijection U.domain (V.product W).domain).comp
    (((GammaGroundBijection.id U.domain).prodMap (gammaGroundRVPackBijection V.domain W.domain)).comp
      ((GammaGroundBijection.prodAssoc U.domain V.domain W.domain).comp
        (((gammaGroundRVPackBijection U.domain V.domain).symm.prodMap (GammaGroundBijection.id W.domain)).comp
          (gammaGroundRVPackBijection (U.product V).domain W.domain).symm)))

def gammaGroundRVRightUnitProjection (U : GammaGroundRVObject hc ground k) :
    GammaGroundBijection (U.domain.prod (GammaGroundRVObject.unit hc ground).domain) U.domain where
  map := GammaGroundMap.prodFst U.domain (GammaGroundRVObject.unit hc ground).domain
  bijective := by
    constructor
    · intro a b hab
      have he : a.val.1 = b.val.1 := congrArg (fun x : U.domain => x.val) hab
      apply Subtype.ext
      apply Prod.ext he
      funext i
      exact i.elim0
    · intro a
      exact ⟨⟨(a.val, Fin.elim0), a.property, Set.mem_univ _⟩, rfl⟩

def gammaGroundRVProductRightUnitBijection (U : GammaGroundRVObject hc ground k) :
    GammaGroundBijection (U.product (GammaGroundRVObject.unit hc ground)).domain U.domain :=
  (gammaGroundRVRightUnitProjection U).comp (gammaGroundRVPackBijection U.domain (GammaGroundRVObject.unit hc ground).domain).symm

end DiamondIntegral.Section3
