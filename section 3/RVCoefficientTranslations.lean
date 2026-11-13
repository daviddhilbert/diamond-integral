import «section 3».RVUnitTupleOperations
import «section 3».GammaGroundRVUnitProducts
import «section 3».GammaGroundBijections
import «section 3».GammaGroundGammaSinglePiece
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q : Space LRV M} {n : ℕ}

/-- Multiply a free RV tuple by a definable function of the retained
parameter. The coefficient is not required to be an old-ground point. -/
def gammaGroundRVUnitSkewMap (A : GammaGroundDefSet hc B Q)
    (G H : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (h : ∀ a : A, ∀ u ∈ G.carrier, (fun i => (c a).val i * u i) ∈ H.carrier) :
    GammaGroundMap (A.prod G) (A.prod H) := by
  let C := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)
  let p := (c.comp (GammaGroundMap.prodFst A G)).pair (GammaGroundMap.prodSnd A G).toUniv
  let m := (gammaGroundRVUnitTupleMulMap (C.prod C)).comp p
  exact (GammaGroundMap.prodFst A G).pair (m.corestrict
    (fun a => h ⟨a.val.1,a.property.1⟩ a.val.2 a.property.2))

@[simp] theorem gammaGroundRVUnitSkewMap_value (A : GammaGroundDefSet hc B Q)
    (G H : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (h : ∀ a : A, ∀ u ∈ G.carrier, (fun i => (c a).val i * u i) ∈ H.carrier)
    (a : A.prod G) :
    (gammaGroundRVUnitSkewMap A G H c h a).val =
      (a.val.1,fun i => (c ⟨a.val.1,a.property.1⟩).val i * a.val.2 i) := rfl

theorem gammaGroundRVUnitSkewMap_bijective (A : GammaGroundDefSet hc B Q)
    (G H : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (h : ∀ a : A, ∀ u ∈ G.carrier, (fun i => (c a).val i * u i) ∈ H.carrier)
    (hback : ∀ a : A, ∀ v ∈ H.carrier, (fun i => ((c a).val i)⁻¹ * v i) ∈ G.carrier) :
    Function.Bijective (gammaGroundRVUnitSkewMap A G H c h) := by
  constructor
  · intro a b he
    have hr : a.val.1 = b.val.1 := congrArg (fun z : A.prod H => z.val.1) he
    have hc : c ⟨a.val.1,a.property.1⟩ = c ⟨b.val.1,b.property.1⟩ :=
      congrArg c (Subtype.ext hr)
    apply Subtype.ext
    refine Prod.ext hr ?_
    funext i
    have hu := congrArg (fun z : A.prod H => z.val.2 i) he
    change (c ⟨a.val.1,a.property.1⟩).val i * a.val.2 i =
      (c ⟨b.val.1,b.property.1⟩).val i * b.val.2 i at hu
    rw [← hc] at hu
    exact mul_left_cancel hu
  · intro p
    let a : A := ⟨p.val.1,p.property.1⟩
    let v : Fin n → (CanonicalRV.RVSort M)ˣ := fun i => ((c a).val i)⁻¹ * p.val.2 i
    refine ⟨⟨(p.val.1,v),p.property.1,hback a p.val.2 p.property.2⟩,?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    exact mul_inv_cancel_left ((c a).val i) (p.val.2 i)

def gammaGroundRVUnitSkewBijection (A : GammaGroundDefSet hc B Q)
    (G H : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (h : ∀ a : A, ∀ u ∈ G.carrier, (fun i => (c a).val i * u i) ∈ H.carrier)
    (hback : ∀ a : A, ∀ v ∈ H.carrier, (fun i => ((c a).val i)⁻¹ * v i) ∈ G.carrier) :
    GammaGroundBijection (A.prod G) (A.prod H) :=
  ⟨gammaGroundRVUnitSkewMap A G H c h,gammaGroundRVUnitSkewMap_bijective A G H c h hback⟩

/-- Full Gamma-preimage products support the coefficient translation
whenever its value tuple is constant. No RV section of that tuple is used. -/
def gammaGroundRVUnitCoefficientTranslation (A : GammaGroundDefSet hc B Q)
    (G H : GammaGroundGammaPiece hc B n)
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (delta : Fin n → Values.Gamma (M := M))
    (hcval : ∀ a : A, rvUnitTupleValues (c a).val = delta)
    (hshift : ∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier ↔ (fun i => delta i * g i) ∈ H.carrier) :
    GammaGroundBijection (A.prod (gammaGroundRVUnitGammaPreimage G))
      (A.prod (gammaGroundRVUnitGammaPreimage H)) := by
  apply gammaGroundRVUnitSkewBijection A _ _ c
  · intro a u hu
    change Fin n → (CanonicalRV.RVSort M)ˣ at u
    change rvUnitTupleValues (fun i => (c a).val i * u i) ∈ H.carrier
    have he : rvUnitTupleValues (fun i => (c a).val i * u i) =
        fun i => delta i * rvUnitTupleValues u i := by
      funext i
      change rvUnitValueHom ((c a).val i * u i) = _
      rw [map_mul]
      exact congrArg (fun z => z * rvUnitTupleValues u i) (congrFun (hcval a) i)
    rw [he]
    exact (hshift _).mp hu
  · intro a v hv
    change Fin n → (CanonicalRV.RVSort M)ˣ at v
    apply (hshift _).mpr
    have he : (fun i => delta i * rvUnitTupleValues (fun j => ((c a).val j)⁻¹ * v j) i) =
        rvUnitTupleValues v := by
      funext i
      change delta i * rvUnitValueHom (((c a).val i)⁻¹ * v i) = _
      rw [map_mul,map_inv]
      rw [show rvUnitValueHom ((c a).val i) = delta i from congrFun (hcval a) i]
      exact mul_inv_cancel_left _ _
    change (fun i => delta i * rvUnitTupleValues (fun j => ((c a).val j)⁻¹ * v j) i) ∈ H.carrier
    rw [he]
    exact hv
end DiamondIntegral.Section3
