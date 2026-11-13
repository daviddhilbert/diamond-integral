import «section 3».GammaGroundConstants
import «section 3».RVCoefficientTranslations
import «section 3».GammaGroundMonomialFibreDescent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def gammaGroundRVUnitPointTranslation (G H : GammaGroundGammaPiece hc B n)
    (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c})
    (hshift : ∀ γ : Fin n → Values.Gamma (M := M),
      γ ∈ G.carrier ↔ (fun i => rvUnitValueHom (c i) * γ i) ∈ H.carrier) :
    GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage H) := by
  let A := gammaGroundRVUnitGammaPreimage G
  let C := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)
  let p := (GammaGroundMap.const (R := rawRVUnitSpace n) A c hcdef).pair (GammaGroundMap.id A).toUniv
  let mul := (gammaGroundRVUnitTupleMulMap (C.prod C)).comp p
  have hval (a : A) : (mul a).val = fun i => c i * a.val i := rfl
  have hin (a : A) : (mul a).val ∈ (gammaGroundRVUnitGammaPreimage H).carrier := by
    change rvUnitTupleValues (mul a).val ∈ H.carrier
    rw [hval]
    have he : rvUnitTupleValues (fun i => c i * a.val i) =
        fun i => rvUnitValueHom (c i) * rvUnitTupleValues a.val i := by
      funext i
      exact map_mul (rvUnitValueHom (M := M)) _ _
    rw [he]
    exact (hshift _).mp a.property
  let f := mul.corestrict hin
  refine ⟨f,?_,?_⟩
  · intro a b he
    apply Subtype.ext
    funext i
    have hi : c i * a.val i = c i * b.val i := congrArg (fun z : gammaGroundRVUnitGammaPreimage H => z.val i) he
    exact mul_left_cancel hi
  · intro v
    let u : Fin n → (CanonicalRV.RVSort M)ˣ := fun i => (c i)⁻¹ * v.val i
    have hu : u ∈ A.carrier := by
      apply (hshift _).mpr
      have he : (fun i => rvUnitValueHom (c i) * rvUnitTupleValues u i) = rvUnitTupleValues v.val := by
        funext i
        change rvUnitValueHom (c i) * rvUnitValueHom ((c i)⁻¹ * v.val i) = _
        rw [map_mul,map_inv]
        exact mul_inv_cancel_left _ _
      rw [he]
      exact v.property
    refine ⟨⟨u,hu⟩,Subtype.ext ?_⟩
    funext i
    exact mul_inv_cancel_left (c i) (v.val i)

/-- A stipulated original-ground RV multiplier gives the genuine Gamma
translation morphism, with a lift on every full value fibre. -/
def gammaGroundGammaSinglePointTranslation (G H : GammaGroundGammaPiece hc B n)
    (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c})
    (hshift : ∀ γ : Fin n → Values.Gamma (M := M),
      γ ∈ G.carrier ↔ (fun i => rvUnitValueHom (c i) * γ i) ∈ H.carrier) :
    GammaGroundGammaObject.single G ⟶ GammaGroundGammaObject.single H :=
  gammaGroundGammaSingleHomOfAffineMonomial G H
    (gammaGroundRVUnitPointTranslation G H c hcdef hshift) 1 (by simp) c
    (by intro u; rw [integerMonomialMap_one]; rfl)
end DiamondIntegral.Section3
