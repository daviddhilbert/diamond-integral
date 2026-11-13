import «section 3».GammaGroundUnitFibreDescent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- The morphism obtained by full-code descent contracts the original
unit bijection pointwise; its computation does not use classification. -/
theorem gammaGroundGammaSingleHomOfUnitBijection_contract
    (I J : GammaGroundGammaPiece hc B n)
    (F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage I) (gammaGroundRVUnitGammaPreimage J))
    (hF : ∀ u v, rvUnitTupleValues u.val = rvUnitTupleValues v.val ↔
      rvUnitTupleValues (F.map u).val = rvUnitTupleValues (F.map v).val)
    (u : gammaGroundRVUnitGammaPreimage I) :
    ((gammaGroundGammaSingleHomOfUnitBijection I J F hF).bijection.equiv
      ⟨(0 : Fin 1),⟨rvUnitTupleValues u.val,u.property⟩⟩).2.val = rvUnitTupleValues (F.map u).val := by
  let c := (gammaGroundRVUnitFullCodeBijection I).map u
  let T := gammaGroundUnitFullCodeTransport I J F
  let L : GammaGroundFamilyBijection (GammaGroundGammaObject.single I).codeLift
      (GammaGroundGammaObject.single J).codeLift :=
    GammaGroundFamilyBijection.pieces (GammaGroundGammaObject.single I).codeLift
      (fun _ => gammaGroundCodePreimage J) (fun _ => T)
  have hp : (GammaGroundGammaObject.single I).decode ⟨(0 : Fin 1),c⟩ =
      (⟨(0 : Fin 1),⟨rvUnitTupleValues u.val,u.property⟩⟩ : (GammaGroundGammaObject.single I).Carrier) := by
    change (⟨(0 : Fin 1),gammaGroundCodeDecode I c⟩ : Σ _ : Fin 1, I) = _
    exact congrArg (Sigma.mk (0 : Fin 1)) (Subtype.ext (gammaGroundRVUnitFullCode_decode I u))
  have hdec : ∀ a b, (GammaGroundGammaObject.single I).decode a = (GammaGroundGammaObject.single I).decode b →
      (GammaGroundGammaObject.single J).decode (L.equiv a) = (GammaGroundGammaObject.single J).decode (L.equiv b) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hab
    rw [gammaGroundGammaSingle_decode_eq_iff,gammaGroundRVUnitFullCode_inverse_decode,
      gammaGroundRVUnitFullCode_inverse_decode] at hab
    apply (gammaGroundGammaSingle_decode_eq_iff J i j _ _).mpr
    change (gammaGroundCodeDecode J ((gammaGroundUnitFullCodeTransport I J F).map a)).val =
      (gammaGroundCodeDecode J ((gammaGroundUnitFullCodeTransport I J F).map b)).val
    rw [gammaGroundUnitFullCodeTransport_decode,gammaGroundUnitFullCodeTransport_decode]
    exact (hF _ _).mp hab
  have he := gammaGroundFamilyDescendedMap_decode L hdec ⟨(0 : Fin 1),c⟩
  rw [hp] at he
  have hv := congrArg (fun t : (GammaGroundGammaObject.single J).Carrier => t.2.val) he
  change _ = (gammaGroundCodeDecode J ((gammaGroundUnitFullCodeTransport I J F).map c)).val at hv
  rw [gammaGroundUnitFullCodeTransport_decode] at hv
  have hc : (gammaGroundRVUnitFullCodeBijection I).symm.map c = u :=
    (gammaGroundRVUnitFullCodeBijection I).map.inverse_apply (gammaGroundRVUnitFullCodeBijection I).bijective u
  rw [hc] at hv
  exact hv

end DiamondIntegral.Section3
