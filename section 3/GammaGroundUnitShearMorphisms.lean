import «section 3».GammaGroundUnitShears
import «section 3».GammaGroundUnitBijectionContraction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}

abbrev GammaGroundShearDomain (I : GammaGroundGammaPiece hc B n) (m : ℕ) :=
  (gammaGroundGammaAppendMap I (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).image

theorem gammaGroundRVUnitShear_value_kernel
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)))
    (hf : ∀ a b, rvUnitTupleValues a.val = rvUnitTupleValues b.val → rvUnitTupleValues (f a).val = rvUnitTupleValues (f b).val)
    (x y : gammaGroundRVUnitGammaPreimage (GammaGroundShearDomain I m)) :
    rvUnitTupleValues x.val = rvUnitTupleValues y.val ↔
      rvUnitTupleValues ((gammaGroundRVUnitShear I f).map x).val =
        rvUnitTupleValues ((gammaGroundRVUnitShear I f).map y).val := by
  let e := gammaGroundUnitPreimageProductBijection I
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
  obtain ⟨u,rfl⟩ := e.bijective.2 x
  obtain ⟨v,rfl⟩ := e.bijective.2 y
  rw [gammaGroundUnitPreimageProductBijection_formula,gammaGroundUnitPreimageProductBijection_formula,
    gammaGroundRVUnitShear_at_product,gammaGroundRVUnitShear_at_product,
    rvUnitTupleValues_append,rvUnitTupleValues_append,rvUnitTupleValues_append,rvUnitTupleValues_append]
  let ua : gammaGroundRVUnitGammaPreimage I := ⟨u.val.1,u.property.1⟩
  let va : gammaGroundRVUnitGammaPreimage I := ⟨v.val.1,v.property.1⟩
  let ub : Fin m → (CanonicalRV.RVSort M)ˣ := u.val.2
  let vb : Fin m → (CanonicalRV.RVSort M)ˣ := v.val.2
  change Fin.append (rvUnitTupleValues ua.val) (rvUnitTupleValues ub) =
      Fin.append (rvUnitTupleValues va.val) (rvUnitTupleValues vb) ↔
    Fin.append (rvUnitTupleValues ua.val)
        (rvUnitTupleValues ((show Fin m → (CanonicalRV.RVSort M)ˣ from (f ua).val) * ub)) =
      Fin.append (rvUnitTupleValues va.val)
        (rvUnitTupleValues ((show Fin m → (CanonicalRV.RVSort M)ˣ from (f va).val) * vb))
  rw [rvUnitTupleValues_mul,rvUnitTupleValues_mul]
  constructor
  · intro h
    have hp : (rvUnitTupleValues ua.val,rvUnitTupleValues ub) =
        (rvUnitTupleValues va.val,rvUnitTupleValues vb) :=
      (Fin.appendEquiv (α := Values.Gamma (M := M)) n m).injective h
    have hfirst : rvUnitTupleValues ua.val = rvUnitTupleValues va.val := congrArg Prod.fst hp
    have hsecond : rvUnitTupleValues ub = rvUnitTupleValues vb := congrArg Prod.snd hp
    have hcoeff := hf ua va hfirst
    exact congrArg₂ Fin.append hfirst (congrArg₂ (· * ·) hcoeff hsecond)
  · intro h
    have hp : (rvUnitTupleValues ua.val,rvUnitTupleValues (f ua).val * rvUnitTupleValues ub) =
        (rvUnitTupleValues va.val,rvUnitTupleValues (f va).val * rvUnitTupleValues vb) :=
      (Fin.appendEquiv (α := Values.Gamma (M := M)) n m).injective h
    have hfirst : rvUnitTupleValues ua.val = rvUnitTupleValues va.val := congrArg Prod.fst hp
    have hsecond : rvUnitTupleValues (f ua).val * rvUnitTupleValues ub =
        rvUnitTupleValues (f va).val * rvUnitTupleValues vb := congrArg Prod.snd hp
    have hcoeff := hf ua va hfirst
    have hβ : rvUnitTupleValues ub = rvUnitTupleValues vb := mul_left_cancel
      (hsecond.trans (congrArg (fun c : Fin m → Values.Gamma (M := M) => c * rvUnitTupleValues vb) hcoeff.symm))
    exact congrArg₂ Fin.append hfirst hβ

/-- A value-contracting map stabilizes to a genuine Gamma morphism in
the larger degree, even if the original map is not injective. -/
def gammaGroundGammaShear
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)))
    (hf : ∀ a b, rvUnitTupleValues a.val = rvUnitTupleValues b.val → rvUnitTupleValues (f a).val = rvUnitTupleValues (f b).val) :
    GammaGroundGammaHom (GammaGroundGammaObject.single (GammaGroundShearDomain I m))
      (GammaGroundGammaObject.single (GammaGroundShearDomain I m)) :=
  gammaGroundGammaSingleHomOfUnitBijection _ _ (gammaGroundRVUnitShear I f)
    (gammaGroundRVUnitShear_value_kernel I f hf)

theorem gammaGroundGammaShear_at_product
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)))
    (hf : ∀ a b, rvUnitTupleValues a.val = rvUnitTupleValues b.val → rvUnitTupleValues (f a).val = rvUnitTupleValues (f b).val)
    (u : (gammaGroundRVUnitGammaPreimage I).prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m))) :
    let p := (gammaGroundUnitPreimageProductBijection I
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).map u
    ((gammaGroundGammaShear I f hf).bijection.equiv
      ⟨(0 : Fin 1),⟨rvUnitTupleValues p.val,p.property⟩⟩).2.val =
      Fin.append (rvUnitTupleValues u.val.1) (rvUnitTupleValues (f ⟨u.val.1,u.property.1⟩).val * rvUnitTupleValues u.val.2) := by
  dsimp only
  let e := gammaGroundUnitPreimageProductBijection I
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
  have hc := gammaGroundGammaSingleHomOfUnitBijection_contract
    (GammaGroundShearDomain I m) (GammaGroundShearDomain I m) (gammaGroundRVUnitShear I f)
    (gammaGroundRVUnitShear_value_kernel I f hf) (e.map u)
  have hv : rvUnitTupleValues ((gammaGroundRVUnitShear I f).map (e.map u)).val =
      Fin.append (rvUnitTupleValues u.val.1)
        (rvUnitTupleValues (f ⟨u.val.1,u.property.1⟩).val * rvUnitTupleValues u.val.2) := by
    rw [gammaGroundRVUnitShear_at_product,rvUnitTupleValues_append]
    exact congrArg (Fin.append (rvUnitTupleValues u.val.1))
      (rvUnitTupleValues_mul (show Fin m → (CanonicalRV.RVSort M)ˣ from (f ⟨u.val.1,u.property.1⟩).val)
        (show Fin m → (CanonicalRV.RVSort M)ˣ from u.val.2))
  exact hc.trans hv

end DiamondIntegral.Section3
