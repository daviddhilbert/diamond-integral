import «section 3».MeasuredTensorCoefficientRelations
import «section 3».TensorFiniteFactorAbsorption
import «section 3».GammaGroundGammaRVProductLift
import «section 3».GammaGroundMeasuredRESProducts
import «section 3».GammaGroundMeasuredRESGradedSemiring
import «section 3».GammaGroundMeasuredGammaCodeCoherence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r : ℕ}

def gammaGroundConstantForm {Q : Space LRV M} (A : GammaGroundDefSet hc B Q)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) : GammaGroundVolumeForm hc B A := by
  letI : Nonempty ((volumeGammaSpace hc).power (Fin 0)).Carrier := ⟨(Fin.elim0 : Fin 0 → Values.Gamma (M := M))⟩
  letI : Subsingleton ((volumeGammaSpace hc).power (Fin 0)).Carrier :=
    ⟨fun a b => by change (Fin 0 → Values.Gamma (M := M)) at a b; exact funext (fun i => i.elim0)⟩
  exact (fullGammaFunctionMap (n := 0) (fun _ => δ) (FullGammaFunction.constant δ (integrationGammaDefinable hδ))).comp
    (GammaGroundMap.ofGlobal A (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin 0)))
      (Map.toSubsingleton (DefSet.univ Q B.real) ((volumeGammaSpace hc).power (Fin 0))) (fun _ => Set.mem_univ _))

@[simp] theorem gammaGroundConstantForm_value {Q : Space LRV M} (A : GammaGroundDefSet hc B Q)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (a : A) :
    gammaGroundFormValue (gammaGroundConstantForm A δ hδ) a = δ := rfl

def GammaGroundMeasuredRESObject.shiftCombinedWeight (X : GammaGroundMeasuredRESObject hc B r)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) : GammaGroundMeasuredRESObject hc B r :=
  ⟨X.obj.underlying.withCombinedWeight (X.obj.combinedWeightForm.mul
    (gammaGroundConstantForm X.obj.underlying.domain δ hδ)),X.property⟩

@[simp] theorem GammaGroundMeasuredRESObject.shiftCombinedWeight_value (X : GammaGroundMeasuredRESObject hc B r)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (a : X.obj.underlying.domain) :
    (X.shiftCombinedWeight δ hδ).obj.combinedWeight a = X.obj.combinedWeight a * δ := by
  change (X.obj.underlying.withCombinedWeight (X.obj.combinedWeightForm.mul
    (gammaGroundConstantForm X.obj.underlying.domain δ hδ))).combinedWeight a = _
  rw [GammaGroundRVObject.withCombinedWeight_value,GammaGroundVolumeForm.mul_value,
    X.obj.combinedWeightForm_value,gammaGroundConstantForm_value]

/-- A weight scalar belongs to the shared finite Gamma coefficient
semiring in degree zero; its full form is retained. -/
def gammaGroundMeasuredGammaScalar (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    GammaGroundMeasuredFiniteGammaObject hc B 0 :=
  let A := gammaGroundMeasuredGammaSingleWeight
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin 0))) (fun _ => δ)
      (FullGammaFunction.constant δ (integrationGammaDefinable hδ))
  ⟨A,A.underlying.degree_zero_finite⟩

theorem gammaGroundMeasuredGammaScalar_lift_weight
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (a : (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).resLift.obj.underlying.domain) :
    (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).resLift.obj.combinedWeight a = δ := by
  let G := GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin 0))
  obtain ⟨u,rfl⟩ := (gammaGroundGammaUnitLiftBijection G).bijective.2 a
  exact gammaGroundMeasuredGammaUnitLift_combined G (fun _ => δ)
    (FullGammaFunction.constant δ (integrationGammaDefinable hδ)) u

/-- On RES, multiplication by the lifted shared scalar changes exactly
the combined weight, through an actual original-ground RV bijection. -/
theorem gammaGroundMeasuredRES_shift_scalar_class (X : GammaGroundMeasuredRESObject hc B r)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    gammaGroundMeasuredRESDirectSumClass (X.shiftCombinedWeight δ hδ) =
      gammaGroundMeasuredRESDirectSumClass X *
        gammaGroundMeasuredRESDirectSumClass (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).resLift := by
  let C := (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).resLift
  let F : GammaGroundBijection (X.obj.product C.obj).underlying.domain X.obj.underlying.domain :=
    (gammaGroundRVRightUnitProjection X.obj.underlying).comp
      (((GammaGroundBijection.id X.obj.underlying.domain).prodMap gammaGroundGammaRVUnitBijection).comp
        (gammaGroundRVPackBijection X.obj.underlying.domain C.obj.underlying.domain).symm)
  have hF (a : X.obj.underlying.domain) (b : C.obj.underlying.domain) :
      F.map (gammaGroundRVPackPair X.obj.underlying.domain C.obj.underlying.domain a b) = a := by
    change GammaGroundMap.prodFst X.obj.underlying.domain (GammaGroundRVObject.unit hc B).domain
      (((GammaGroundBijection.id X.obj.underlying.domain).prodMap gammaGroundGammaRVUnitBijection).map
        (gammaGroundRVUnpack X.obj.underlying.domain C.obj.underlying.domain
          (gammaGroundRVPackPair X.obj.underlying.domain C.obj.underlying.domain a b))) = a
    rw [gammaGroundRVUnpack_pair]
    rfl
  let f : GammaGroundMeasuredRVHom (X.obj.product C.obj) (X.shiftCombinedWeight δ hδ).obj :=
    { bijection := F
      preserves := by
        intro p
        obtain ⟨a,b,rfl⟩ := exists_gammaGroundRVPackPair X.obj.underlying.domain C.obj.underlying.domain p
        rw [GammaGroundMeasuredRVObject.product_combined_pair,hF,
          gammaGroundMeasuredGammaScalar_lift_weight,X.shiftCombinedWeight_value] }
  let e : (X.product C).obj ≅ (X.shiftCombinedWeight δ hδ).obj := asIso (show _ ⟶ _ from f)
  have he := gammaGroundMeasuredRESClass_iso (gammaGroundMeasuredResProperty.isoMk e)
  rw [← gammaGroundMeasuredRESDirectSumClass_product]
  exact (congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) r) he).symm

variable {n : ℕ}

def GammaGroundMeasuredGammaObject.shiftCombinedWeight (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) : GammaGroundMeasuredGammaObject hc B n :=
  ⟨A.underlying,fun i => (A.form i).mul (gammaGroundConstantForm (A.underlying.piece i) δ hδ)⟩

@[simp] theorem GammaGroundMeasuredGammaObject.shiftCombinedWeight_value (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (a : A.underlying.Carrier) :
    (A.shiftCombinedWeight δ hδ).combinedWeight a = A.combinedWeight a * δ := by
  change gammaGroundFormValue ((A.form a.1).mul (gammaGroundConstantForm _ δ hδ)) a.2 * _ = _
  rw [GammaGroundVolumeForm.mul_value,gammaGroundConstantForm_value]
  change (_ * δ) * _ = (_ * _) * δ
  ac_rfl

theorem gammaGroundMeasuredGammaScalar_combined
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (a : (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj.underlying.Carrier) :
    (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj.combinedWeight a = δ :=
  gammaGroundMeasuredGammaSingleWeight_combined _ (fun _ => δ)
    (FullGammaFunction.constant δ (integrationGammaDefinable hδ)) a

theorem gammaGroundMeasuredGammaProduct_scalar_combined (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (a : (A.product (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj).underlying.Carrier) :
    (A.product (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj).combinedWeight a =
      (A.product (GammaGroundMeasuredGammaObject.unit hc B)).combinedWeight a * δ := by
  rcases a with ⟨i,z⟩
  obtain ⟨⟨⟨x,y⟩,hx,hy⟩,hz⟩ := (gammaGroundGammaAppendBijection
    (A.underlying.piece (finProdFinEquiv.symm i).1)
    ((GammaGroundGammaObject.unit hc B).piece (finProdFinEquiv.symm i).2)).bijective.2 z
  subst z
  have hl := gammaGroundMeasuredGammaProduct_combined A (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj
    (show Fin (A.underlying.tags * (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj.underlying.tags) from i) ⟨x,hx⟩ ⟨y,hy⟩
  have hr := gammaGroundMeasuredGammaProduct_combined A (GammaGroundMeasuredGammaObject.unit hc B)
    (show Fin (A.underlying.tags * (GammaGroundMeasuredGammaObject.unit hc B).underlying.tags) from i) ⟨x,hx⟩ ⟨y,hy⟩
  rw [gammaGroundMeasuredGammaUnit_combined,mul_one] at hr
  exact hl.trans ((congrArg (fun z => A.combinedWeight ⟨(finProdFinEquiv.symm i).1,⟨x,hx⟩⟩ * z)
    (gammaGroundMeasuredGammaScalar_combined δ hδ ⟨(finProdFinEquiv.symm i).2,⟨y,hy⟩⟩)).trans
      (congrArg (fun z => z * δ) hr).symm)

def gammaGroundMeasuredGammaScalarRightUnitHom (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    GammaGroundMeasuredGammaHom (A.product (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj)
      (A.shiftCombinedWeight δ hδ) where
  underlying := (gammaGroundMeasuredGammaProductRightUnitHom A).underlying
  preserves a := by
    rw [gammaGroundMeasuredGammaProduct_scalar_combined,
      (gammaGroundMeasuredGammaProductRightUnitHom A).preserves a,A.shiftCombinedWeight_value]
    rfl

theorem gammaGroundMeasuredGamma_shift_scalar_class (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    gammaGroundMeasuredGammaSemiringClass (A.shiftCombinedWeight δ hδ) =
      gammaGroundMeasuredGammaSemiringClass A *
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaScalar (hc := hc) δ hδ).obj := by
  have he := gammaGroundMeasuredGammaSemiringClass_iso
    (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaScalarRightUnitHom A δ hδ))
  exact he.symm.trans (gammaGroundMeasuredGammaSemiringClass_product A _)

/-- A common original-ground weight shift moves between the two factors
by positive balancing over the shared finite measured Gamma semiring. -/
theorem gammaGroundMeasuredTensor_shared_weight_shift (X : GammaGroundMeasuredRESObject hc B r)
    (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :
    gammaGroundMeasuredRESDirectSumClass (X.shiftCombinedWeight δ hδ) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass A =
    gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (A.shiftCombinedWeight δ hδ) := by
  let C := gammaGroundMeasuredGammaScalar (hc := hc) δ hδ
  have hr : gammaGroundMeasuredRESDirectSumClass (X.shiftCombinedWeight δ hδ) =
      gammaGroundMeasuredRESDirectSumClass (X.product C.resLift) := by
    rw [gammaGroundMeasuredRESDirectSumClass_product]
    exact gammaGroundMeasuredRES_shift_scalar_class X δ hδ
  rw [hr,← gammaGroundMeasuredTensor_finite_factor_absorption X C A,
    gammaGroundMeasuredGamma_shift_scalar_class,mul_comm (gammaGroundMeasuredGammaSemiringClass A)]
end DiamondIntegral.Section3
