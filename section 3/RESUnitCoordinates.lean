import «section 3».RVNonzeroTupleCoding
import «section 3».GammaGroundRVCategories
import «section 3».RVAngularQuotient
import «section 3».TensorLocalMonomialCongruence
import «section 3».GammaGroundBijectionRestrictions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

/-- Values of the fixed nonzero tuple code are determined by the original
value tuple, including the zero branch. -/
def rvNonzeroTupleValueCode (γ : Fin n → Section2.GammaInfinity M) :
    Fin (n*2) → Section2.GammaInfinity M := fun j =>
  let q := finProdFinEquiv.symm j
  if q.2 = 0 then
    if γ q.1 = Values.infinity then Values.vrv (Section2.rv M (1 : Section2.VF M)) else γ q.1
  else if γ q.1 = Values.infinity then Values.vrv (Section2.rv M (1 : Section2.VF M))
    else Values.vrv (Section2.rv M (-1 : Section2.VF M))

theorem rvNonzeroTupleCode_values (t : Fin n → CanonicalRV.RVSort M) :
    (fun j => (rvUnitTupleValues (rvNonzeroTupleCode t) j).val) =
      rvNonzeroTupleValueCode (fun i => Values.vrv (t i)) := by
  funext j
  change Values.vrv ⟨Section2.nonzeroRVCode (t (finProdFinEquiv.symm j).1).val (finProdFinEquiv.symm j).2,_⟩ = _
  rw [rvNonzeroTupleValueCode]
  simp only [Values.vrv_eq_infinity_iff]
  by_cases hj : (finProdFinEquiv.symm j).2 = 0 <;>
    by_cases hz : (t (finProdFinEquiv.symm j).1).val = iRVZero <;>
    simp only [Section2.nonzeroRVCode,hj,hz,ite_true,ite_false]

/-- Encoding a RES domain by nonzero tuples preserves finite value
support and adds no parameters or Gamma factors. -/
theorem gammaGroundRES_nonzero_code_finite
    {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    (X : GammaGroundRESObject hc B r) :
    (rvUnitTupleValues '' (gammaGroundRVNonzeroTupleCodeMap X.obj.domain).image.carrier).Finite := by
  let emb (γ : Fin (X.obj.arity*2) → Values.Gamma (M := M)) := fun j => (γ j).val
  have hi : Function.Injective emb := by
    intro a b h
    funext j
    exact Subtype.ext (congrFun h j)
  apply ((X.property.image rvNonzeroTupleValueCode).preimage hi.injOn).subset
  rintro _ ⟨u,⟨a,ha⟩,rfl⟩
  refine ⟨(fun i => Values.vrv (a.val i)),⟨a.val,a.property,rfl⟩,?_⟩
  have hau : rvNonzeroTupleCode a.val = u := ha
  change rvNonzeroTupleValueCode (fun i => Values.vrv (a.val i)) = emb (rvUnitTupleValues u)
  rw [← hau]
  exact (rvNonzeroTupleCode_values a.val).symm

/-- A native unit presentation of an actual RES object, with its original
label degree retained separately from its ambient tuple arity. -/
structure GammaGroundRESUnitChart (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (r : ℕ) where
  object : GammaGroundRESObject hc B r
  arity : ℕ
  native : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) arity)
  finite_values : (rvUnitTupleValues '' native.carrier).Finite
  bijection : GammaGroundBijection object.obj.domain native

/-- Every RES coefficient has one original-ground native unit chart.
The fixed zero encoding avoids a further partition of the coefficient. -/
def gammaGroundRESUnitChart (h00 : M ⊨ Axioms.ACVF00)
    {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    (X : GammaGroundRESObject hc B r) : GammaGroundRESUnitChart hc B r :=
  ⟨X,X.obj.arity*2,(gammaGroundRVNonzeroTupleCodeMap X.obj.domain).image,
    gammaGroundRES_nonzero_code_finite X,gammaGroundRVNonzeroTupleCodeBijection h00 X.obj.domain⟩

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- A native RES restriction retains the original finite label via its
actual preimage. -/
def GammaGroundRESUnitChart.restrict (X : GammaGroundRESUnitChart hc B r)
    (D : GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (hD : D.carrier ⊆ X.native.carrier) :
    GammaGroundRESUnitChart hc B r :=
  ⟨X.object.restrict (X.bijection.inverseImage D) (X.bijection.inverseImage_subset D),
    X.arity,D,X.finite_values.subset (Set.image_mono hD),X.bijection.restrictTarget D hD⟩

/-- Native local monomial comparisons transport through the stored RES
charts to the actual labelled coefficients in the positive tensor. -/
theorem GammaGroundRESUnitChart.local_monomial_congruence {m : ℕ}
    (X Y : GammaGroundRESUnitChart hc B r)
    (s : GammaGroundMap X.native (GammaGroundDefSet.univ hc B (rawRVUnitSpace Y.arity)))
    (hs : Function.Injective s) (hsub : s.image.carrier ⊆ Y.native.carrier)
    (G : GammaGroundGammaPiece hc B m) (C : Matrix (Fin m) (Fin m) ℤ) (hC : IsUnit C.det)
    (c : GammaGroundMap X.native (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (δ : Fin m → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hcval : ∀ a : X.native, rvUnitTupleValues (c a).val = δ) :
    gammaGroundUnmeasuredCoefficientCongruence
      (gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G))
      (gammaGroundRESDirectSumClass (Y.restrict s.image hsub).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single
          (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ))) := by
  let es : GammaGroundBijection X.native s.image := ⟨s.toImage,s.toImage_bijective hs⟩
  let e := (Y.restrict s.image hsub).bijection.symm.comp (es.comp X.bijection)
  exact gammaGroundUnmeasuredCoefficientCongruence_local_monomial X.object (Y.restrict s.image hsub).object
    e G C hC (c.comp X.bijection.map) δ hδ (fun a => hcval (X.bijection.map a))
end DiamondIntegral.Section3
