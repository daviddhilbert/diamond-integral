import «section 3».TensorCoefficientRelations
import «section 3».MeasuredTensorChart
import «section 3».MeasuredTensorSurjectivity
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

/-- The product chart retains the RES weight and the prescribed full
Gamma weight, including finite and degree-zero factors. -/
theorem gammaGroundMeasuredTensorNativeProduct_weight
    (X : GammaGroundMeasuredRVObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (a : X.underlying.domain) (u : gammaGroundRVUnitGammaPreimage G) :
    (X.product (gammaGroundMeasuredGammaSingleWeight G f hf).rvLift).combinedWeight
      ((gammaGroundTensorNativeProductBijection X.underlying G).map
        ⟨(a.val,u.val),a.property,u.property⟩) =
      X.combinedWeight a * f (rvUnitTupleValues u.val) := by
  rw [gammaGroundTensorNativeProductBijection_pair]
  exact (GammaGroundMeasuredRVObject.product_combined_pair X
    (gammaGroundMeasuredGammaSingleWeight G f hf).rvLift a
    ((gammaGroundGammaUnitLiftBijection G).map u)).trans
      (congrArg (fun z => X.combinedWeight a * z)
        (gammaGroundMeasuredGammaUnitLift_combined G f hf u))

/-- Constant-value coefficient translations preserve measured products
when the full Gamma weight is transported along the translation. -/
theorem gammaGroundMeasuredTensor_coefficient_pair (X : GammaGroundMeasuredRESObject hc B r)
    (G H : GammaGroundGammaPiece hc B n)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (hh : FullGammaFunction (integrationGammaBase B) h)
    (c : GammaGroundMap X.obj.underlying.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (delta : Fin n → Values.Gamma (M := M))
    (hcval : ∀ a : X.obj.underlying.domain, rvUnitTupleValues (c a).val = delta)
    (hshift : ∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier ↔ (fun i => delta i * g i) ∈ H.carrier)
    (hweight : ∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier → f g = h (fun i => delta i * g i)) :
    gammaGroundMeasuredTensorMap
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf)) =
    gammaGroundMeasuredTensorMap
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight H h hh)) := by
  let Xu : GammaGroundRESObject hc B r := ⟨X.obj.underlying,X.property⟩
  let eG := gammaGroundTensorNativeProductBijection X.obj.underlying G
  let eH := gammaGroundTensorNativeProductBijection X.obj.underlying H
  let tr := gammaGroundRVUnitCoefficientTranslation X.obj.underlying.domain G H c delta hcval hshift
  let F := gammaGroundTensorCoefficientBijection Xu G H c delta hcval hshift
  rw [gammaGroundMeasuredTensorMap_objects,gammaGroundMeasuredTensorMap_objects]
  apply gammaGroundMeasuredRVSemiringClass_of_weight_bijection _ _ rfl F
  intro w
  obtain ⟨p,rfl⟩ := eG.bijective.2 w
  let a : X.obj.underlying.domain := ⟨p.val.1,p.property.1⟩
  let u : gammaGroundRVUnitGammaPreimage G := ⟨p.val.2,p.property.2⟩
  let v : gammaGroundRVUnitGammaPreimage H := ⟨(tr.map p).val.2,(tr.map p).property.2⟩
  have hF : F.map (eG.map p) = eH.map (tr.map p) := by
    change eH.map (tr.map (eG.map.inverse eG.bijective (eG.map p))) = _
    rw [GammaGroundMap.inverse_apply]
  have hv : rvUnitTupleValues v.val = fun i => delta i * rvUnitTupleValues u.val i := by
    funext i
    change rvUnitValueHom ((c a).val i * u.val i) = _
    rw [map_mul]
    exact congrArg (fun z => z * rvUnitTupleValues u.val i) (congrFun (hcval a) i)
  rw [hF]
  change (X.obj.product (gammaGroundMeasuredGammaSingleWeight G f hf).rvLift).combinedWeight
      (eG.map ⟨(a.val,u.val),a.property,u.property⟩) =
    (X.obj.product (gammaGroundMeasuredGammaSingleWeight H h hh).rvLift).combinedWeight
      (eH.map ⟨(a.val,v.val),a.property,v.property⟩)
  rw [gammaGroundMeasuredTensorNativeProduct_weight,
    gammaGroundMeasuredTensorNativeProduct_weight,hv,hweight _ u.property]

/-- Positive measured pairs retain the measured RES coefficient and
transport the entire Gamma combined weight. -/
def gammaGroundMeasuredCoefficientPair (a b : GammaGroundMeasuredPositiveTensor hc B) : Prop :=
  ∃ (r n : ℕ) (i : Fin n) (X : GammaGroundMeasuredRESObject hc B r)
      (G H : GammaGroundGammaPiece hc B n)
      (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hf : FullGammaFunction (integrationGammaBase B) f)
      (hh : FullGammaFunction (integrationGammaBase B) h)
      (delta : Fin n → Values.Gamma (M := M)),
    (∀ j, j ≠ i → delta j = 1) ∧
    (∀ j, GammaDefinableClosureAtBase B (delta j)) ∧
    GammaGroundRESAvailableValueTuple ⟨X.obj.underlying,X.property⟩ delta ∧
    (∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier ↔ (fun j => delta j * g j) ∈ H.carrier) ∧
    (∀ g : Fin n → Values.Gamma (M := M),
      g ∈ G.carrier → f g = h (fun j => delta j * g j)) ∧
    a = gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) ∧
    b = gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight H h hh)

def gammaGroundMeasuredCoefficientCongruence : RingCon (GammaGroundMeasuredPositiveTensor hc B) :=
  ringConGen (gammaGroundMeasuredCoefficientPair (hc := hc) (B := B))

theorem gammaGroundMeasuredCoefficientPair_valid
    {a b : GammaGroundMeasuredPositiveTensor hc B}
    (hab : gammaGroundMeasuredCoefficientPair a b) :
    gammaGroundMeasuredTensorMap a = gammaGroundMeasuredTensorMap b := by
  obtain ⟨r,n,i,X,G,H,f,h,hf,hh,delta,_,_,⟨c,hcval⟩,hshift,hweight,rfl,rfl⟩ := hab
  exact gammaGroundMeasuredTensor_coefficient_pair X G H f h hf hh c delta hcval hshift hweight

theorem gammaGroundMeasuredCoefficientCongruence_le_ker :
    gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B) ≤
      RingCon.ker (gammaGroundMeasuredTensorMap (hc := hc) (ground := B)) := by
  apply RingCon.ringConGen_le.mpr
  intro a b hab
  exact gammaGroundMeasuredCoefficientPair_valid hab

abbrev GammaGroundMeasuredCoefficientQuotient (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) :=
  (gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).Quotient

def gammaGroundMeasuredCoefficientQuotientMap :
    GammaGroundMeasuredCoefficientQuotient hc B →+* GammaGroundMeasuredRVPositiveSemiring hc B :=
  (gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).lift
    (gammaGroundMeasuredTensorMap (hc := hc) (ground := B))
    gammaGroundMeasuredCoefficientCongruence_le_ker

@[simp] theorem gammaGroundMeasuredCoefficientQuotientMap_class
    (a : GammaGroundMeasuredPositiveTensor hc B) :
    gammaGroundMeasuredCoefficientQuotientMap
      ((gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a) =
        gammaGroundMeasuredTensorMap a := rfl

theorem gammaGroundMeasuredCoefficientQuotientMap_surjective {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (gammaGroundMeasuredCoefficientQuotientMap (hc := hc) (B := B)) := by
  intro v
  obtain ⟨a,ha⟩ := gammaGroundMeasuredTensorMap_surjective (hc := hc) hκ hs h00 hsmall hγsmall hΓ v
  exact ⟨(gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a,ha⟩
end DiamondIntegral.Section3
