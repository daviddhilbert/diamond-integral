import «section 3».TensorPieceNormalForm
import «section 3».RESUnitCoordinates
import «section 3».TensorCoefficientRelations
import «section 3».GammaGroundRESPositiveComparison
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

theorem gammaGroundRESDirectSumClass_scissor
    (X : GammaGroundRESObject hc B r)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (hA : A.carrier ⊆ X.obj.domain.carrier) :
    gammaGroundRESDirectSumClass (X.restrict A hA) +
      gammaGroundRESDirectSumClass (X.restrict (X.obj.domain.sdiff A) (fun _ h => h.1)) =
      gammaGroundRESDirectSumClass X := by
  have h := congrArg (DirectSum.of (GammaGroundRESKPlus hc B) r) (gammaGroundRESClass_scissor X A hA)
  simpa only [gammaGroundRESDirectSumClass,map_add] using h

theorem gammaGroundGammaSemiringClass_piece_cut
    (G H : GammaGroundGammaPiece hc B n) (hH : H.carrier ⊆ G.carrier) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single H) +
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (G.sdiff H)) =
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) := by
  have h := congrArg (gammaGroundGammaKPlusToSemiring (hc := hc) (ground := B))
    (gammaGroundGammaClass_scissor (GammaGroundGammaObject.single G) (fun _ => H) (fun _ => hH))
  simp only [map_add,gammaGroundGammaKPlusToSemiring_class] at h
  dsimp [GammaGroundGammaObject.restrict,GammaGroundGammaObject.difference,GammaGroundGammaObject.single] at h
  exact h

/-- A product can be cut into a chosen rectangle and its two disjoint
product complements inside the positive tensor. This is a scissor identity,
not cancellation of a previously matched summand. -/
theorem gammaGroundUnmeasuredTensor_product_cut
    (X : GammaGroundRESObject hc B r)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (hA : A.carrier ⊆ X.obj.domain.carrier)
    (G H : GammaGroundGammaPiece hc B n) (hH : H.carrier ⊆ G.carrier) :
    gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
    (gammaGroundRESDirectSumClass (X.restrict A hA) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single H)) +
    (gammaGroundRESDirectSumClass (X.restrict A hA) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (G.sdiff H))) +
    (gammaGroundRESDirectSumClass (X.restrict (X.obj.domain.sdiff A) (fun _ h => h.1)) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G)) := by
  have hx := gammaGroundRESDirectSumClass_scissor X A hA
  have hg := gammaGroundGammaSemiringClass_piece_cut G H hH
  conv_lhs => rw [← hx,TensorProduct.add_tmul]
  conv_lhs => arg 1; rw [← hg,TensorProduct.tmul_add]

/-- The two positive remainder terms describe the actual complement of
the chosen native rectangle. This supports restriction of an RV bijection
between remainders without cancelling matched images. -/
theorem gammaGroundNativeProduct_rectangle_complement
    (X : GammaGroundRESObject hc B r)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (hA : A.carrier ⊆ X.obj.domain.carrier)
    (G H : GammaGroundGammaPiece hc B n)
    (a : (rawRVSpace (M := M) X.obj.arity).Carrier)
    (u : Fin n → (CanonicalRV.RVSort M)ˣ) :
    ((a,u) ∈ (X.obj.domain.prod (gammaGroundRVUnitGammaPreimage G)).carrier ∧
      ¬ (a,u) ∈ (A.prod (gammaGroundRVUnitGammaPreimage H)).carrier) ↔
    (a,u) ∈ ((X.obj.domain.sdiff A).prod (gammaGroundRVUnitGammaPreimage G)).carrier ∨
      (a,u) ∈ (A.prod (gammaGroundRVUnitGammaPreimage (G.sdiff H))).carrier := by
  change ((a ∈ X.obj.domain.carrier ∧ rvUnitTupleValues u ∈ G.carrier) ∧
    ¬ (a ∈ A.carrier ∧ rvUnitTupleValues u ∈ H.carrier)) ↔
    ((a ∈ X.obj.domain.carrier ∧ a ∉ A.carrier) ∧ rvUnitTupleValues u ∈ G.carrier) ∨
      (a ∈ A.carrier ∧ rvUnitTupleValues u ∈ G.carrier ∧ rvUnitTupleValues u ∉ H.carrier)
  constructor
  · rintro ⟨⟨ha,hu⟩,hn⟩
    by_cases h : a ∈ A.carrier
    · exact Or.inr ⟨h,hu,fun hh => hn ⟨h,hh⟩⟩
    · exact Or.inl ⟨⟨ha,h⟩,hu⟩
  · rintro (⟨⟨ha,hn⟩,hu⟩ | ⟨ha,hu,hn⟩)
    · exact ⟨⟨ha,hu⟩,fun h => hn h.1⟩
    · exact ⟨⟨hA ha,hu⟩,fun h => hn h.2⟩

/-- Partial preimages commute with relative complement in the map's
actual target. -/
theorem GammaGroundMap.preimage_target_sdiff {P Q : Space LRV M}
    {D : GammaGroundDefSet hc B P} {E : GammaGroundDefSet hc B Q}
    (f : GammaGroundMap D E) (Z : GammaGroundDefSet hc B Q) :
    f.preimage (E.sdiff Z) = D.sdiff (f.preimage Z) := by
  apply gammaGroundDefSet_eq_of_carrier_eq
  ext x
  constructor
  · rintro ⟨a,hax,_,haZ⟩
    refine ⟨hax ▸ a.property,?_⟩
    rintro ⟨b,hbx,hbZ⟩
    have hba : b = a := Subtype.ext (hbx.trans hax.symm)
    exact haZ (hba ▸ hbZ)
  · rintro ⟨hx,hn⟩
    let a : D := ⟨x,hx⟩
    exact ⟨a,rfl,(f a).property,fun ha => hn ⟨a,rfl,ha⟩⟩

/-- A cut in native unit coordinates induces a positive RES scissor
identity on the original labelled coefficient. -/
theorem GammaGroundRESUnitChart.class_cut (X : GammaGroundRESUnitChart hc B r)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (hA : A.carrier ⊆ X.native.carrier) :
    gammaGroundRESDirectSumClass (X.restrict A hA).object +
      gammaGroundRESDirectSumClass (X.restrict (X.native.sdiff A) (fun _ h => h.1)).object =
      gammaGroundRESDirectSumClass X.object := by
  have he := X.bijection.map.preimage_target_sdiff A
  have hcomp : gammaGroundRESDirectSumClass (X.restrict (X.native.sdiff A) (fun _ h => h.1)).object =
      gammaGroundRESDirectSumClass (X.object.restrict
        (X.object.obj.domain.sdiff (X.bijection.inverseImage A)) (fun _ h => h.1)) := by
    apply gammaGroundRESDirectSumClass_bijection
    exact GammaGroundBijection.ofCarrierEq (congrArg GammaGroundDefSet.carrier he)
  rw [hcomp]
  exact gammaGroundRESDirectSumClass_scissor X.object (X.bijection.inverseImage A)
    (X.bijection.inverseImage_subset A)
end DiamondIntegral.Section3
