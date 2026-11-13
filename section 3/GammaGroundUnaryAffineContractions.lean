import «section 3».GammaGroundShearSlices
import «section 3».GammaGroundGammaAffineClassification
import «section 3».GammaGroundRVUnitSingletonPoints
import «section 3».GammaGroundUnaryAffineCriterion
import «section 3».GammaGroundUnaryShearFormula
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- A potentially nonbijective unary full-preimage contraction is
piecewise integral-affine. Stabilization reduces it to the locally
proved bijective criterion; no [19] or HK input is used. -/
theorem gammaGroundUnary_contraction_piecewiseIntegralAffine [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 2 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (I J : GammaGroundGammaPiece hc B 1) (h : GammaGroundMap I J)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I) (gammaGroundRVUnitGammaPreimage J))
    (hf : ∀ u, rvUnitTupleValues (f u).val = (h (gammaGroundFullPreimageValueMap I u)).val) :
    GammaGroundUnaryPiecewiseIntegralAffine h := by
  let g := gammaGroundGammaShear I f.toUniv (gammaGroundRV_value_kernel_of_contraction I f.toUniv h.toUniv hf)
  let H := gammaGroundSingleFamilyBijection g.bijection
  let G := GammaGroundShearDomain I 1
  have hg := gammaGroundGammaHom_piecewiseGLZ hκ hs h00 hsmall hγsmall RY g
  have hpoint : ∀ γ : G, ∃ F : OriginalGroundAffineRVFormula hc B 2,
      (H.map γ).val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.val := by
    intro γ
    exact gammaGroundPiecewiseGLZ_pointwise g.bijection hg ⟨(0 : Fin 1),γ⟩
  obtain ⟨N,F,P,hP,hcover,hformula⟩ := gammaGroundAffine_finite_partition hκ.le hs hsmall hγsmall G G H.map hpoint
  let slice := gammaGroundGammaUnitSlice I 1
  let Q := fun i => slice.preimage (P i)
  have hQ (i : Fin N) (γ : I) : γ.val ∈ (Q i).carrier ↔ (slice γ).val ∈ (P i).carrier := by
    constructor
    · rintro ⟨a,ha,hpa⟩
      have he : a = γ := Subtype.ext ha
      exact he ▸ hpa
    · exact fun hp => ⟨γ,rfl,hp⟩
  refine ⟨N,Q,fun i => (F i).matrix (1 : Fin 2) 0,fun i => (F i).coefficient (1 : Fin 2),
    fun i => slice.preimage_subset (P i),?_,?_,?_⟩
  · intro γ
    obtain ⟨i,hi,huniq⟩ := hcover (slice γ)
    exact ⟨i,(hQ i γ).mpr hi,fun j hj => huniq j ((hQ j γ).mp hj)⟩
  · intro i
    exact (gammaGroundRVUnitTuple_point_definable_iff (F i).coefficient).mp (F i).coefficient_definable (1 : Fin 2)
  · intro i γ hγ
    have hform := hformula i (slice γ) ((hQ i γ).mp hγ)
    have hslice := gammaGroundGammaShear_unit_slice I f.toUniv h.toUniv hf γ
    change (H.map (slice γ)).val = Fin.append γ.val (h γ).val at hslice
    rw [gammaGroundGammaUnitSlice_formula] at hform
    have he := congrFun (hslice.symm.trans hform) (1 : Fin 2)
    have hleft : (Fin.append γ.val (h γ).val) (1 : Fin 2) = (h γ).val (0 : Fin 1) :=
      Fin.append_right γ.val (h γ).val (0 : Fin 1)
    exact hleft.symm.trans (he.trans (integralAffine_shear_slice_coordinate
      (F i).matrix (rvUnitTupleValues (F i).coefficient)
      (show Fin 1 → Values.Gamma (M := M) from γ.val)))

end DiamondIntegral.Section3
