import «section 3».GammaGroundShearSlices
import «section 3».GammaGroundGammaAffineClassification
import «section 3».GammaGroundRVUnitSingletonPoints
import «section 3».GammaGroundIntegralAffineCriterion
import «section 3».GammaGroundAffineSliceFormula
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- Every full-preimage contraction between arbitrary Gamma tuples is
piecewise integral-affine over its complete original ground. The map
need not be injective; matrices may be rectangular and singular. -/
theorem gammaGround_contraction_piecewiseIntegralAffine [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin (n+m) → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (I : GammaGroundGammaPiece hc B n) (J : GammaGroundGammaPiece hc B m) (h : GammaGroundMap I J)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I) (gammaGroundRVUnitGammaPreimage J))
    (hf : ∀ u, rvUnitTupleValues (f u).val = (h (gammaGroundFullPreimageValueMap I u)).val) :
    GammaGroundPiecewiseIntegralAffine h := by
  let g := gammaGroundGammaShear I f.toUniv (gammaGroundRV_value_kernel_of_contraction I f.toUniv h.toUniv hf)
  let H := gammaGroundSingleFamilyBijection g.bijection
  let G := GammaGroundShearDomain I m
  have hg := gammaGroundGammaHom_piecewiseGLZ hκ hs h00 hsmall hγsmall RY g
  have hpoint : ∀ γ : G, ∃ F : OriginalGroundAffineRVFormula hc B (n+m),
      (H.map γ).val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.val := by
    intro γ
    exact gammaGroundPiecewiseGLZ_pointwise g.bijection hg ⟨(0 : Fin 1),γ⟩
  obtain ⟨N,F,P,hP,hcover,hformula⟩ := gammaGroundAffine_finite_partition hκ.le hs hsmall hγsmall G G H.map hpoint
  let slice := gammaGroundGammaUnitSlice I m
  let Q := fun i => slice.preimage (P i)
  have hQ (i : Fin N) (γ : I) : γ.val ∈ (Q i).carrier ↔ (slice γ).val ∈ (P i).carrier := by
    constructor
    · rintro ⟨a,ha,hpa⟩
      have he : a = γ := Subtype.ext ha
      exact he ▸ hpa
    · exact fun hp => ⟨γ,rfl,hp⟩
  refine ⟨N,Q,fun i j k => (F i).matrix (Fin.natAdd n j) (Fin.castAdd m k),
    fun i j => (F i).coefficient (Fin.natAdd n j),fun i => slice.preimage_subset (P i),?_,?_,?_⟩
  · intro γ
    obtain ⟨i,hi,huniq⟩ := hcover (slice γ)
    exact ⟨i,(hQ i γ).mpr hi,fun j hj => huniq j ((hQ j γ).mp hj)⟩
  · intro i j
    exact (gammaGroundRVUnitTuple_point_definable_iff (F i).coefficient).mp
      (F i).coefficient_definable (Fin.natAdd n j)
  · intro i γ hγ
    have hform := hformula i (slice γ) ((hQ i γ).mp hγ)
    have hslice := gammaGroundGammaShear_unit_slice I f.toUniv h.toUniv hf γ
    change (H.map (slice γ)).val = Fin.append γ.val (h γ).val at hslice
    rw [gammaGroundGammaUnitSlice_formula] at hform
    have he := congrArg (fun v : Fin (n+m) → Values.Gamma (M := M) => fun j : Fin m => v (Fin.natAdd n j))
      (hslice.symm.trans hform)
    have hleft : (fun j : Fin m => Fin.append γ.val (h γ).val (Fin.natAdd n j)) = (h γ).val :=
      funext (fun j => Fin.append_right γ.val (h γ).val j)
    exact hleft.symm.trans (he.trans (integralAffine_identity_slice_bottom
      (F i).matrix (rvUnitTupleValues (F i).coefficient)
      (show Fin n → Values.Gamma (M := M) from γ.val)))

end DiamondIntegral.Section3
