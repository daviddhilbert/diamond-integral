import «section 3».GammaGroundUnitShearMorphisms
import «section 3».GammaGroundRVGenericScalarContraction
import «section 3».GammaGroundGammaUnitSlice
import «section 3».GammaGroundSingleFamilyBijections
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

/-- The value-kernel condition follows from pointwise contraction to an
actual interpreted Gamma map. -/
theorem gammaGroundRV_value_kernel_of_contraction
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)))
    (h : GammaGroundMap I (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m))))
    (hval : ∀ u, rvUnitTupleValues (f u).val = (h (gammaGroundFullPreimageValueMap I u)).val)
    (a b : gammaGroundRVUnitGammaPreimage I) (hab : rvUnitTupleValues a.val = rvUnitTupleValues b.val) :
    rvUnitTupleValues (f a).val = rvUnitTupleValues (f b).val :=
  (hval a).trans ((congrArg (fun γ : I => (h γ).val) (Subtype.ext hab)).trans (hval b).symm)

/-- Evaluating the stabilized Gamma morphism on the identity slice
recovers the original contraction, including in nonbijective cases. -/
theorem gammaGroundGammaShear_unit_slice
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)))
    (h : GammaGroundMap I (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m))))
    (hval : ∀ u, rvUnitTupleValues (f u).val = (h (gammaGroundFullPreimageValueMap I u)).val)
    (γ : I) :
    let g := gammaGroundGammaShear I f (gammaGroundRV_value_kernel_of_contraction I f h hval)
    ((gammaGroundSingleFamilyBijection g.bijection).map (gammaGroundGammaUnitSlice I m γ)).val =
      Fin.append γ.val (h γ).val := by
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective (M := M) n γ.val
  have huI : u ∈ (gammaGroundRVUnitGammaPreimage I).carrier := by
    change rvUnitTupleValues u ∈ I.carrier
    exact hu.symm ▸ γ.property
  let a : gammaGroundRVUnitGammaPreimage I := ⟨u,huI⟩
  let p : (gammaGroundRVUnitGammaPreimage I).prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)) :=
    ⟨(u,(1 : Fin m → (CanonicalRV.RVSort M)ˣ)),huI,Set.mem_univ _⟩
  let e := gammaGroundUnitPreimageProductBijection I
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
  have h_one : rvUnitTupleValues (1 : Fin m → (CanonicalRV.RVSort M)ˣ) = 1 := by
    funext j
    exact map_one (rvUnitValueHom (M := M))
  have hp : rvUnitTupleValues (e.map p).val = (gammaGroundGammaUnitSlice I m γ).val := by
    rw [gammaGroundUnitPreimageProductBijection_formula,rvUnitTupleValues_append,hu,gammaGroundGammaUnitSlice_formula,h_one]
    rfl
  have hs : (⟨rvUnitTupleValues (e.map p).val,(e.map p).property⟩ : GammaGroundShearDomain I m) =
      gammaGroundGammaUnitSlice I m γ := Subtype.ext hp
  have hv := gammaGroundGammaShear_at_product I f
    (gammaGroundRV_value_kernel_of_contraction I f h hval) p
  change _ = Fin.append (rvUnitTupleValues u) (rvUnitTupleValues (f a).val * rvUnitTupleValues (1 : Fin m → (CanonicalRV.RVSort M)ˣ)) at hv
  rw [h_one,mul_one,hu,hval a] at hv
  have hγ : gammaGroundFullPreimageValueMap I a = γ := Subtype.ext hu
  rw [hγ] at hv
  exact (congrArg (fun z : GammaGroundShearDomain I m =>
    ((gammaGroundGammaShear I f (gammaGroundRV_value_kernel_of_contraction I f h hval)).bijection.equiv
      ⟨(0 : Fin 1),z⟩).2.val) hs).symm.trans hv

end DiamondIntegral.Section3
