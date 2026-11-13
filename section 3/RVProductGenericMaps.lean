import «section 3».ResidueGenericValueFibres
import «section 3».GammaGroundRealExtensions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m p : ℕ}

/-- On a generic full value fibre in a product chart, the residue output
of an actual definable map is constant after the residue input is fixed. -/
theorem gammaGroundRVProduct_residue_map_generic_fibre {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (S : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (A : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) m).prod (rawRVUnitSpace n)))
    (F : GammaGroundMap A S) (r : R)
    (x y : gammaGroundRealPointFibre A ⟨rvUnitValues r.val,Set.mem_range_self _⟩)
    (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val))
    (hxy : rvUnitTupleValues x.val = rvUnitTupleValues y.val) :
    F.fibreSource ⟨rvUnitValues r.val,Set.mem_range_self _⟩ x =
      F.fibreSource ⟨rvUnitValues r.val,Set.mem_range_self _⟩ y := by
  let C := adjoinRVUnitTuple B r.val
  let c : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
  let T : GammaGroundDefSet hc C (rawRVUnitSpace (M := M) p) := S.monoReal Set.subset_union_left
  have hC : Cardinal.mk C.real < κ := small_union_range hκ B.real hsmall (rvUnitValues r.val)
  have hg : GammaTupleIndependentOver C (rvUnitTupleValues x.val) :=
    (gammaGroundRVUnit_residue_gamma_independent_iff hκ hs h00 hsmall R hR r _).mpr hγ
  exact gammaGroundRVUnitResidueMap_generic_fibre_constant hκ hs h00 hC
    (gammaGroundRealPointFibre A c) T hS (F.fibreSource c) x y hg hxy

/-- The Gamma-valued weight likewise cannot depend on angular choices
inside that generic full fibre, even with the residue input named. -/
theorem gammaGroundRVProduct_gamma_map_generic_fibre {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (A : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) m).prod (rawRVUnitSpace n)))
    (F : GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) (r : R)
    (x y : gammaGroundRealPointFibre A ⟨rvUnitValues r.val,Set.mem_range_self _⟩)
    (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val))
    (hxy : rvUnitTupleValues x.val = rvUnitTupleValues y.val) :
    F.fibreSource ⟨rvUnitValues r.val,Set.mem_range_self _⟩ x =
      F.fibreSource ⟨rvUnitValues r.val,Set.mem_range_self _⟩ y := by
  let C := adjoinRVUnitTuple B r.val
  let c : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
  have hC : Cardinal.mk C.real < κ := small_union_range hκ B.real hsmall (rvUnitValues r.val)
  have hg : GammaTupleIndependentOver C (rvUnitTupleValues x.val) :=
    (gammaGroundRVUnit_residue_gamma_independent_iff hκ hs h00 hsmall R hR r _).mpr hγ
  exact gammaGroundRVUnitGammaMap_generic_fibre_constant hκ hs h00 hC hγsmall
    (gammaGroundRealPointFibre A c) (F.fibreSource c) x y hg hxy
end DiamondIntegral.Section3
