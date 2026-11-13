import «section 3».GammaGenericValueFibres
import «section 3».ResidueGammaGenericity
import «section 3».GammaGroundRealFibres
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- Full generic value fibres remain indivisible after naming a point
from any original-ground finite-value-support residue set. -/
theorem gammaGroundRVUnit_generic_fibre_over_residue {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite) (r : R)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) m).prod (rawRVUnitSpace n)))
    (x y : Fin m → (CanonicalRV.RVSort M)ˣ) (hx : (x,r.val) ∈ T.carrier)
    (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x))
    (hxy : rvUnitTupleValues x = rvUnitTupleValues y) : (y,r.val) ∈ T.carrier := by
  let C := adjoinRVUnitTuple B r.val
  let c : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
  let A : GammaGroundDefSet hc C (rawRVUnitSpace (M := M) m) :=
    ⟨{z | (z,r.val) ∈ T.carrier},by
      simpa only [c,C,adjoinRVUnitTuple,decode_rvUnitValues] using T.definable.fibreRealPoint c⟩
  have hC : Cardinal.mk C.real < κ := small_union_range hκ B.real hsmall (rvUnitValues r.val)
  have hg : GammaTupleIndependentOver C (rvUnitTupleValues x) :=
    (gammaGroundRVUnit_residue_gamma_independent_iff hκ hs h00 hsmall R hR r _).mpr hγ
  exact gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hC A ⟨x,hx⟩ hg y hxy

/-- A definable map into a residue set is constant on every full
Gamma-generic value fibre in its source. -/
theorem gammaGroundRVUnitResidueMap_generic_fibre_constant {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m))
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite) (F : GammaGroundMap A R) (x y : A)
    (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val))
    (hxy : rvUnitTupleValues x.val = rvUnitTupleValues y.val) : F x = F y := by
  let T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) m).prod (rawRVUnitSpace n)) :=
    ⟨{z | ∃ a : A, a.val = z.1 ∧ (F a).val = z.2},F.graph_definable⟩
  have hy := gammaGroundRVUnit_generic_fibre_over_residue hκ hs h00 hsmall R hR (F x) T x.val y.val
    ⟨x,rfl,rfl⟩ hγ hxy
  obtain ⟨a,ha,he⟩ := hy
  have hay : a = y := Subtype.ext ha
  subst a
  exact (Subtype.ext he).symm
end DiamondIntegral.Section3
