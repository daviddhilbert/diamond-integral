import «section 3».RVProductFibreMonomials
import «section 3».RVGenericFibreArity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m k p : ℕ}

/-- At a generic source fibre the target product has at least the source
free arity. Together with a maximal-rank bound this gives equality of
arities before applying the unimodular neighbourhood theorem. -/
theorem gammaGroundRVProduct_generic_fibre_arity_le {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace k))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) (r : R)
    (x : gammaGroundRealPointFibre T ⟨rvUnitValues r.val,Set.mem_range_self _⟩)
    (hxg : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) : m ≤ k := by
  let cr : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
  have hsmallC : Cardinal.mk (adjoinRVUnitTuple B r.val).real < κ :=
    small_union_range hκ B.real hsmall (rvUnitValues r.val)
  have hΓC : Section2.NontrivialDefinableGamma (adjoinRVUnitTuple B r.val) :=
    hΓ.mono Set.subset_union_left Set.Subset.rfl
  have hxC : GammaTupleIndependentOver (adjoinRVUnitTuple B r.val) (rvUnitTupleValues x.val) :=
    (gammaGroundRVUnit_residue_gamma_independent_iff hκ hs h00 hsmall R hR r _).mpr hxg
  exact gammaGroundRVUnitMap_generic_fibre_joint_arity_le hκ hs h00 hsmallC hγsmall hΓC
    (gammaGroundRealPointFibre T cr) (D.monoReal Set.subset_union_left)
    (S.monoReal Set.subset_union_left) hS (f.fibreSource cr) (g.fibreSource cr)
    (gammaGround_fibreSource_joint_injective f g hjoint cr) x hxC
end DiamondIntegral.Section3
