import «section 3».GammaGroundMapRealization
import «section 3».GammaGroundBijections
import «section 3».RVFibreDimension

/-! Finiteness of the actual RV fibres is invariant under Gamma-ground
bijections. This conclusion does not identify RV ranks after arbitrary
real parameter expansions. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r m s : ℕ}

theorem gammaGroundFiniteRVFibres_iff
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}
    (f : GammaGroundBijection A B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk ground.real < κ) :
    (∀ a : Fin n → Section2.VF M, {t | (a, t) ∈ A.carrier}.Finite) ↔
      (∀ b : Fin m → Section2.VF M, {t | (b, t) ∈ B.carrier}.Finite) := by
  obtain ⟨T, hT, hsmall, hfield, hDA, hDB, hgraph⟩ := f.map.realize hκ hS
  let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hDA⟩
  let DB : DefSet (rawMixedSpace (M := M) m s) T := ⟨B.carrier, hDB⟩
  let F : Map DA DB := ⟨f.map.toFun, (relationDefinable_iff_product _).mpr hgraph⟩
  have hd := SpecialTransformations.Section4.lemma_4_13 hc
    (rvExchangeInput_of_earlier hκ hs h00) hκ hs hsmall F f.bijective
  exact (rvFibreDim_eq_zero_iff_finite_fibres DA).symm.trans
    ((by rw [hd] : rvFibreDim DA = 0 ↔ rvFibreDim DB = 0).trans
      (rvFibreDim_eq_zero_iff_finite_fibres DB))

end DiamondIntegral.Section3
