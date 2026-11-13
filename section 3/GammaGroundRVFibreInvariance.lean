import «section 3».GammaGroundRVFibreDimension
import «section 3».GammaGroundMixedRVAlgebraicity
import «section 3».GammaGroundRVDimension
import «section 3».GammaGroundRealFibres
import Section4.RVFibreDimension
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r : ℕ}
variable {m s : ℕ}
theorem gammaGroundRVFibreDim_le_of_bijective
    (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hS : Cardinal.mk ground.real < κ)
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}
    (f : GammaGroundMap A B) (hf : Function.Bijective f) :
    gammaGroundRVFibreDim A ≤ gammaGroundRVFibreDim B := by
  apply ciSup_le'
  intro a
  apply (gammaGroundRVDim_le_iff_point_rank hex hκ hs hγ
    (small_union_range hκ ground.real hS (vfValues a.val.1))
    (gammaGroundFixedVFFibre A a.val.1) _).mpr
  intro t
  let p : A := ⟨(a.val.1, t.val), t.property⟩
  let q := f p
  have he := gammaGroundMixedBijection_point_rv_rank hex f hf p hκ hγ hS
  change rvTupleRank hc hex (ground.real ∪ Set.range (vfValues a.val.1)) t.val ≤ gammaGroundRVFibreDim B
  rw [← he]
  let u : gammaGroundFixedVFFibre B q.val.1 := ⟨q.val.2, q.property⟩
  exact ((gammaGroundRVDim_le_iff_point_rank hex hκ hs hγ
    (small_union_range hκ ground.real hS (vfValues q.val.1))
    (gammaGroundFixedVFFibre B q.val.1) _).mp le_rfl u).trans
      (le_ciSup (gammaGroundRVFibreDim_bounded B) q)

theorem gammaGroundRVFibreDim_eq_of_bijective
    (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hS : Cardinal.mk ground.real < κ)
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}
    (f : GammaGroundMap A B) (hf : Function.Bijective f) :
    gammaGroundRVFibreDim A = gammaGroundRVFibreDim B :=
  (gammaGroundRVFibreDim_le_of_bijective hex hκ hs hγ hS f hf).antisymm
    (gammaGroundRVFibreDim_le_of_bijective hex hκ hs hγ hS (f.inverse hf)
      (Equiv.ofBijective f hf).symm.bijective)

end DiamondIntegral.Section3
