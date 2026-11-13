import «section 3».GammaGroundVFDimension
import «section 3».GammaGroundMapRealization
import «section 3».GammaGroundBijections
import «section 3».GammaGroundMapImages
import Section4.VFCategories

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
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {n r m s : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}

theorem gammaGroundVFDimension_le_of_finiteMap (f : GammaGroundMap A B) (hf : f.FiniteFibres)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Section2.vfDimension A.carrier ≤ Section2.vfDimension B.carrier := by
  by_cases hA : A.carrier.Nonempty
  · obtain ⟨T, hT, hsmall, hfield, hDA, hDB, hgraph⟩ := f.realize hκ hS
    let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hDA⟩
    let DB : DefSet (rawMixedSpace (M := M) m s) T := ⟨B.carrier, hDB⟩
    let F : Map DA DB := ⟨f.toFun, (relationDefinable_iff_product _).mpr hgraph⟩
    have hB : B.carrier.Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨(f ⟨a, ha⟩).val, (f ⟨a, ha⟩).property⟩
    rw [vfDimension_eq_companion hc hs hsmall hv DA hA,
      vfDimension_eq_companion hc hs hsmall hv DB hB]
    exact_mod_cast vfDim_le_of_finite_map (rawRVSpace 1) F hf
  · rw [Set.not_nonempty_iff_eq_empty.mp hA, Section2.vfDimension_empty]
    exact bot_le

theorem gammaGroundVFDimension_eq_of_bijection (f : GammaGroundBijection A B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Section2.vfDimension A.carrier = Section2.vfDimension B.carrier :=
  (gammaGroundVFDimension_le_of_finiteMap f.map
    (GammaGroundMap.finiteFibres_of_injective f.bijective.injective) hκ hs hS hv).antisymm
      (gammaGroundVFDimension_le_of_finiteMap f.symm.map
        (GammaGroundMap.finiteFibres_of_injective f.symm.bijective.injective) hκ hs hS hv)

end DiamondIntegral.Section3
