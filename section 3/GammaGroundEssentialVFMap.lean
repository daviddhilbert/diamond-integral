import «section 3».GammaGroundGenericGeometry
import «section 3».GammaGroundMapRealization
import «section 3».GammaGroundMapPreimages

/-! Essential VF representatives over Gamma ground parameters retain
actual partial bijections and the manuscript's intrinsic dimension. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r s : ℕ}

section Data
variable [TopologicalSpace (Section2.VF M)]
structure GammaGroundEssentialVFMap
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)) where
  source : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)
  target : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)
  source_subset : source.carrier ⊆ A.carrier
  target_subset : target.carrier ⊆ B.carrier
  source_small : Section2.vfDimension (A.sdiff source).carrier < (n : WithBot ℕ)
  target_small : Section2.vfDimension (B.sdiff target).carrier < (n : WithBot ℕ)
  map : GammaGroundMap source target
  bijective : Function.Bijective map

def GammaGroundEssentialVFMap.id
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) : GammaGroundEssentialVFMap A A := by
  have h : (A.sdiff A).carrier = ∅ := Set.sdiff_self
  have hd : Section2.vfDimension (A.sdiff A).carrier < (n : WithBot ℕ) := by
    rw [h, Section2.vfDimension_empty]
    exact WithBot.bot_lt_coe n
  exact ⟨A, A, fun _ h => h, fun _ h => h, hd, hd, GammaGroundMap.id A, Function.bijective_id⟩

def GammaGroundEssentialVFMap.symm
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
    (f : GammaGroundEssentialVFMap A B) : GammaGroundEssentialVFMap B A :=
  ⟨f.target, f.source, f.target_subset, f.source_subset, f.target_small, f.source_small,
    f.map.inverse f.bijective, (Equiv.ofBijective f.map f.bijective).symm.bijective⟩
end Data

theorem gammaGround_independent_map
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
    (f : GammaGroundMap A B) (hf : f.FiniteFibres)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk ground.real < κ)
    (a : A) (ha : AlgebraicIndependent (vfParameterField ground.real) a.val.1) :
    AlgebraicIndependent (vfParameterField ground.real) (f a).val.1 := by
  obtain ⟨T, hT, hsmall, hfield, hDA, hDB, hgraph⟩ := f.realize hκ hS
  let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hDA⟩
  let DB : DefSet (rawMixedSpace (M := M) n s) T := ⟨B.carrier, hDB⟩
  let F : Map DA DB := ⟨f.toFun, (relationDefinable_iff_product _).mpr hgraph⟩
  have haT : AlgebraicIndependent (vfParameterField T) a.val.1 := by rwa [hfield]
  have h := independent_map_of_finiteFibres hc F hf a haT
  rwa [hfield] at h

namespace GammaGroundEssentialVFMap
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

def genericFun (f : GammaGroundEssentialVFMap A B) (a : GammaGroundGeneric A) : GammaGroundGeneric B := by
  let p : f.source := ⟨a.val.val,
    gammaGround_mem_of_small_complement f.source hκ hs hS hv hn f.source_small a⟩
  exact ⟨⟨(f.map p).val, f.target_subset (f.map p).property⟩,
    gammaGround_independent_map f.map (GammaGroundMap.finiteFibres_of_injective f.bijective.injective)
      hκ hS p a.property⟩

def genericEquiv (f : GammaGroundEssentialVFMap A B) : GammaGroundGeneric A ≃ GammaGroundGeneric B where
  toFun := f.genericFun hκ hs hS hv hn
  invFun := f.symm.genericFun hκ hs hS hv hn
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    change (f.map.inverse f.bijective (f.map _)).val = _
    rw [GammaGroundMap.inverse_apply]
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    change (f.map (f.map.inverse f.bijective _)).val = _
    rw [GammaGroundMap.apply_inverse]

end GammaGroundEssentialVFMap
end DiamondIntegral.Section3
