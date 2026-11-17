import «section 3».GammaEssentialMeasuredProducts
import «section 3».GammaMeasuredArrowLift

/-! The actual measured VF groupoids respect Cartesian products in all
degrees. Zero-degree generic representatives are converted back to full
form-preserving bijections, so no points are discarded there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaMeasuredHom_generic_representative {n : ℕ} {U V : GammaGroundMeasuredVFData hc B n}
    (f : GammaGroundMeasuredVFHom hκ hs hr hv U V) :
    ∃ r : GammaGroundEssentialVFMap U.domain V.domain,
      r.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) := by
  cases n with
  | zero =>
    refine ⟨gammaEssentialOfBijection f.bijection,?_⟩
    intro p _
    refine ⟨1,hasMixedVFJacobianAt_zero_arity f.bijection.map p,?_⟩
    rw [map_one,mul_one]
    exact congrArg Subtype.val (f.preserves p)
  | succ n =>
    obtain ⟨r,_⟩ := f.property
    exact ⟨r.val,r.property.toGeneric⟩

def gammaMeasuredHomOfGenericEssential {n : ℕ} {U V : GammaGroundMeasuredVFData hc B n}
    (f : GammaGroundEssentialVFMap U.domain V.domain)
    (hf : f.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V)) :
    GammaGroundMeasuredVFHom hκ hs hr hv U V := by
  cases n with
  | zero =>
    have hS : f.source.carrier = U.domain.carrier := Set.Subset.antisymm f.source_subset
      (Set.sdiff_eq_empty.mp ((vf_small_zero_iff_empty _).mp f.source_small))
    have hT : f.target.carrier = V.domain.carrier := Set.Subset.antisymm f.target_subset
      (Set.sdiff_eq_empty.mp ((vf_small_zero_iff_empty _).mp f.target_small))
    let a : GammaGroundBijection U.domain f.source := GammaGroundBijection.ofCarrierEq hS.symm
    let b : GammaGroundBijection f.target V.domain := GammaGroundBijection.ofCarrierEq hT
    let e := b.comp ((⟨f.map,f.bijective⟩ : GammaGroundBijection f.source f.target).comp a)
    refine ⟨e,?_⟩
    intro p
    obtain ⟨J,hJ,hw⟩ := hf (a.map p) algebraicIndependent_empty_type
    have hOne : J=1 := hJ.unique (hasMixedVFJacobianAt_zero_arity f.map (a.map p))
    rw [hOne,map_one,mul_one] at hw
    exact Subtype.ext hw
  | succ n =>
    exact (gammaGroundMeasuredGermEquivGeneric hκ hs hr hv (Nat.succ_pos n) U V).symm
      ⟨f.genericEquiv hκ hs hr hv (Nat.succ_pos n),f,hf,rfl⟩

def gammaMeasuredVFProductHom {n m : ℕ}
    {U U' : GammaGroundMeasuredVFData hc B n} {V V' : GammaGroundMeasuredVFData hc B m}
    (f : GammaGroundMeasuredVFHom hκ hs hr hv U U') (g : GammaGroundMeasuredVFHom hκ hs hr hv V V') :
    GammaGroundMeasuredVFHom hκ hs hr hv (U.product V) (U'.product V') := by
  let R := gammaMeasuredHom_generic_representative hκ hs hr hv f
  let S := gammaMeasuredHom_generic_representative hκ hs hr hv g
  let r := R.choose
  let s := S.choose
  exact gammaMeasuredHomOfGenericEssential hκ hs hr hv (r.product hκ hs hr hv s)
    (gammaEssential_product_preserves hκ hs hr hv r s R.choose_spec S.choose_spec)

end DiamondIntegral.Section3
