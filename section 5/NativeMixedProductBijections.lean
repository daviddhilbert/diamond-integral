import «section 3».GammaGroundMixedProducts
import «section 3».GammaGroundBijectionProducts

/-! Actual mixed product bijections retain their full Gamma-ground graphs
and every VF/RV coordinate. Their values are the literal grouped products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {n r m s u v w t : ℕ}

def nativeMixedPackingBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)) :
    GammaGroundBijection (A.prod C) (gammaGroundMixedProductDomain A C) :=
  ⟨(gammaGroundMixedPack A C).toImage,
    (gammaGroundMixedPack A C).toImage_bijective (gammaGroundMixedPack_injective A C)⟩

def nativeMixedProductBijection
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) u v)}
    {E : GammaGroundDefSet hc B (rawMixedSpace (M := M) w t)}
    (f : GammaGroundBijection A D) (g : GammaGroundBijection C E) :
    GammaGroundBijection (gammaGroundMixedProductDomain A C) (gammaGroundMixedProductDomain D E) :=
  (nativeMixedPackingBijection D E).comp ((f.prodMap g).comp (nativeMixedPackingBijection A C).symm)

theorem nativeMixedProductBijection_pack
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) u v)}
    {E : GammaGroundDefSet hc B (rawMixedSpace (M := M) w t)}
    (f : GammaGroundBijection A D) (g : GammaGroundBijection C E) (a : A) (c : C) :
    (nativeMixedProductBijection f g).map
        ((nativeMixedPackingBijection A C).map ⟨(a.val,c.val),a.property,c.property⟩) =
      (nativeMixedPackingBijection D E).map ⟨((f.map a).val,(g.map c).val),(f.map a).property,(g.map c).property⟩ := by
  change (nativeMixedPackingBijection D E).map ((f.prodMap g).map
    (((nativeMixedPackingBijection A C).map.inverse (nativeMixedPackingBijection A C).bijective)
      ((nativeMixedPackingBijection A C).map ⟨(a.val,c.val),a.property,c.property⟩))) = _
  rw [GammaGroundMap.inverse_apply]
  rfl

end DiamondIntegral.Section5
