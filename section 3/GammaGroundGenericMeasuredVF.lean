import «section 3».GammaGroundEssentialVFCategory
import «section 3».GammaGroundEssentialVFMeasure
import «section 3».GammaGroundMeasuredVFData

/-! A measured generic-point presentation on actual Gamma-ground VF
objects. GammaGroundPointwiseVFMeasure and GammaGroundMeasuredVFGerms
prove its comparison with pointwise preservation on a definable cofull
subset and with the manuscript's quotient of representatives. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {n : ℕ}

def gammaGroundMeasuredVFWeight (U : GammaGroundMeasuredVFData hc ground n) (a : U.domain) :
    Values.GammaTop (M := M) := (gammaGroundFormValue U.form a).val

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

def GammaGroundGenericMeasuredVFGerm (U V : GammaGroundMeasuredVFData hc ground n) :=
  {e : GammaGroundGeneric U.domain ≃ GammaGroundGeneric V.domain //
    ∃ f : GammaGroundEssentialVFMap U.domain V.domain,
      f.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) ∧
        f.genericEquiv hκ hs hS hv hn = e}

def gammaGroundGenericMeasuredVFGroupoid [CharZero (Section2.VF M)] :
    Groupoid (GammaGroundMeasuredVFData hc ground n) where
  Hom U V := GammaGroundGenericMeasuredVFGerm hκ hs hS hv hn U V
  id U := ⟨Equiv.refl _, by
    refine ⟨GammaGroundEssentialVFMap.id U.domain,
      GammaGroundEssentialVFMap.preservesGeneric_id hκ hs hS hv Values.vfValueHom (gammaGroundMeasuredVFWeight U), ?_⟩
    exact GammaGroundEssentialVFMap.genericEquiv_id hκ hs hS hv hn⟩
  comp {U V W} f g := ⟨f.val.trans g.val, by
    obtain ⟨p, hp, he⟩ := f.property
    obtain ⟨q, hq, hf⟩ := g.property
    refine ⟨GammaGroundEssentialVFMap.comp hκ hs hS hv hn p q,
      GammaGroundEssentialVFMap.preservesGeneric_comp hκ hs hS hv hn Values.vfValueHom
        (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) (gammaGroundMeasuredVFWeight W) p q hp hq, ?_⟩
    exact (GammaGroundEssentialVFMap.genericEquiv_comp hκ hs hS hv hn p q).trans (congrArg₂ Equiv.trans he hf)⟩
  id_comp f := by apply Subtype.ext; exact Equiv.refl_trans f.val
  comp_id f := by apply Subtype.ext; exact Equiv.trans_refl f.val
  assoc f g h := by apply Subtype.ext; exact Equiv.trans_assoc f.val g.val h.val
  inv {U V} f := ⟨f.val.symm, by
    obtain ⟨p, hp, he⟩ := f.property
    refine ⟨p.symm, GammaGroundEssentialVFMap.preservesGeneric_symm hκ hs hS hv Values.vfValueHom
      (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) p hp, ?_⟩
    exact (GammaGroundEssentialVFMap.genericEquiv_symm hκ hs hS hv hn p).trans (congrArg Equiv.symm he)⟩
  inv_comp f := by apply Subtype.ext; exact Equiv.symm_trans_self f.val
  comp_inv f := by apply Subtype.ext; exact Equiv.self_trans_symm f.val

end DiamondIntegral.Section3
