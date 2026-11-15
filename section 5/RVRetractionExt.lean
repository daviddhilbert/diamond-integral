import «section 4».Section3T001Integration

/-! Retractions on the actual ordinary RV ring are determined by their
values on actual RES objects and full Gamma RV preimages. The tensor
presentation used here is the proved Section 3 presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
open scoped TensorProduct
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {R : Type} [CommRing R]

theorem rvOrdinaryRetraction_ext (p : ApprovedT001Presentation.Ordinary B)
    (f g : RVOrdinaryRing.Ring B →+* R)
    (hres : ∀ x : RESOrdinaryRing.Ring B,f (RVOrdinaryMaps.ofRES B x) = g (RVOrdinaryMaps.ofRES B x))
    (hgamma : ∀ n (a : GammaOrdinaryCharts.Chart B n),
      f (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a)) =
        g (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a))) : f = g := by
  have hg : f.comp (GammaOrdinarySharpRingMap.sharp B) = g.comp (GammaOrdinarySharpRingMap.sharp B) :=
    GammaOrdinaryRing.hom_ext B _ _ hgamma
  ext x
  obtain ⟨t,rfl⟩ := p.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [RVOrdinaryBalancedTensor.comparison_tmul,map_mul,map_mul,hres]
    exact congrArg (fun z => g (RVOrdinaryMaps.ofRES B x)*z) (RingHom.congr_fun hg y)
  | add x y hx hy =>
    rw [map_add,map_add,map_add,hx,hy]

end DiamondIntegral.Section5
