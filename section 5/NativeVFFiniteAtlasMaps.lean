import «section 5».NativeVFFiniteAtlas

/-! Actual original-ground maps on a finite native atlas glue to one
map on its tagged realization. The formula is proved on every chart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {N : ℕ} (A : Fin N → GammaGroundFiniteVFObject hc B)

theorem nativeVFFiniteSumInclusion_injective (i : Fin N) :
    Function.Injective (nativeVFFiniteSumInclusion N A i) := by
  intro a b hab
  rw [nativeVFFiniteSumInclusion_value,nativeVFFiniteSumInclusion_value] at hab
  have he := (nativeVFFiniteSumEquiv N A).injective hab
  exact eq_of_heq (Sigma.mk.inj he).2

theorem nativeVFFiniteSum_chart_partition (a : (nativeVFFiniteSum N A).domain) :
    ∃! i,a.val ∈ (nativeVFFiniteSumInclusion N A i).image.carrier := by
  obtain ⟨⟨i,x⟩,hx⟩ := (nativeVFFiniteSumEquiv N A).surjective a
  refine ⟨i,⟨x,?_⟩,?_⟩
  · exact congrArg Subtype.val ((nativeVFFiniteSumInclusion_value N A i x).trans hx)
  · rintro j ⟨y,hy⟩
    have hej : nativeVFFiniteSumEquiv N A ⟨j,y⟩ = a :=
      (nativeVFFiniteSumInclusion_value N A j y).symm.trans (Subtype.ext hy)
    exact congrArg Sigma.fst ((nativeVFFiniteSumEquiv N A).injective (hej.trans hx.symm))

theorem nativeVFFiniteSum_map {Q : Space LRV M} (D : GammaGroundDefSet hc B Q)
    (f : ∀ i,GammaGroundMap (A i).domain D) :
    ∃ F : GammaGroundMap (nativeVFFiniteSum N A).domain D,
      ∀ i (a : (A i).domain),F (nativeVFFiniteSumInclusion N A i a) = f i a := by
  let c := nativeVFFiniteSumInclusion N A
  have hc (i : Fin N) : Function.Bijective (c i).toImage :=
    (c i).toImage_bijective (nativeVFFiniteSumInclusion_injective A i)
  let g (i : Fin N) : GammaGroundMap (c i).image D := (f i).comp ((c i).toImage.inverse (hc i))
  obtain ⟨F,hF⟩ := gammaGroundMap_of_finite_partition (nativeVFFiniteSum N A).domain D
    (fun i => (c i).image) (by intro i x hx; obtain ⟨a,rfl⟩ := hx; exact (c i a).property) (nativeVFFiniteSum_chart_partition A) g
  refine ⟨F,?_⟩
  intro i a
  have he := hF i (c i a) (show (c i a).val ∈ (c i).image.carrier from ⟨a,rfl⟩)
  change F (c i a) = (f i) (((c i).toImage.inverse (hc i)) ((c i).toImage a)) at he
  exact he.trans (congrArg (f i) ((c i).toImage.inverse_apply (hc i) a))

end DiamondIntegral.Section5
