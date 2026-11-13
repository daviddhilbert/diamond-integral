import «section 3».GammaGroundBijectionRestrictions
import «section 3».GammaGroundBijectionProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q U V : Space LRV M}
variable {A : GammaGroundDefSet hc B P} {E : GammaGroundDefSet hc B Q}
variable {C : GammaGroundDefSet hc B U} {D : GammaGroundDefSet hc B V}

/-- Source coordinates whose actual RV image lies in a specified target
chart. No old-ground point is chosen to define the transition. -/
def gammaGroundChartTransitionDomain (F : GammaGroundBijection A E)
    (s : GammaGroundMap C A) (t : GammaGroundMap D E) : GammaGroundDefSet hc B U :=
  (F.map.comp s).preimage t.image

theorem gammaGroundChartTransitionDomain_subset (F : GammaGroundBijection A E)
    (s : GammaGroundMap C A) (t : GammaGroundMap D E) :
    (gammaGroundChartTransitionDomain F s t).carrier ⊆ C.carrier :=
  (F.map.comp s).preimage_subset t.image

/-- The partial coordinate expression of an actual RV bijection between
two injectively presented product charts. -/
def gammaGroundChartTransitionMap (F : GammaGroundBijection A E)
    (s : GammaGroundMap C A) (t : GammaGroundMap D E) (ht : Function.Injective t) :
    GammaGroundMap (gammaGroundChartTransitionDomain F s t) D := by
  let e : GammaGroundBijection D t.image := ⟨t.toImage,t.toImage_bijective ht⟩
  let f := (F.map.comp s).restrict (gammaGroundChartTransitionDomain_subset F s t)
  let g : GammaGroundMap (gammaGroundChartTransitionDomain F s t) t.image := f.corestrict (fun x => by
    obtain ⟨c,hcx,hc⟩ := x.property
    have he : (⟨x.val,gammaGroundChartTransitionDomain_subset F s t x.property⟩ : C) = c :=
      Subtype.ext hcx.symm
    change (F.map (s ⟨x.val,gammaGroundChartTransitionDomain_subset F s t x.property⟩)).val ∈ t.image.carrier
    rw [he]
    exact hc)
  exact e.symm.map.comp g

theorem gammaGroundChartTransitionMap_agrees (F : GammaGroundBijection A E)
    (s : GammaGroundMap C A) (t : GammaGroundMap D E) (ht : Function.Injective t)
    (x : gammaGroundChartTransitionDomain F s t) :
    t (gammaGroundChartTransitionMap F s t ht x) =
      F.map (s ⟨x.val,gammaGroundChartTransitionDomain_subset F s t x.property⟩) := by
  have h := t.toImage.apply_inverse (t.toImage_bijective ht)
  have hx := h ⟨(F.map (s ⟨x.val,gammaGroundChartTransitionDomain_subset F s t x.property⟩)).val,
    by
      obtain ⟨c,hcx,hc⟩ := x.property
      have he : (⟨x.val,gammaGroundChartTransitionDomain_subset F s t x.property⟩ : C) = c := Subtype.ext hcx.symm
      rw [he]
      exact hc⟩
  apply Subtype.ext
  exact congrArg (fun z : t.image => z.val) hx

theorem gammaGroundChartTransitionMap_injective (F : GammaGroundBijection A E)
    (s : GammaGroundMap C A) (hs : Function.Injective s)
    (t : GammaGroundMap D E) (ht : Function.Injective t) :
    Function.Injective (gammaGroundChartTransitionMap F s t ht) := by
  intro x y h
  have he := congrArg t h
  rw [gammaGroundChartTransitionMap_agrees,gammaGroundChartTransitionMap_agrees] at he
  have hc := hs (F.bijective.1 he)
  exact Subtype.ext (congrArg (fun z : C => z.val) hc)

/-- A finite target chart cover pulls back to an actual finite cover of
any source chart. The target chart spaces may have different arities. -/
theorem gammaGroundChartTransitionDomain_cover {ι : Type}
    {W : ι → Space LRV M} {D : ∀ i, GammaGroundDefSet hc B (W i)}
    (F : GammaGroundBijection A E) (s : GammaGroundMap C A)
    (t : ∀ i, GammaGroundMap (D i) E)
    (hcover : ∀ b : E, ∃ i, ∃ d : D i, t i d = b) (c : C) :
    ∃ i, c.val ∈ (gammaGroundChartTransitionDomain F s (t i)).carrier := by
  obtain ⟨i,d,hd⟩ := hcover (F.map (s c))
  exact ⟨i,c,rfl,⟨d,congrArg Subtype.val hd⟩⟩
end DiamondIntegral.Section3
