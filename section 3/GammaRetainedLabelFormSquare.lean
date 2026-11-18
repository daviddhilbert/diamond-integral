import «section 3».GammaGroundVolumeForms

/-! Retained-label density descent commutes with literal RV inclusions.
This applies to both branches of a partial focus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}

theorem gammaRetainedLabel_form_square
    {A D : GammaGroundDefSet hc B (rawRVSpace (M := M) m)}
    {C E : GammaGroundDefSet hc B (rawRVSpace (M := M) (n+m))}
    (j : GammaGroundMap A D) (i : GammaGroundMap C E)
    (f : GammaGroundMap C A) (g : GammaGroundMap E D)
    (hj : ∀ a, (j a).val = a.val) (hi : ∀ c, (i c).val = c.val)
    (hf : ∀ c, (f c).val = c.val ∘ Fin.natAdd n)
    (hg : ∀ e, (g e).val = e.val ∘ Fin.natAdd n)
    (ω : GammaGroundVolumeForm hc B D) : (ω.comp j).comp f = (ω.comp g).comp i := by
  apply GammaGroundMap.ext
  intro c
  change ω (j (f c)) = ω (g (i c))
  congr 1
  apply Subtype.ext
  rw [hj,hf,hg,hi]

end DiamondIntegral.Section3
