import «section 3».GammaGroundGammaCoproducts
import «section 3».GammaGroundGammaVolumeCategories
/-! Genuine tagged disjoint unions retain each original Gamma form. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundFormValue_transport {P : Space LRV M} {A B : GammaGroundDefSet hc ground P}
    (h : A = B) (ω : GammaGroundVolumeForm hc ground A) (b : B) :
    gammaGroundFormValue (cast (congrArg (fun D => GammaGroundVolumeForm hc ground D) h) ω) b =
      gammaGroundFormValue ω ⟨b.val, h.symm ▸ b.property⟩ := by
  subst B
  rfl

@[reducible] def GammaGroundMeasuredGammaObject.coprod (A B : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundMeasuredGammaObject hc ground k where
  underlying := A.underlying.coprod B.underlying
  form := Fin.addCases (motive := fun i => GammaGroundVolumeForm hc ground ((A.underlying.coprod B.underlying).piece i))
    (fun a => by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using A.form a)
    (fun b => by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using B.form b)

theorem gammaGroundMeasuredGammaCoprod_combined_left (A B : GammaGroundMeasuredGammaObject hc ground k)
    (a : A.underlying.Carrier) :
    (A.coprod B).combinedWeight (gammaGroundFamilyCoprodInl A.underlying B.underlying a) = A.combinedWeight a := by
  rcases a with ⟨i, a⟩
  simp only [GammaGroundMeasuredGammaObject.combinedWeight, GammaGroundMeasuredGammaObject.weight,
    GammaGroundMeasuredGammaObject.coprod, gammaGroundFamilyCoprodInl, Fin.addCases_left,
    GammaGroundGammaObject.coordinates]
  congr 1
  exact gammaGroundFormValue_transport
    (Fin.addCases_left (motive := fun _ => _) (left := A.underlying.piece) (right := B.underlying.piece) i).symm _ _

theorem gammaGroundMeasuredGammaCoprod_combined_right (A B : GammaGroundMeasuredGammaObject hc ground k)
    (b : B.underlying.Carrier) :
    (A.coprod B).combinedWeight (gammaGroundFamilyCoprodInr A.underlying B.underlying b) = B.combinedWeight b := by
  rcases b with ⟨j, b⟩
  simp only [GammaGroundMeasuredGammaObject.combinedWeight, GammaGroundMeasuredGammaObject.weight,
    GammaGroundMeasuredGammaObject.coprod, gammaGroundFamilyCoprodInr, Fin.addCases_right,
    GammaGroundGammaObject.coordinates]
  congr 1
  exact gammaGroundFormValue_transport
    (Fin.addCases_right (motive := fun _ => _) (left := A.underlying.piece) (right := B.underlying.piece) j).symm _ _

end DiamondIntegral.Section3
