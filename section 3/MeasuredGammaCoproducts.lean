import «section 3».GammaCoproductCuts
import «section 3».GammaVolumeCategories

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem gammaFormValue_transport {P : Space LRV M} {A B : DefSet P S}
    (h : A = B) (ω : GammaVolumeForm hc A) (b : B) :
    gammaFormValue (cast (congrArg (fun D => GammaVolumeForm hc D) h) ω) b =
      gammaFormValue ω ⟨b.val, h.symm ▸ b.property⟩ := by
  subst B
  rfl

@[reducible] def MeasuredGammaObject.coprod (A B : MeasuredGammaObject hc S k) : MeasuredGammaObject hc S k where
  underlying := A.underlying.coprod B.underlying
  form := Fin.addCases (motive := fun i => GammaVolumeForm hc ((A.underlying.coprod B.underlying).piece i))
    (fun a => by simpa only [FiniteFamily.coprod, Fin.addCases_left] using A.form a)
    (fun b => by simpa only [FiniteFamily.coprod, Fin.addCases_right] using B.form b)

theorem measuredGammaCoprod_combined_left (A B : MeasuredGammaObject hc S k)
    (a : A.underlying.Carrier) :
    (A.coprod B).combinedWeight (familyCoprodInl A.underlying B.underlying a) = A.combinedWeight a := by
  rcases a with ⟨i, a⟩
  simp only [MeasuredGammaObject.combinedWeight, MeasuredGammaObject.weight,
    MeasuredGammaObject.coprod, familyCoprodInl, Fin.addCases_left,
    GammaObject.coordinates]
  congr 1
  exact gammaFormValue_transport
    (Fin.addCases_left (motive := fun _ => _) (left := A.underlying.piece) (right := B.underlying.piece) i).symm _ _

theorem measuredGammaCoprod_combined_right (A B : MeasuredGammaObject hc S k)
    (b : B.underlying.Carrier) :
    (A.coprod B).combinedWeight (familyCoprodInr A.underlying B.underlying b) = B.combinedWeight b := by
  rcases b with ⟨j, b⟩
  simp only [MeasuredGammaObject.combinedWeight, MeasuredGammaObject.weight,
    MeasuredGammaObject.coprod, familyCoprodInr, Fin.addCases_right,
    GammaObject.coordinates]
  congr 1
  exact gammaFormValue_transport
    (Fin.addCases_right (motive := fun _ => _) (left := A.underlying.piece) (right := B.underlying.piece) j).symm _ _

end DiamondIntegral.Section3
