import «section 3».MeasuredGammaRepresentatives
import «section 3».MeasuredFiniteGammaScissors

/-! Actual finite Gamma representatives and injectivity of the inclusion
in the genuine fixed-degree Gamma positive classes. -/
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

def MeasuredFiniteGammaObject.coprod (A B : MeasuredFiniteGammaObject hc S k) : MeasuredFiniteGammaObject hc S k :=
  ⟨A.obj.coprod B.obj, by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [MeasuredGammaObject.coprod, FiniteFamily.coprod, Fin.addCases_left] using A.property a
    · simpa only [MeasuredGammaObject.coprod, FiniteFamily.coprod, Fin.addCases_right] using B.property b⟩

def MeasuredFiniteGammaObject.restrict (A : MeasuredFiniteGammaObject hc S k)
    (X : Fin A.obj.underlying.tags → DefSet ((volumeGammaSpace hc).power (Fin k)) S)
    (hX : ∀ i, (X i).carrier ⊆ (A.obj.underlying.piece i).carrier) : MeasuredFiniteGammaObject hc S k :=
  ⟨A.obj.restrict X hX, fun i => (A.property i).subset (hX i)⟩

theorem measuredFiniteGammaClass_iso {A B : MeasuredFiniteGammaObject hc S k} (e : A ≅ B) :
    measuredFiniteGammaClass A = measuredFiniteGammaClass B := positiveClass_iso (measuredFiniteGammaPresentation hc S k) ⟨e⟩

@[simp] theorem measuredFiniteGammaClass_empty : measuredFiniteGammaClass (MeasuredFiniteGammaObject.empty hc S k) = 0 :=
  positiveClass_empty (measuredFiniteGammaPresentation hc S k)

theorem measuredFiniteGammaClass_coprod (A B : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaClass (A.coprod B) = measuredFiniteGammaClass A + measuredFiniteGammaClass B := by
  let U := A.coprod B
  let X := gammaCoprodLeftCut A.obj.underlying B.obj.underlying
  have hX : ∀ i, (X i).carrier ⊆ (U.obj.underlying.piece i).carrier := gammaCoprodLeftCut_subset A.obj.underlying B.obj.underlying
  let D := U.restrict X hX
  let E := U.restrict (U.obj.underlying.difference X) (fun _ _ h => h.1)
  have hs := positiveClass_scissor (measuredFiniteGammaPresentation hc S k)
    (show MeasuredGammaScissor D.obj E.obj U.obj (MeasuredFiniteGammaObject.empty hc S k).obj from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change measuredFiniteGammaClass D + measuredFiniteGammaClass E = measuredFiniteGammaClass U + measuredFiniteGammaClass (MeasuredFiniteGammaObject.empty hc S k) at hs
  have hD : measuredFiniteGammaClass D = measuredFiniteGammaClass A := measuredFiniteGammaClass_iso
    ((measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).isoMk (asIso (show _ ⟶ _ from measuredGammaCoprodLeftCutHom A.obj B.obj)))
  have hE : measuredFiniteGammaClass E = measuredFiniteGammaClass B := measuredFiniteGammaClass_iso
    ((measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).isoMk (asIso (show _ ⟶ _ from measuredGammaCoprodRightCutHom A.obj B.obj)))
  rw [hD, hE, measuredFiniteGammaClass_empty, add_zero] at hs
  exact hs.symm

theorem measuredFiniteGammaClass_surjective :
    Function.Surjective (measuredFiniteGammaClass (M := M) (hc := hc) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (measuredFiniteGammaPresentation hc S k)
    MeasuredFiniteGammaObject.coprod measuredFiniteGammaClass_coprod

theorem measuredFiniteGammaClass_eq_iff_iso {A B : MeasuredFiniteGammaObject hc S k} :
    measuredFiniteGammaClass A = measuredFiniteGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    have he := congrArg measuredFiniteGammaToGammaKPlus h
    rw [measuredFiniteGammaToGammaKPlus_class, measuredFiniteGammaToGammaKPlus_class] at he
    obtain ⟨e⟩ := measuredGammaClass_eq_iff_iso.mp he
    exact ⟨(measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).isoMk e⟩
  · rintro ⟨e⟩
    exact measuredFiniteGammaClass_iso e

theorem measuredFiniteGammaToGammaKPlus_injective :
    Function.Injective (measuredFiniteGammaToGammaKPlus (M := M) (hc := hc) (S := S) (k := k)) := by
  intro a b he
  obtain ⟨A, rfl⟩ := measuredFiniteGammaClass_surjective a
  obtain ⟨B, rfl⟩ := measuredFiniteGammaClass_surjective b
  rw [measuredFiniteGammaToGammaKPlus_class, measuredFiniteGammaToGammaKPlus_class] at he
  obtain ⟨e⟩ := measuredGammaClass_eq_iff_iso.mp he
  exact measuredFiniteGammaClass_iso ((measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).isoMk e)

end DiamondIntegral.Section3
