import «section 3».GammaCoproductCuts
import «section 3».FiniteGammaScissors

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

def FiniteGammaObject.coprod (A B : FiniteGammaObject hc S k) : FiniteGammaObject hc S k :=
  ⟨A.obj.coprod B.obj, by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [FiniteFamily.coprod, Fin.addCases_left] using A.property a
    · simpa only [FiniteFamily.coprod, Fin.addCases_right] using B.property b⟩

theorem finiteGammaClass_iso {A B : FiniteGammaObject hc S k} (e : A ≅ B) :
    finiteGammaClass A = finiteGammaClass B := positiveClass_iso (finiteGammaPresentation hc S k) ⟨e⟩

@[simp] theorem finiteGammaClass_empty : finiteGammaClass (FiniteGammaObject.empty hc S k) = 0 :=
  positiveClass_empty (finiteGammaPresentation hc S k)

theorem finiteGammaClass_coprod (A B : FiniteGammaObject hc S k) :
    finiteGammaClass (A.coprod B) = finiteGammaClass A + finiteGammaClass B := by
  let U := A.coprod B
  let X := gammaCoprodLeftCut A.obj B.obj
  have hX : ∀ i, (X i).carrier ⊆ (U.obj.piece i).carrier := gammaCoprodLeftCut_subset A.obj B.obj
  let D := U.restrict X hX
  let E := U.restrict (U.obj.difference X) (fun _ _ h => h.1)
  have hs := positiveClass_scissor (finiteGammaPresentation hc S k)
    (show GammaScissor D.obj E.obj U.obj (FiniteGammaObject.empty hc S k).obj from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change finiteGammaClass D + finiteGammaClass E = finiteGammaClass U + finiteGammaClass (FiniteGammaObject.empty hc S k) at hs
  have hD : finiteGammaClass D = finiteGammaClass A := finiteGammaClass_iso
    ((finiteGammaProperty (hc := hc) (S := S) (k := k)).isoMk (gammaCoprodLeftCutIso A.obj B.obj))
  have hE : finiteGammaClass E = finiteGammaClass B := finiteGammaClass_iso
    ((finiteGammaProperty (hc := hc) (S := S) (k := k)).isoMk (gammaCoprodRightCutIso A.obj B.obj))
  rw [hD, hE, finiteGammaClass_empty, add_zero] at hs
  exact hs.symm

theorem finiteGammaClass_surjective :
    Function.Surjective (finiteGammaClass (M := M) (hc := hc) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (finiteGammaPresentation hc S k)
    FiniteGammaObject.coprod finiteGammaClass_coprod

theorem finiteGammaClass_eq_iff_iso {A B : FiniteGammaObject hc S k} :
    finiteGammaClass A = finiteGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    have he := congrArg finiteGammaToGammaKPlus h
    rw [finiteGammaToGammaKPlus_class, finiteGammaToGammaKPlus_class] at he
    obtain ⟨e⟩ := gammaClass_eq_iff_iso.mp he
    exact ⟨(finiteGammaProperty (hc := hc) (S := S) (k := k)).isoMk e⟩
  · rintro ⟨e⟩
    exact finiteGammaClass_iso e

theorem finiteGammaToGammaKPlus_injective :
    Function.Injective (finiteGammaToGammaKPlus (M := M) (hc := hc) (S := S) (k := k)) := by
  intro a b he
  obtain ⟨A, rfl⟩ := finiteGammaClass_surjective a
  obtain ⟨B, rfl⟩ := finiteGammaClass_surjective b
  rw [finiteGammaToGammaKPlus_class, finiteGammaToGammaKPlus_class] at he
  obtain ⟨e⟩ := gammaClass_eq_iff_iso.mp he
  exact finiteGammaClass_iso ((finiteGammaProperty (hc := hc) (S := S) (k := k)).isoMk e)

end DiamondIntegral.Section3
