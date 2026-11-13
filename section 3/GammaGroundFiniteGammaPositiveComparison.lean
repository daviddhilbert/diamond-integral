import «section 3».GammaGroundGammaCoproductCuts
import «section 3».GammaGroundFiniteGammaScissors
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundFiniteGammaObject.coprod (A B : GammaGroundFiniteGammaObject hc ground k) : GammaGroundFiniteGammaObject hc ground k :=
  ⟨A.obj.coprod B.obj, by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using A.property a
    · simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using B.property b⟩

theorem gammaGroundFiniteGammaClass_iso {A B : GammaGroundFiniteGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundFiniteGammaClass A = gammaGroundFiniteGammaClass B := positiveClass_iso (gammaGroundFiniteGammaPresentation hc ground k) ⟨e⟩

@[simp] theorem gammaGroundFiniteGammaClass_empty : gammaGroundFiniteGammaClass (GammaGroundFiniteGammaObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundFiniteGammaPresentation hc ground k)

theorem gammaGroundFiniteGammaClass_coprod (A B : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaClass (A.coprod B) = gammaGroundFiniteGammaClass A + gammaGroundFiniteGammaClass B := by
  let U := A.coprod B
  let X := gammaGroundGammaCoprodLeftCut A.obj B.obj
  have hX : ∀ i, (X i).carrier ⊆ (U.obj.piece i).carrier := gammaGroundGammaCoprodLeftCut_subset A.obj B.obj
  let D := U.restrict X hX
  let E := U.restrict (U.obj.difference X) (fun _ _ h => h.1)
  have hs := positiveClass_scissor (gammaGroundFiniteGammaPresentation hc ground k)
    (show GammaGroundGammaScissor D.obj E.obj U.obj (GammaGroundFiniteGammaObject.empty hc ground k).obj from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change gammaGroundFiniteGammaClass D + gammaGroundFiniteGammaClass E = gammaGroundFiniteGammaClass U + gammaGroundFiniteGammaClass (GammaGroundFiniteGammaObject.empty hc ground k) at hs
  have hD : gammaGroundFiniteGammaClass D = gammaGroundFiniteGammaClass A := gammaGroundFiniteGammaClass_iso
    ((gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk (gammaGroundGammaCoprodLeftCutIso A.obj B.obj))
  have hE : gammaGroundFiniteGammaClass E = gammaGroundFiniteGammaClass B := gammaGroundFiniteGammaClass_iso
    ((gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk (gammaGroundGammaCoprodRightCutIso A.obj B.obj))
  rw [hD, hE, gammaGroundFiniteGammaClass_empty, add_zero] at hs
  exact hs.symm

theorem gammaGroundFiniteGammaClass_surjective :
    Function.Surjective (gammaGroundFiniteGammaClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundFiniteGammaPresentation hc ground k)
    GammaGroundFiniteGammaObject.coprod gammaGroundFiniteGammaClass_coprod

theorem gammaGroundFiniteGammaClass_eq_iff_iso {A B : GammaGroundFiniteGammaObject hc ground k} :
    gammaGroundFiniteGammaClass A = gammaGroundFiniteGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    have he := congrArg gammaGroundFiniteGammaToGammaKPlus h
    rw [gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundFiniteGammaToGammaKPlus_class] at he
    obtain ⟨e⟩ := gammaGroundGammaClass_eq_iff_iso.mp he
    exact ⟨(gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk e⟩
  · rintro ⟨e⟩
    exact gammaGroundFiniteGammaClass_iso e

theorem gammaGroundFiniteGammaToGammaKPlus_injective :
    Function.Injective (gammaGroundFiniteGammaToGammaKPlus (M := M) (hc := hc) (ground := ground) (k := k)) := by
  intro a b he
  obtain ⟨A, rfl⟩ := gammaGroundFiniteGammaClass_surjective a
  obtain ⟨B, rfl⟩ := gammaGroundFiniteGammaClass_surjective b
  rw [gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundFiniteGammaToGammaKPlus_class] at he
  obtain ⟨e⟩ := gammaGroundGammaClass_eq_iff_iso.mp he
  exact gammaGroundFiniteGammaClass_iso ((gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk e)

end DiamondIntegral.Section3
