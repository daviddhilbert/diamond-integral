import «section 3».GammaGroundMeasuredGammaRepresentatives
import «section 3».GammaGroundMeasuredFiniteGammaScissors
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

def GammaGroundMeasuredFiniteGammaObject.coprod (A B : GammaGroundMeasuredFiniteGammaObject hc ground k) : GammaGroundMeasuredFiniteGammaObject hc ground k :=
  ⟨A.obj.coprod B.obj, by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [GammaGroundMeasuredGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_left] using A.property a
    · simpa only [GammaGroundMeasuredGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_right] using B.property b⟩

def GammaGroundMeasuredFiniteGammaObject.restrict (A : GammaGroundMeasuredFiniteGammaObject hc ground k)
    (X : Fin A.obj.underlying.tags → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)))
    (hX : ∀ i, (X i).carrier ⊆ (A.obj.underlying.piece i).carrier) : GammaGroundMeasuredFiniteGammaObject hc ground k :=
  ⟨A.obj.restrict X hX, fun i => (A.property i).subset (hX i)⟩

theorem gammaGroundMeasuredFiniteGammaClass_iso {A B : GammaGroundMeasuredFiniteGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundMeasuredFiniteGammaClass A = gammaGroundMeasuredFiniteGammaClass B := positiveClass_iso (gammaGroundMeasuredFiniteGammaPresentation hc ground k) ⟨e⟩

@[simp] theorem gammaGroundMeasuredFiniteGammaClass_empty : gammaGroundMeasuredFiniteGammaClass (GammaGroundMeasuredFiniteGammaObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundMeasuredFiniteGammaPresentation hc ground k)

theorem gammaGroundMeasuredFiniteGammaClass_coprod (A B : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaClass (A.coprod B) = gammaGroundMeasuredFiniteGammaClass A + gammaGroundMeasuredFiniteGammaClass B := by
  let U := A.coprod B
  let X := gammaGroundGammaCoprodLeftCut A.obj.underlying B.obj.underlying
  have hX : ∀ i, (X i).carrier ⊆ (U.obj.underlying.piece i).carrier := gammaGroundGammaCoprodLeftCut_subset A.obj.underlying B.obj.underlying
  let D := U.restrict X hX
  let E := U.restrict (U.obj.underlying.difference X) (fun _ _ h => h.1)
  have hs := positiveClass_scissor (gammaGroundMeasuredFiniteGammaPresentation hc ground k)
    (show GammaGroundMeasuredGammaScissor D.obj E.obj U.obj (GammaGroundMeasuredFiniteGammaObject.empty hc ground k).obj from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change gammaGroundMeasuredFiniteGammaClass D + gammaGroundMeasuredFiniteGammaClass E = gammaGroundMeasuredFiniteGammaClass U + gammaGroundMeasuredFiniteGammaClass (GammaGroundMeasuredFiniteGammaObject.empty hc ground k) at hs
  have hD : gammaGroundMeasuredFiniteGammaClass D = gammaGroundMeasuredFiniteGammaClass A := gammaGroundMeasuredFiniteGammaClass_iso
    ((gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodLeftCutHom A.obj B.obj)))
  have hE : gammaGroundMeasuredFiniteGammaClass E = gammaGroundMeasuredFiniteGammaClass B := gammaGroundMeasuredFiniteGammaClass_iso
    ((gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodRightCutHom A.obj B.obj)))
  rw [hD, hE, gammaGroundMeasuredFiniteGammaClass_empty, add_zero] at hs
  exact hs.symm

theorem gammaGroundMeasuredFiniteGammaClass_surjective :
    Function.Surjective (gammaGroundMeasuredFiniteGammaClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundMeasuredFiniteGammaPresentation hc ground k)
    GammaGroundMeasuredFiniteGammaObject.coprod gammaGroundMeasuredFiniteGammaClass_coprod

theorem gammaGroundMeasuredFiniteGammaClass_eq_iff_iso {A B : GammaGroundMeasuredFiniteGammaObject hc ground k} :
    gammaGroundMeasuredFiniteGammaClass A = gammaGroundMeasuredFiniteGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    have he := congrArg gammaGroundMeasuredFiniteGammaToGammaKPlus h
    rw [gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredFiniteGammaToGammaKPlus_class] at he
    obtain ⟨e⟩ := gammaGroundMeasuredGammaClass_eq_iff_iso.mp he
    exact ⟨(gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk e⟩
  · rintro ⟨e⟩
    exact gammaGroundMeasuredFiniteGammaClass_iso e

theorem gammaGroundMeasuredFiniteGammaToGammaKPlus_injective :
    Function.Injective (gammaGroundMeasuredFiniteGammaToGammaKPlus (M := M) (hc := hc) (ground := ground) (k := k)) := by
  intro a b he
  obtain ⟨A, rfl⟩ := gammaGroundMeasuredFiniteGammaClass_surjective a
  obtain ⟨B, rfl⟩ := gammaGroundMeasuredFiniteGammaClass_surjective b
  rw [gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredFiniteGammaToGammaKPlus_class] at he
  obtain ⟨e⟩ := gammaGroundMeasuredGammaClass_eq_iff_iso.mp he
  exact gammaGroundMeasuredFiniteGammaClass_iso ((gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).isoMk e)

end DiamondIntegral.Section3
