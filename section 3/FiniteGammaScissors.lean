import «section 3».GammaRESLift
import «section 3».GammaRVScissors
import «section 3».RESCoproducts

/-! Fixed-degree finite Gamma scissors and the actual commutative square
of positive additive maps to Gamma, RES and RV. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def FiniteGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    FiniteGammaObject hc S k := ⟨GammaObject.empty hc S k, fun i => i.elim0⟩

def FiniteGammaObject.restrict (A : FiniteGammaObject hc S k)
    (X : Fin A.obj.tags → GammaPiece hc S k)
    (hX : ∀ i, (X i).carrier ⊆ (A.obj.piece i).carrier) : FiniteGammaObject hc S k :=
  ⟨A.obj.restrict X, fun i => (A.property i).subset (hX i)⟩

def finiteGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    ScissorPresentation (FiniteGammaObject (M := M) hc S k) where
  iso A B := Nonempty (A ≅ B)
  empty := FiniteGammaObject.empty hc S k
  scissor A B D E := GammaScissor A.obj B.obj D.obj E.obj

abbrev FiniteGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KPlus (finiteGammaPresentation hc S k)

def finiteGammaClass (A : FiniteGammaObject hc S k) : FiniteGammaKPlus hc S k :=
  positiveClass (finiteGammaPresentation hc S k) A

def finiteGammaToGammaKPlus : FiniteGammaKPlus hc S k →+ GammaKPlus hc S k :=
  PositiveAdditiveGrothendieck.lift (finiteGammaPresentation hc S k) {
    toFun A := gammaClass A.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact gammaClass_iso ((finiteGammaProperty (hc := hc) (S := S) (k := k)).ι.mapIso e)
    empty := gammaClass_empty
    scissor := fun h => positiveClass_scissor (gammaPresentation hc S k) h }

@[simp] theorem finiteGammaToGammaKPlus_class (A : FiniteGammaObject hc S k) :
    finiteGammaToGammaKPlus (finiteGammaClass A) = gammaClass A.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

def finiteGammaToRESKPlus : FiniteGammaKPlus hc S k →+ RESKPlus S k :=
  PositiveAdditiveGrothendieck.lift (finiteGammaPresentation hc S k) {
    toFun A := resClass A.resLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := finiteGammaHom_lift_iso e.hom
      exact resClass_iso E
    empty := by
      apply resToRVKPlus_injective
      rw [resToRVKPlus_class, map_zero]
      exact gammaRVClass_empty
    scissor := by
      intro A B D E h
      apply resToRVKPlus_injective
      simp only [map_add, resToRVKPlus_class]
      change rvClass A.obj.rvLift + rvClass B.obj.rvLift = rvClass D.obj.rvLift + rvClass E.obj.rvLift
      have hs0 : gammaClass A.obj + gammaClass B.obj = gammaClass D.obj + gammaClass E.obj :=
        positiveClass_scissor (gammaPresentation hc S k) h
      have hs := congrArg gammaToRVKPlus hs0
      simpa only [map_add, gammaToRVKPlus_class] using hs }

@[simp] theorem finiteGammaToRESKPlus_class (A : FiniteGammaObject hc S k) :
    finiteGammaToRESKPlus (finiteGammaClass A) = resClass A.resLift :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem finiteGamma_positive_square :
    (resToRVKPlus (M := M) (S := S) (k := k)).comp (finiteGammaToRESKPlus (hc := hc)) =
      gammaToRVKPlus.comp finiteGammaToGammaKPlus := by
  apply PositiveAdditiveGrothendieck.hom_ext (finiteGammaPresentation hc S k)
  intro A
  change resToRVKPlus (finiteGammaToRESKPlus (finiteGammaClass A)) =
    gammaToRVKPlus (finiteGammaToGammaKPlus (finiteGammaClass A))
  rw [finiteGammaToRESKPlus_class, resToRVKPlus_class,
    finiteGammaToGammaKPlus_class, gammaToRVKPlus_class]
  rfl

end DiamondIntegral.Section3
