import «section 3».GammaGroundGammaVolumeCategories
import «section 3».Grothendieck
import Section4.RVRestrictions

/-! Fixed-degree scissor quotients for Gamma families and Gamma volume
forms. Restrictions retain every tag and the inherited form. -/

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
local notation "P" => Space.power (volumeGammaSpace hc) (Fin k)

def GammaGroundGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    GammaGroundGammaObject hc ground k := ⟨0, fun i => i.elim0⟩

def GammaGroundGammaObject.restrict (A : GammaGroundGammaObject hc ground k) (X : Fin A.tags → GammaGroundDefSet hc ground P) :
    GammaGroundGammaObject hc ground k := ⟨A.tags, X⟩

def GammaGroundGammaObject.difference (A : GammaGroundGammaObject hc ground k) (X : Fin A.tags → GammaGroundDefSet hc ground P) :
    Fin A.tags → GammaGroundDefSet hc ground P := fun i => (A.piece i).sdiff (X i)

def GammaGroundMeasuredGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    GammaGroundMeasuredGammaObject hc ground k := ⟨GammaGroundGammaObject.empty hc ground k, fun i => i.elim0⟩

def GammaGroundMeasuredGammaObject.restrict (A : GammaGroundMeasuredGammaObject hc ground k)
    (X : Fin A.underlying.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.underlying.piece i).carrier) : GammaGroundMeasuredGammaObject hc ground k :=
  ⟨A.underlying.restrict X, fun i => (A.form i).comp (GammaGroundMap.inclusion (hX i))⟩

def GammaGroundGammaScissor (A B C D : GammaGroundGammaObject hc ground k) : Prop :=
  ∃ U : GammaGroundGammaObject hc ground k, ∃ X : Fin U.tags → GammaGroundDefSet hc ground P,
    ∃ hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier,
      A = U.restrict X ∧ B = U.restrict (U.difference X) ∧ C = U ∧ D = GammaGroundGammaObject.empty hc ground k

def gammaGroundGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    ScissorPresentation (GammaGroundGammaObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundGammaObject.empty hc ground k
  scissor := GammaGroundGammaScissor

abbrev GammaGroundGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  KPlus (gammaGroundGammaPresentation hc ground k)
abbrev GammaGroundGammaKGroup (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  KGroup (gammaGroundGammaPresentation hc ground k)

def gammaGroundGammaClass (A : GammaGroundGammaObject hc ground k) : GammaGroundGammaKPlus hc ground k :=
  positiveClass (gammaGroundGammaPresentation hc ground k) A

theorem gammaGroundGammaClass_iso {A B : GammaGroundGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundGammaClass A = gammaGroundGammaClass B := positiveClass_iso (gammaGroundGammaPresentation hc ground k) ⟨e⟩

@[simp] theorem gammaGroundGammaClass_empty : gammaGroundGammaClass (GammaGroundGammaObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundGammaPresentation hc ground k)

theorem gammaGroundGammaClass_scissor (U : GammaGroundGammaObject hc ground k)
    (X : Fin U.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    gammaGroundGammaClass (U.restrict X) + gammaGroundGammaClass (U.restrict (U.difference X)) = gammaGroundGammaClass U := by
  have h : GammaGroundGammaScissor (U.restrict X) (U.restrict (U.difference X)) U (GammaGroundGammaObject.empty hc ground k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (gammaGroundGammaPresentation hc ground k) h
  change gammaGroundGammaClass _ + gammaGroundGammaClass _ = gammaGroundGammaClass _ + gammaGroundGammaClass _ at hs
  simpa only [gammaGroundGammaClass_empty, add_zero] using hs

def GammaGroundMeasuredGammaScissor (A B C D : GammaGroundMeasuredGammaObject hc ground k) : Prop :=
  ∃ U : GammaGroundMeasuredGammaObject hc ground k, ∃ X : Fin U.underlying.tags → GammaGroundDefSet hc ground P,
    ∃ hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.underlying.difference X) (fun i _ h => h.1) ∧ C = U ∧ D = GammaGroundMeasuredGammaObject.empty hc ground k

def gammaGroundMeasuredGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    ScissorPresentation (GammaGroundMeasuredGammaObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundMeasuredGammaObject.empty hc ground k
  scissor := GammaGroundMeasuredGammaScissor

abbrev GammaGroundMeasuredGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  KPlus (gammaGroundMeasuredGammaPresentation hc ground k)
abbrev GammaGroundMeasuredGammaKGroup (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  KGroup (gammaGroundMeasuredGammaPresentation hc ground k)

def gammaGroundMeasuredGammaClass (A : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundMeasuredGammaKPlus hc ground k :=
  positiveClass (gammaGroundMeasuredGammaPresentation hc ground k) A

theorem gammaGroundMeasuredGammaClass_iso {A B : GammaGroundMeasuredGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundMeasuredGammaClass A = gammaGroundMeasuredGammaClass B := positiveClass_iso (gammaGroundMeasuredGammaPresentation hc ground k) ⟨e⟩

@[simp] theorem gammaGroundMeasuredGammaClass_empty : gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundMeasuredGammaPresentation hc ground k)

theorem gammaGroundMeasuredGammaClass_scissor (U : GammaGroundMeasuredGammaObject hc ground k)
    (X : Fin U.underlying.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    gammaGroundMeasuredGammaClass (U.restrict X hX) + gammaGroundMeasuredGammaClass (U.restrict (U.underlying.difference X) (fun i _ h => h.1)) = gammaGroundMeasuredGammaClass U := by
  have h : GammaGroundMeasuredGammaScissor (U.restrict X hX) (U.restrict (U.underlying.difference X) (fun i _ h => h.1)) U (GammaGroundMeasuredGammaObject.empty hc ground k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (gammaGroundMeasuredGammaPresentation hc ground k) h
  change gammaGroundMeasuredGammaClass _ + gammaGroundMeasuredGammaClass _ = gammaGroundMeasuredGammaClass _ + gammaGroundMeasuredGammaClass _ at hs
  simpa only [gammaGroundMeasuredGammaClass_empty, add_zero] using hs

end DiamondIntegral.Section3
