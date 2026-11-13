import «section 3».GammaVolumeCategories
import «section 3».Grothendieck
import Section4.RVRestrictions

/-! Fixed-degree scissor quotients for Gamma families and Gamma volume
forms. Restrictions retain every tag and the inherited form. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}
local notation "P" => Space.power (volumeGammaSpace hc) (Fin k)

def GammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    GammaObject hc S k := ⟨0, fun i => i.elim0⟩

def GammaObject.restrict (A : GammaObject hc S k) (X : Fin A.tags → DefSet P S) :
    GammaObject hc S k := ⟨A.tags, X⟩

def GammaObject.difference (A : GammaObject hc S k) (X : Fin A.tags → DefSet P S) :
    Fin A.tags → DefSet P S := fun i => (A.piece i).sdiff (X i)

def MeasuredGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    MeasuredGammaObject hc S k := ⟨GammaObject.empty hc S k, fun i => i.elim0⟩

def MeasuredGammaObject.restrict (A : MeasuredGammaObject hc S k)
    (X : Fin A.underlying.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.underlying.piece i).carrier) : MeasuredGammaObject hc S k :=
  ⟨A.underlying.restrict X, fun i => (A.form i).comp (Map.inclusion (hX i))⟩

def GammaScissor (A B C D : GammaObject hc S k) : Prop :=
  ∃ U : GammaObject hc S k, ∃ X : Fin U.tags → DefSet P S,
    ∃ hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier,
      A = U.restrict X ∧ B = U.restrict (U.difference X) ∧ C = U ∧ D = GammaObject.empty hc S k

def gammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    ScissorPresentation (GammaObject hc S k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaObject.empty hc S k
  scissor := GammaScissor

abbrev GammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KPlus (gammaPresentation hc S k)
abbrev GammaKGroup (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KGroup (gammaPresentation hc S k)

def gammaClass (A : GammaObject hc S k) : GammaKPlus hc S k :=
  positiveClass (gammaPresentation hc S k) A

theorem gammaClass_iso {A B : GammaObject hc S k} (e : A ≅ B) :
    gammaClass A = gammaClass B := positiveClass_iso (gammaPresentation hc S k) ⟨e⟩

@[simp] theorem gammaClass_empty : gammaClass (GammaObject.empty hc S k) = 0 :=
  positiveClass_empty (gammaPresentation hc S k)

theorem gammaClass_scissor (U : GammaObject hc S k)
    (X : Fin U.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    gammaClass (U.restrict X) + gammaClass (U.restrict (U.difference X)) = gammaClass U := by
  have h : GammaScissor (U.restrict X) (U.restrict (U.difference X)) U (GammaObject.empty hc S k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (gammaPresentation hc S k) h
  change gammaClass _ + gammaClass _ = gammaClass _ + gammaClass _ at hs
  simpa only [gammaClass_empty, add_zero] using hs

def MeasuredGammaScissor (A B C D : MeasuredGammaObject hc S k) : Prop :=
  ∃ U : MeasuredGammaObject hc S k, ∃ X : Fin U.underlying.tags → DefSet P S,
    ∃ hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.underlying.difference X) (fun i _ h => h.1) ∧ C = U ∧ D = MeasuredGammaObject.empty hc S k

def measuredGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    ScissorPresentation (MeasuredGammaObject hc S k) where
  iso A B := Nonempty (A ≅ B)
  empty := MeasuredGammaObject.empty hc S k
  scissor := MeasuredGammaScissor

abbrev MeasuredGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KPlus (measuredGammaPresentation hc S k)
abbrev MeasuredGammaKGroup (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KGroup (measuredGammaPresentation hc S k)

def measuredGammaClass (A : MeasuredGammaObject hc S k) : MeasuredGammaKPlus hc S k :=
  positiveClass (measuredGammaPresentation hc S k) A

theorem measuredGammaClass_iso {A B : MeasuredGammaObject hc S k} (e : A ≅ B) :
    measuredGammaClass A = measuredGammaClass B := positiveClass_iso (measuredGammaPresentation hc S k) ⟨e⟩

@[simp] theorem measuredGammaClass_empty : measuredGammaClass (MeasuredGammaObject.empty hc S k) = 0 :=
  positiveClass_empty (measuredGammaPresentation hc S k)

theorem measuredGammaClass_scissor (U : MeasuredGammaObject hc S k)
    (X : Fin U.underlying.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    measuredGammaClass (U.restrict X hX) + measuredGammaClass (U.restrict (U.underlying.difference X) (fun i _ h => h.1)) = measuredGammaClass U := by
  have h : MeasuredGammaScissor (U.restrict X hX) (U.restrict (U.underlying.difference X) (fun i _ h => h.1)) U (MeasuredGammaObject.empty hc S k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (measuredGammaPresentation hc S k) h
  change measuredGammaClass _ + measuredGammaClass _ = measuredGammaClass _ + measuredGammaClass _ at hs
  simpa only [measuredGammaClass_empty, add_zero] using hs

end DiamondIntegral.Section3
