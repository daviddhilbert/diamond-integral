import «section 3».MeasuredVFPositive
import «section 3».MeasuredVFZero
import «section 3».Grothendieck

/-! Scissors for the actual quotient groupoids of measured VF objects.
The separate degree-zero presentation retains its form and admits no
exceptional points. Positive degrees use essential-bijection germs. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}

section
variable {S : Set M}

def ZeroMeasuredVF.empty (S : Set M) (hc : CanonicalStructure.IsCanonical (M := M)) : ZeroMeasuredVF S hc where
  arity := 0
  domain := DefSet.empty (rawMixedSpace 0 0) S
  finite _ := Set.finite_empty
  form := Map.empty (rawMixedSpace 0 0) (volumeGammaSpace hc) S

def ZeroMeasuredVF.restrict (U : ZeroMeasuredVF S hc)
    (X : DefSet (rawMixedSpace (M := M) 0 U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) : ZeroMeasuredVF S hc where
  arity := U.arity
  domain := X
  finite a := (U.finite a).subset (fun _ ht => hX ht)
  form := U.form.comp (Map.inclusion hX)

def zeroMeasuredVFScissor (A B D E : ZeroMeasuredVF S hc) : Prop :=
  ∃ U : ZeroMeasuredVF S hc, ∃ X : DefSet (rawMixedSpace (M := M) 0 U.arity) S,
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧
      B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = ZeroMeasuredVF.empty S hc

def zeroMeasuredVFPresentation (S : Set M) (hc : CanonicalStructure.IsCanonical (M := M)) : ScissorPresentation (ZeroMeasuredVF S hc) where
  iso A B := Nonempty (A ≅ B)
  empty := ZeroMeasuredVF.empty S hc
  scissor := zeroMeasuredVFScissor

def zeroMeasuredVFClass (A : ZeroMeasuredVF S hc) : KPlus (zeroMeasuredVFPresentation S hc) :=
  positiveClass (zeroMeasuredVFPresentation S hc) A

@[simp] theorem zeroMeasuredVFClass_empty : zeroMeasuredVFClass (ZeroMeasuredVF.empty S hc) = 0 :=
  positiveClass_empty (zeroMeasuredVFPresentation S hc)

theorem zeroMeasuredVFClass_iso {A B : ZeroMeasuredVF S hc} (e : A ≅ B) :
    zeroMeasuredVFClass A = zeroMeasuredVFClass B := positiveClass_iso (zeroMeasuredVFPresentation S hc) ⟨e⟩

theorem zeroMeasuredVFClass_scissor (U : ZeroMeasuredVF S hc)
    (X : DefSet (rawMixedSpace (M := M) 0 U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) :
    zeroMeasuredVFClass (U.restrict X hX) +
      zeroMeasuredVFClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) = zeroMeasuredVFClass U := by
  have h : zeroMeasuredVFScissor (U.restrict X hX)
      (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) U (ZeroMeasuredVF.empty S hc) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (zeroMeasuredVFPresentation S hc) h
  change zeroMeasuredVFClass _ + zeroMeasuredVFClass _ = zeroMeasuredVFClass _ + zeroMeasuredVFClass _ at hs
  simpa only [zeroMeasuredVFClass_empty, add_zero] using hs

end

section
variable {C : BaseContext M} {k : ℕ}

def PositiveMeasuredVF.empty (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) (k : ℕ) : PositiveMeasuredVF C hc k where
  arity := 0
  domain := DefSet.empty (rawMixedSpace (k + 1) 0) (C.base : Set M)
  finite _ := Set.finite_empty
  form := Map.empty (rawMixedSpace (k + 1) 0) (volumeGammaSpace hc) (C.base : Set M)

def PositiveMeasuredVF.restrict (U : PositiveMeasuredVF C hc k)
    (X : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) (C.base : Set M))
    (hX : X.carrier ⊆ U.domain.carrier) : PositiveMeasuredVF C hc k where
  arity := U.arity
  domain := X
  finite a := (U.finite a).subset (fun _ ht => hX ht)
  form := U.form.comp (Map.inclusion hX)

def positiveMeasuredVFScissor (A B D E : PositiveMeasuredVF C hc k) : Prop :=
  ∃ U : PositiveMeasuredVF C hc k, ∃ X : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) (C.base : Set M),
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧
      B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = PositiveMeasuredVF.empty C hc k

variable [CharZero (VFType (M := M))]
def positiveMeasuredVFPresentation (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) (k : ℕ) : ScissorPresentation (PositiveMeasuredVF C hc k) where
  iso A B := Nonempty (A ≅ B)
  empty := PositiveMeasuredVF.empty C hc k
  scissor := positiveMeasuredVFScissor

def positiveMeasuredVFClass (A : PositiveMeasuredVF C hc k) : KPlus (positiveMeasuredVFPresentation C hc k) :=
  positiveClass (positiveMeasuredVFPresentation C hc k) A

@[simp] theorem positiveMeasuredVFClass_empty : positiveMeasuredVFClass (PositiveMeasuredVF.empty C hc k) = 0 :=
  positiveClass_empty (positiveMeasuredVFPresentation C hc k)

theorem positiveMeasuredVFClass_iso {A B : PositiveMeasuredVF C hc k} (e : A ≅ B) :
    positiveMeasuredVFClass A = positiveMeasuredVFClass B := positiveClass_iso (positiveMeasuredVFPresentation C hc k) ⟨e⟩

theorem positiveMeasuredVFClass_scissor (U : PositiveMeasuredVF C hc k)
    (X : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) (C.base : Set M))
    (hX : X.carrier ⊆ U.domain.carrier) :
    positiveMeasuredVFClass (U.restrict X hX) +
      positiveMeasuredVFClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) = positiveMeasuredVFClass U := by
  have h : positiveMeasuredVFScissor (U.restrict X hX)
      (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) U (PositiveMeasuredVF.empty C hc k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (positiveMeasuredVFPresentation C hc k) h
  change positiveMeasuredVFClass _ + positiveMeasuredVFClass _ = positiveMeasuredVFClass _ + positiveMeasuredVFClass _ at hs
  simpa only [positiveMeasuredVFClass_empty, add_zero] using hs

end

abbrev MeasuredVFObject (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) : ℕ → Type
  | 0 => ZeroMeasuredVF (C.base : Set M) hc
  | k + 1 => PositiveMeasuredVF C hc k

instance measuredVFObjectGroupoid [CharZero (VFType (M := M))]
    (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :
    ∀ k, Groupoid (MeasuredVFObject C hc k)
  | 0 => inferInstanceAs (Groupoid (ZeroMeasuredVF (C.base : Set M) hc))
  | k + 1 => inferInstanceAs (Groupoid (PositiveMeasuredVF C hc k))

def measuredVFPresentation [CharZero (VFType (M := M))]
    (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :
    ∀ k, ScissorPresentation (MeasuredVFObject C hc k)
  | 0 => zeroMeasuredVFPresentation (C.base : Set M) hc
  | k + 1 => positiveMeasuredVFPresentation C hc k

abbrev MeasuredVFKPlus [CharZero (VFType (M := M))]
    (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) (k : ℕ) :=
  KPlus (measuredVFPresentation C hc k)

abbrev MeasuredVFKGroup [CharZero (VFType (M := M))]
    (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) (k : ℕ) :=
  KGroup (measuredVFPresentation C hc k)

end DiamondIntegral.Section3
