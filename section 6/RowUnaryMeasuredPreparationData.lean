import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredFocusStep

/-! (Row-form version for Remark 6.20, translated from `UnaryMeasuredPreparationData`.)
 Actual unary measured preparation data and exact composition through
an earlier protected special map. Every narrow map is the literal
restriction of the common ambient map; forms are transported pointwise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

structure UnaryMeasuredPreparationRow (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (ω : RowFormOn A qR) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) 1 arity) S
  map : Map A target
  special : SpecialCovariantChain (G := G) A target map
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  prepared : IsRVPullback target.carrier
  tagged : ∀ p ∈ target.carrier, ∀ q ∈ target.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  form : RowFormOn target qR
  transportRow : ∀ p : A, (form (map p)).val = (ω p).val
  constant : ∀ p ∈ target.carrier, ∀ q ∈ target.carrier, p.2 = q.2 →
    rowFormExtension form p = rowFormExtension form q
  pieces : ∀ i, SpecialCovariantChain (G := G) (C i) (map.restrict (hCA i)).image (map.restrict (hCA i)).toImage ∧
    IsRVPullback (map.restrict (hCA i)).image.carrier

def UnaryMeasuredPreparationRow.precompose {s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {A₀ : DefSet (rawMixedSpace (M := M) 1 s) S}
    (h00 : M ⊨ Axioms.ACVF00)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (f₀ : Map A A₀) (hf₀ : SpecialCovariantChain (G := G) A A₀ f₀)
    (hPieces₀ : ∀ i, SpecialCovariantChain (G := G) (C i) (f₀.restrict (hCA i)).image (f₀.restrict (hCA i)).toImage)
    (hC₀A₀ : ∀ i, (f₀.restrict (hCA i)).image.carrier ⊆ A₀.carrier)
    (ω : RowFormOn A qR)
    (ω₀ : RowFormOn A₀ qR)
    (hTransport₀ : ∀ p : A, (ω₀ (f₀ p)).val = (ω p).val)
    (T : UnaryMeasuredPreparationRow (G := G) A₀ (fun i => (f₀.restrict (hCA i)).image) hC₀A₀ ω₀) :
    UnaryMeasuredPreparationRow (G := G) A C hCA ω := by
  refine {
    arity := T.arity
    target := T.target
    map := T.map.comp f₀
    special := .comp hf₀ T.special
    proper := T.proper
    doublyBounded := T.doublyBounded
    prepared := T.prepared
    tagged := T.tagged
    form := T.form
    transportRow := fun p => (T.transportRow (f₀ p)).trans (hTransport₀ p)
    constant := T.constant
    pieces := ?_
  }
  intro i
  let g₀ := (f₀.restrict (hCA i)).toImage
  have hg : SpecialCovariantChain (G := G) (C i) (T.map.restrict (hC₀A₀ i)).image
      ((T.map.restrict (hC₀A₀ i)).toImage.comp g₀) := .comp (hPieces₀ i) (T.pieces i).1
  have hPoint (p : C i) :
      (((T.map.restrict (hC₀A₀ i)).toImage.comp g₀) p).val = ((T.map.comp f₀) ⟨p.val,hCA i p.property⟩).val := rfl
  have he := image_eq_of_surjective_liesOver (T.map.comp f₀)
    ((T.map.restrict (hC₀A₀ i)).toImage.comp g₀) (hg.bijective h00).surjective (hCA i) hPoint
  exact ⟨hg.restriction_of_liesOver h00 (T.map.comp f₀) (hCA i) hPoint,
    by rw [← he]; exact (T.pieces i).2⟩

end DiamondIntegral.Section6
