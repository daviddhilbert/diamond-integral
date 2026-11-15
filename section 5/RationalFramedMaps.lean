import «section 5».RationalFrameComparison
import «section 5».FramedGraphConstructibility

/-! Framing the full graph of an original-base bijection produces an
equivariant constructible isomorphism, without a denominator choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
local instance rationalFramedMapsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

def RationalFrameSupport {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) : Prop :=
  ∀ r ∈ A.carrier, ∀ i, taggedRVEquiv (r i) = none ∨ value (taggedRVEquiv (r i)) = (q i : WithTop ℚ)

theorem rationalFrame_reconstruction {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : RationalFrameSupport q A) (u : A) :
    rationalFrame q (fun i => lineCoefficient (taggedRVEquiv (u.val i))) = u.val := by
  funext i
  have he := linePoint_coefficient (q i) ⟨taggedRVEquiv (u.val i), hA u.val u.property i⟩
  exact (congrArg rvTag he).trans (taggedRVEquiv.symm_apply_apply _)

def rationalFrameEquiv {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : RationalFrameSupport q A) : A ≃ rationalFramedSet q A where
  toFun u := ⟨fun i => lineCoefficient (taggedRVEquiv (u.val i)), by
    change rationalFrame q _ ∈ A.carrier
    rw [rationalFrame_reconstruction q A hA u]
    exact u.property⟩
  invFun x := ⟨rationalFrame q x.val, x.property⟩
  left_inv u := Subtype.ext (rationalFrame_reconstruction q A hA u)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact lineCoefficient_point (q i) (x.val i)

def rationalFramedBijection {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : RationalFrameSupport q A) (hB : RationalFrameSupport r B)
    (f : DefinableBijection A B) : rationalFramedSet q A ≃ rationalFramedSet r B :=
  ((rationalFrameEquiv q A hA).symm.trans (_root_.Equiv.ofBijective f.map f.bijective)).trans
    (rationalFrameEquiv r B hB)

theorem rationalFramedBijection_graph {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : RationalFrameSupport q A) (hB : RationalFrameSupport r B)
    (f : DefinableBijection A B) :
    framedEquivGraph (rationalFramedSet q A) (rationalFramedSet r B)
      (rationalFramedBijection q r A B hA hB f) =
      rationalFramedSet (Fin.append q r) (originalGraphRVSet A B f.map) := by
  let EA := rationalFrameEquiv q A hA
  let EB := rationalFrameEquiv r B hB
  let e := rationalFramedBijection q r A B hA hB f
  have he (u : A) : e (EA u) = EB (f.map u) := by
    change EB (f.map (EA.symm (EA u))) = _
    rw [EA.symm_apply_apply]
  ext z
  change (∃ x : rationalFramedSet q A, (fun i => z (Fin.castAdd m i)) = x.val ∧
    (fun j => z (Fin.natAdd n j)) = (e x).val) ↔ _
  have hrow : (rationalFrame (Fin.append q r) z ∈ (originalGraphRVSet A B f.map).carrier) ↔
      ∃ u : A, u.val = rationalFrame q (fun i => z (Fin.castAdd m i)) ∧
        (f.map u).val = rationalFrame r (fun j => z (Fin.natAdd n j)) := by
    change (∃ u : A, u.val = _ ∧ (f.map u).val = _) ↔ _
    simp only [rationalFrame, Fin.append_left, Fin.append_right]
    rfl
  change _ ↔ rationalFrame (Fin.append q r) z ∈ (originalGraphRVSet A B f.map).carrier
  rw [hrow]
  constructor
  · rintro ⟨x, hx, hy⟩
    let u := EA.symm x
    refine ⟨u, ?_, ?_⟩
    · change rationalFrame q x.val = _
      rw [hx]
    · have hb := rationalFrame_reconstruction r B hB (f.map u)
      change rationalFrame r (EB (f.map u)).val = (f.map u).val at hb
      have hu : e x = EB (f.map u) := by
        change EB (f.map (EA.symm x)) = _
        rfl
      rw [← hu, ← hy] at hb
      exact hb.symm
  · rintro ⟨u, hu, hv⟩
    refine ⟨EA u, ?_, ?_⟩
    · apply rationalFrame_injective q
      exact hu.symm.trans (rationalFrame_reconstruction q A hA u).symm
    · rw [he]
      apply rationalFrame_injective r
      exact hv.symm.trans (rationalFrame_reconstruction r B hB (f.map u)).symm

def rationalFramedIso {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : RationalFrameSupport q A) (hB : RationalFrameSupport r B)
    (f : DefinableBijection A B) : DiagonalConstructible.Iso (framedObject q A) (framedObject r B) where
  equiv := rationalFramedBijection q r A B hA hB f
  graph_definable := by
    change (Set.univ : Set ℂ).Definable Language.ring
      (framedEquivGraph (rationalFramedSet q A) (rationalFramedSet r B)
        (rationalFramedBijection q r A B hA hB f))
    rw [rationalFramedBijection_graph]
    exact (framedObject (Fin.append q r) (originalGraphRVSet A B f.map)).definable
  graph_invariant := by
    change RationalInvariant (Fin.append q r)
      (framedEquivGraph (rationalFramedSet q A) (rationalFramedSet r B)
        (rationalFramedBijection q r A B hA hB f))
    rw [rationalFramedBijection_graph]
    exact (framedObject (Fin.append q r) (originalGraphRVSet A B f.map)).invariant

end DiamondIntegral.Section5.PuiseuxOriginal
