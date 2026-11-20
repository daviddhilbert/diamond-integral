import «section 6».MeasuredMorphismsLiftChains
import «section 6».ZeroArityRVIsomorphismLifts

/-! Lemma 6.33's first clause in every degree, without the doubly bounded
hypothesis. In degree zero there are no VF coordinates, so "relatively
unary" is vacuous and the clause is the existence of a lift with the
measure identity (`lemma_6_31_zero_arity`). In positive degree the lift is
the composite of Section 6's chain of relatively unary measured lifts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Lemma 6.33, first clause, degree zero: every measured RV isomorphism in
degree zero has an everywhere measured lift (any object, any base). -/
theorem lemma_6_33_zero_degree {S : Set M} {U V : MeasuredRVObject (M := M) S 0}
    (e : MeasuredRVIso U V) : Nonempty (EverywhereMeasuredRVLift e) := by
  obtain ⟨f, hf, hl, hm⟩ := lemma_6_31_zero_arity e
  exact ⟨⟨f, hf, hl, hm⟩⟩

/-- A chain whose composite has the RV map of `e` gives a lift of `e`. -/
def MeasuredVFUnaryLiftChain.liftOf {S : Set M} {n : ℕ} {U V : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso U V} (T : MeasuredVFUnaryLiftChain S n U V)
    (h : T.iso.iso.hom.map = e.iso.hom.map) : EverywhereMeasuredRVLift e where
  map := T.lift.map
  bijective := T.lift.bijective
  labels p := h ▸ T.lift.labels p
  measure := T.lift.measure

/-- Lemma 6.33, first clause, in every degree `k` (including `0`) and for
objects that need not be doubly bounded: every measured RV isomorphism has an
everywhere measured lift; in positive degree it is the composite of a chain
of relatively unary measured lifts with the given RV map, doubly bounded when
both objects are. -/
theorem lemma_6_33_all_degrees_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1) {k : ℕ}
    {U V : MeasuredRVObject (M := M) (S : Set M) k} (e : MeasuredRVIso U V) :
    Nonempty (EverywhereMeasuredRVLift e) ∧
      (0 < k → ∃ T : MeasuredVFUnaryLiftChain (S : Set M) k U V, T.iso.iso.hom.map = e.iso.hom.map ∧
        ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨lemma_6_33_zero_degree e, fun h => absurd h (lt_irrefl 0)⟩
  · obtain ⟨T, hT, hB⟩ := lemma_6_33_vfGenerated (G := G) h00 hc hκ hs hv S B hsmall hΓ hnt hk e
    exact ⟨⟨T.liftOf hT⟩, fun _ => ⟨T, hT, hB⟩⟩

end DiamondIntegral.Section6
