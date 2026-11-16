import «section 6».UnaryOffsetCoreFibres

/-! Proper complements of the actual offset cores. Every center is
removed from the complement, with literal containment and all ambient
bounds retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (F : UnaryFocusData A)
variable (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))

def offsetCoreComplement : DefSet (rawMixedSpace (M := M) 1 r) S :=
  ⟨A.carrier \ (F.offsetCoreDomain dMap).carrier,A.definable.sdiff _ (F.offsetCoreDomain dMap).definable⟩

theorem offsetCoreComplement_subset : (F.offsetCoreComplement dMap).carrier ⊆ A.carrier := fun _ hp => hp.1

theorem offsetCoreComplement_doublyBounded : VFDoublyBounded (F.offsetCoreComplement dMap).carrier := by
  obtain ⟨γ,hγ⟩ := F.sourceDoublyBounded
  exact ⟨γ,fun p hp => hγ p hp.1⟩

theorem offsetCoreComplement_tagged : ∀ p ∈ (F.offsetCoreComplement dMap).carrier,
    ∀ q ∈ (F.offsetCoreComplement dMap).carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1 :=
  fun p hp q hq => F.tagged p hp.1 q hq.1

variable (d : (Fin r → RVInfinity M) → VF M)
variable (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)
include hdMap in
theorem offsetCoreDomain_contains_center (p : Mixed M 1 r) (hp : p ∈ A.carrier)
    (hu : p.2 ∈ F.activeTags.carrier) (hd : d p.2 ≠ 0) (hCenter : p.1 0=F.focus p.2) :
    p ∈ (F.offsetCoreDomain dMap).carrier := by
  rw [F.mem_offsetCoreDomain dMap d hdMap]
  refine ⟨hp,hu,?_⟩
  rw [hCenter,sub_self]
  exact gamma_lt_value_zero (finiteValue (d p.2) hd)

include hdMap in
theorem offsetCoreComplement_ne_center (p : Mixed M 1 r)
    (hp : p ∈ (F.offsetCoreComplement dMap).carrier)
    (hu : p.2 ∈ F.activeTags.carrier) (hd : d p.2 ≠ 0) : p.1 0 ≠ F.focus p.2 :=
  fun he => hp.2 (F.offsetCoreDomain_contains_center dMap d hdMap p hp.1 hu hd he)

include hdMap in
theorem offsetCoreComplement_avoids_centers
    (E : Set (Mixed M 1 r)) (hEA : E ⊆ A.carrier)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hE : ∀ p ∈ E,p.2 ∈ F.activeTags.carrier ∧ p.1 0=F.focus p.2) :
    ∀ p ∈ (F.offsetCoreComplement dMap).carrier,p ∉ E := by
  intro p hp hpE
  exact F.offsetCoreComplement_ne_center dMap d hdMap p hp (hE p hpE).1
    (hd p.2 (hE p hpE).1) (hE p hpE).2

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
include hdMap in
theorem offsetCoreComplement_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0) :
    ProperInvariant S (F.offsetCoreComplement dMap).carrier :=
  F.sourceProper.diff (F.offsetCoreDomain_proper dMap d hdMap h00 hc hκ hs hv hd)

end DiamondIntegral.Section6.UnaryFocusData
