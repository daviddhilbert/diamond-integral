import «section 6».RVHeadStartBundles
import «section 6».PreparedRVObjects

/-! Every retained-label head start preserves the actual proper bounds,
RV-pullback and tagged geometry. Its RV object has degree n+k. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem rvHeadStartBundle_rvBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : RVSupportDoublyBounded A.carrier) : RVSupportDoublyBounded (rvHeadStartBundle A k π).carrier := by
  obtain ⟨γ,hγ⟩ := hA
  exact ⟨γ,fun p hp i => hγ _ ((mem_rvHeadStartBundle A k π p.1 p.2).mp hp).1 i⟩

theorem rvHeadStartBundle_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : VFDoublyBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier) :
    VFDoublyBounded (rvHeadStartBundle A k π).carrier := by
  induction k with
  | zero => exact hA
  | succ k ih => exact rvCoordinateBundle_doublyBounded _ _ (ih _) (rvHeadStartBundle_rvBounded A k _ hRV)

theorem rvHeadStartBundle_pullback
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : IsRVPullback A.carrier) : IsRVPullback (rvHeadStartBundle A k π).carrier := by
  induction k with
  | zero => exact hA
  | succ k ih => exact rvCoordinateBundle_pullback _ _ (ih _)

theorem rvHeadStartBundle_tagged
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    ∀ p ∈ (rvHeadStartBundle A k π).carrier,∀ q ∈ (rvHeadStartBundle A k π).carrier,
      p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  induction k with
  | zero => exact hA
  | succ k ih => exact rvCoordinateBundle_tagged _ _ (ih _)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem rvHeadStartBundle_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : ProperInvariant S A.carrier) : ProperInvariant S (rvHeadStartBundle A k π).carrier := by
  induction k with
  | zero => exact hA
  | succ k ih => exact rvCoordinateBundle_properInvariant h00 hc hκ hs hv _ _ (ih _)

def preparedHeadStartRVObject
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    RVObject (M := M) S (n+k) :=
  preparedRVObject (rvHeadStartBundle A k π) (rvHeadStartBundle_tagged A k π hA)

theorem preparedHeadStartRVObject_lift_carrier
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    (rvLift (preparedHeadStartRVObject A k π hTag)).carrier=(rvHeadStartBundle A k π).carrier :=
  preparedRVObject_lift_carrier _ (rvHeadStartBundle_pullback A k π hA) _

theorem preparedHeadStartRVObject_finite_volume
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hA : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) :
    (preparedHeadStartRVObject A k π hTag).volume.FiniteFibres :=
  preparedRVObject_finite_volume _ (rvHeadStartBundle_pullback A k π hA) _
    (rvHeadStartBundle_finite_rv_fibres A k π hFin)

theorem preparedHeadStartRVObject_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hA : VFDoublyBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier) :
    RVValueDoublyBounded (preparedHeadStartRVObject A k π hTag).domain.carrier ∧
      RVValueDoublyBounded (Set.range (preparedHeadStartRVObject A k π hTag).value) :=
  ⟨preparedRVObject_domain_doublyBounded _ _ (rvHeadStartBundle_rvBounded A k π hRV),
    preparedRVObject_values_doublyBounded _ _ (rvHeadStartBundle_doublyBounded A k π hA hRV)⟩

end DiamondIntegral.Section6
