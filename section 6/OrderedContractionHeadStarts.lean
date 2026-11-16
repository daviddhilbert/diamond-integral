import «section 6».OrderedContractionLiftProperties
import «section 6».HeadStartCarriedGeometry

/-! The degree n+k and actual VF lift of a standard contraction with
head start k. Every added VF coordinate stays fixed. The finite-volume
condition follows from the source fibres over the selected old RV head. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S A U}
namespace OrderedStandardContractionLift

def headStartObject (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    RVObject (M := M) S (n+k) :=
  preparedHeadStartRVObject V.target k (T.oldLabels ∘ π) V.target_tagged

def headStartBijection (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    HeadStartCarriedBijection V.map k π (T.oldLabels ∘ π) :=
  carryHeadStartBijection V.map V.home.bijective k π (T.oldLabels ∘ π) (fun p i => V.retained p (π i))

theorem headStart_target_eq (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    rvHeadStartBundle V.target k (T.oldLabels ∘ π)=rvLift (V.headStartObject k π) :=
  (defSet_eq_of_carrier_eq (preparedHeadStartRVObject_lift_carrier V.target k _ V.pullback V.target_tagged)).symm

def headStartLift (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    Map (rvHeadStartBundle A k π) (rvLift (V.headStartObject k π)) :=
  changeMapTarget (V.headStartBijection k π).map (V.headStart_target_eq k π)

theorem headStartLift_value (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (p : rvHeadStartBundle A k π) :
    (V.headStartLift k π p).val=((V.headStartBijection k π).map p).val :=
  changeMapTarget_value _ _ p

theorem headStartLift_fixed (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (p : rvHeadStartBundle A k π) :
    headStartExtraVF n k (V.headStartLift k π p).val.1=headStartExtraVF n k p.val.1 := by
  rw [headStartLift_value]
  exact (V.headStartBijection k π).fixed p

theorem headStartLift_labels (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (p : rvHeadStartBundle A k π) :
    (V.headStartLift k π p).val.2=(T.toMap (headStartBaseProjection A k π p)).val.2 := by
  rw [headStartLift_value,(V.headStartBijection k π).labels]
  exact V.labels _

theorem headStartObject_finite_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) :
    (V.headStartObject k π).volume.FiniteFibres :=
  prepared_head_start_finite_volume_of_bijective hc h00 hκ hs hsmall V.map V.home.bijective k π _
    (fun p i => V.retained p (π i)) V.pullback V.target_tagged hFin

theorem headStartObject_doublyBounded (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    RVValueDoublyBounded (V.headStartObject k π).domain.carrier ∧
      RVValueDoublyBounded (Set.range (V.headStartObject k π).value) :=
  preparedHeadStartRVObject_doublyBounded V.target k _ V.target_tagged V.doublyBounded V.proper.rvBounded

theorem headStartLift_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    ProperCovariantHomeomorphism (V.headStartLift k π) :=
  (carryHeadStartBijection_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    V.map V.home.bijective V.home k π _ (fun p i => V.retained p (π i))).changeMapTarget _

theorem headStartLift_unit_derivative_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hn : 0 < n) (hA : ProperInvariant S A.carrier)
    (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    ∃ E : DefSet (rawMixedSpace (M := M) (n+k) r) S,E.carrier ⊆ (rvHeadStartBundle A k π).carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n+k ∧
      ∀ p : rvHeadStartBundle A k π,p.val ∉ E.carrier → HasMixedUnitDerivativeAt (V.headStartLift k π) p := by
  obtain ⟨E,hEA,hDim,hUnit⟩ := V.unit_derivative_ae hc hs hsmall hn
  obtain ⟨hSub,hD,hU⟩ := carryHeadStartBijection_unit_derivative_ae h00 hc hκ hs hv hsmall
    V.map V.home.bijective hA k π (T.oldLabels ∘ π) (fun p i => V.retained p (π i)) E hEA hDim hUnit
  exact ⟨rvHeadStartBundle E k π,hSub,hD,fun p hp => (hU p hp).changeMapTarget _⟩

end OrderedStandardContractionLift
end DiamondIntegral.Section6
