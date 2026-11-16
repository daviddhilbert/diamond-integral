import «section 6».UnaryMeasuredRVLifting
import «section 6».ProperHomeomorphisms

/-! Literal nonzero RV lifts have full clopen VF polydisc fibres. Their
actual double bounds imply proper invariance through the proved clopen
criterion, with original-base definable radii. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem nonzero_rvTupleFibre_isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (t : Fin n → RVInfinity M) (ht : ∀ i, (t i).val ≠ iRVZero) :
    IsClopen {x : Fin n → VF M | SpecialTransformations.Section4.tupleRV x = t} := by
  obtain ⟨a,ha⟩ := SpecialTransformations.Section4.tupleRV_surjective t
  have ha0 (i : Fin n) : a i ≠ 0 := by
    intro hz
    apply ht i
    have h := congrArg Subtype.val (congrFun ha i)
    change (rv M (a i)).val = (t i).val at h
    rw [hz,rv_zero] at h
    exact h.symm
  let α : Fin n → Gamma M := fun i => finiteValue (a i) (ha0 i)
  have he : {x : Fin n → VF M | SpecialTransformations.Section4.tupleRV x = t} =
      {x | Congruent α a x} := by
    ext x
    change SpecialTransformations.Section4.tupleRV x = t ↔ Congruent α a x
    rw [← ha]
    constructor
    · intro hx i
      have h := (rv_eq_iff_value_close (ha0 i)).mp (congrFun hx i)
      change vfValue (a i) < vfValue (a i-x i)
      have hc : vfValue (a i-x i) = vfValue (x i-a i) := vfValue_sub_comm _ _
      rw [hc]
      exact h
    · intro hx
      funext i
      apply (rv_eq_iff_value_close (ha0 i)).mpr
      have h := hx i
      change vfValue (a i) < vfValue (a i-x i) at h
      have hc : vfValue (a i-x i) = vfValue (x i-a i) := vfValue_sub_comm _ _
      rwa [hc] at h
  rw [he]
  exact (Congruent.class_invariant α a).isClopen hv

theorem measuredRVLift_fibre_isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : MeasuredRVObject (M := M) S n) (t : Fin U.object.arity → RVInfinity M) :
    IsClopen (vfFibre (rvLift U.object).carrier t) := by
  by_cases ht : t ∈ U.object.domain.carrier
  · let u : U.object.domain := ⟨t,ht⟩
    have he : vfFibre (rvLift U.object).carrier t =
        {x | SpecialTransformations.Section4.tupleRV x = U.object.value u} := by
      ext x
      constructor
      · rintro ⟨v,hv,hvol⟩
        have he : v = u := Subtype.ext hv
        exact hvol.symm.trans (congrArg U.object.value he)
      · intro hx
        exact ⟨u,rfl,hx.symm⟩
    rw [he]
    exact nonzero_rvTupleFibre_isClopen hv (U.object.value u) (U.nonzero u)
  · have he : vfFibre (rvLift U.object).carrier t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨u,hu,_⟩
      change u.val = t at hu
      exact ht (hu ▸ u.property)
    rw [he]
    exact isClopen_empty

theorem measuredRVLift_vfDoublyBounded (U : MeasuredRVObject (M := M) S n)
    (hU : U.doublyBounded) : VFDoublyBounded (rvLift U.object).carrier := by
  obtain ⟨γ,hγ⟩ := hU.2
  refine ⟨γ,fun p hp i => ?_⟩
  let q : rvLift U.object := ⟨p,hp⟩
  have h := hγ (U.object.value (liftLabelMap U.object q)) ⟨_,rfl⟩ i
  rw [liftLabelMap_volume] at h
  exact h

theorem measuredRVLift_rvDoublyBounded (U : MeasuredRVObject (M := M) S n)
    (hU : U.doublyBounded) : RVSupportDoublyBounded (rvLift U.object).carrier := by
  obtain ⟨γ,hγ⟩ := hU.1
  refine ⟨γ,fun p hp i => ?_⟩
  exact hγ p.2 (liftLabelMap U.object ⟨p,hp⟩).property i

theorem measuredRVLift_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : MeasuredRVObject (M := M) S n) (hU : U.doublyBounded) :
    ProperInvariant S (rvLift U.object).carrier := by
  obtain ⟨γ,hγ⟩ := measuredRVLift_vfDoublyBounded U hU
  exact (lemma_6_5 h00 hc hκ hs hv _ (rvLift U.object).definable
    ⟨γ⁻¹,fun p hp i => (hγ p hp i).1⟩ (measuredRVLift_rvDoublyBounded U hU)).mpr
    (measuredRVLift_fibre_isClopen hv U)

end DiamondIntegral.Section6
