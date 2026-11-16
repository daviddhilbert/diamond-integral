import «section 6».PureRVDiscQuotients

/-! The actual finite-volume RV object of a prepared domain. Its lifted
set is exactly the original prepared set, and its finite-volume property
follows from finite RV fibers at a genuine VF representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem preparedRVObject_lift_carrier
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    (rvLift (preparedRVObject A hTag)).carrier = A.carrier := by
  ext p
  constructor
  · rintro ⟨u,hu,hVolume⟩
    obtain ⟨q,hqu⟩ := pureRVTagQuotient_surjective A u
    have hqVolume := preparedRVVolume_at A hTag q
    rw [hqu] at hqVolume
    have hHead : tupleRV M q.val.1 = tupleRV M p.1 := hqVolume.symm.trans hVolume
    have hTags : q.val.2 = p.2 := (congrArg Subtype.val hqu).trans hu
    exact rvPullback_mem_of_sameRV hA q.property hHead hTags
  · intro hp
    exact ⟨pureRVTagQuotient A ⟨p,hp⟩,rfl,preparedRVVolume_at A hTag ⟨p,hp⟩⟩

theorem preparedRVObject_finite_volume
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hFin : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    (preparedRVObject A hTag).volume.FiniteFibres := by
  intro t
  obtain ⟨a,ha⟩ := SpecialTransformations.Section4.tupleRV_surjective t.val
  have ha' : tupleRV M a = t.val := ha
  apply ((hFin a).preimage Subtype.val_injective.injOn).subset
  intro u hu
  change (a,u.val) ∈ A.carrier
  obtain ⟨p,hpu⟩ := pureRVTagQuotient_surjective A u
  have hpVolume := preparedRVVolume_at A hTag p
  rw [hpu] at hpVolume
  have hHead : tupleRV M p.val.1 = tupleRV M a :=
    hpVolume.symm.trans ((congrArg Subtype.val hu).trans ha'.symm)
  exact rvPullback_mem_of_sameRV hA p.property hHead (congrArg Subtype.val hpu)

theorem preparedRVObject_domain_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hRV : RVSupportDoublyBounded A.carrier) : RVValueDoublyBounded (preparedRVObject A hTag).domain.carrier := by
  obtain ⟨γ,hγ⟩ := hRV
  refine ⟨γ,?_⟩
  rintro _ ⟨p,rfl⟩ i
  exact hγ p.val p.property i

theorem preparedRVObject_values_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hVF : VFDoublyBounded A.carrier) : RVValueDoublyBounded (Set.range (preparedRVObject A hTag).value) := by
  obtain ⟨γ,hγ⟩ := hVF
  refine ⟨γ,?_⟩
  rintro _ ⟨u,rfl⟩ i
  obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective A u
  change (γ⁻¹).val ≤ Values.vrv ((preparedRVVolume A hTag (pureRVTagQuotient A p)).val i) ∧
    Values.vrv ((preparedRVVolume A hTag (pureRVTagQuotient A p)).val i) ≤ γ.val
  rw [preparedRVVolume_at]
  exact hγ p.val p.property i

end DiamondIntegral.Section6
