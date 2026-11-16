import «section 6».EverywhereMeasuredRVLiftData
import «section 6».MeasuredRVRestrictions

/-! Restriction of an actual everywhere measured lift to whole label
domains retains its full total charts and literal restricted forms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem mixedDerivative_to_label_restriction
    {U V : RVObject (M := M) S n}
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    {B : DefSet (rawMixedSpace (M := M) n V.arity) S}
    (f : Map (rvLift U) (rvLift V)) (g : Map (rvLift (U.restrict A hA)) B)
    (p : rvLift (U.restrict A hA)) (q : rvLift U) (hpq : p.val = q.val)
    (hagree : ∀ (p' : rvLift (U.restrict A hA)) (q' : rvLift U), p'.val = q'.val →
      (g p').val = (f q').val)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hL : HasMixedVFDerivativeAt f q L) : HasMixedVFDerivativeAt g p L := by
  obtain ⟨F,⟨ρ,hρ⟩,hD⟩ := hL
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  have hpA := ((rvLift_restrict_mem_iff U A hA p.val).mp p.property).2
  refine ⟨F,⟨ρ,fun z hz => ?_⟩,h₁.symm ▸ hD⟩
  obtain ⟨hzU,hzF⟩ := hρ z (h₁ ▸ hz)
  have hzU' : (z,p.val.2) ∈ (rvLift U).carrier := h₂.symm ▸ hzU
  let a : rvLift (U.restrict A hA) :=
    ⟨(z,p.val.2),(rvLift_restrict_mem_iff U A hA _).mpr ⟨hzU',hpA⟩⟩
  let b : rvLift U := ⟨(z,q.val.2),hzU⟩
  refine ⟨a.property,?_⟩
  change (g a).val = _
  rw [hagree a b (Prod.ext rfl h₂),hzF,← congrArg Prod.snd (hagree p q hpq)]

theorem exists_everywhere_measured_lift_restrict
    {U V : MeasuredRVObject (M := M) S n} {e : MeasuredRVIso U V}
    (F : EverywhereMeasuredRVLift e)
    (A : DefSet (rawRVSpace (M := M) U.object.arity) S) (hA : A.carrier ⊆ U.object.domain.carrier) :
    Nonempty (EverywhereMeasuredRVLift (e.restrict A hA)) := by
  obtain ⟨g,hg,hagree⟩ := exists_restricted_actual_lift e.iso A hA F.map F.bijective F.labels
  refine ⟨⟨g,hg,fun p => ?_,fun p => ?_⟩⟩
  · let q : rvLift U.object :=
      ⟨p.val,((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).1⟩
    obtain ⟨u,hu,hv⟩ := F.labels q
    have huA : u.val ∈ A.carrier := hu.symm ▸
      ((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).2
    exact ⟨⟨u.val,huA⟩,hu,hv.trans (congrArg Prod.snd (hagree p q rfl)).symm⟩
  · let q : rvLift U.object :=
      ⟨p.val,((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).1⟩
    obtain ⟨L,hL,hJ⟩ := F.measure q
    refine ⟨L,mixedDerivative_to_label_restriction A hA F.map g p q rfl hagree hL,?_⟩
    have hVal := congrArg Prod.snd (hagree p q rfl)
    change vfValue (LinearMap.toMatrix' L).det =
      (gammaMapValue U.form (liftLabelMap U.object q) /
        gammaMapValue V.form ⟨(g p).val.2,
          rvLabelImage_subset e.iso A hA (liftLabelMap _ (g p)).property⟩).val
    have he : (⟨(g p).val.2,
        rvLabelImage_subset e.iso A hA (liftLabelMap _ (g p)).property⟩ : V.object.domain) =
        liftLabelMap V.object (F.map q) := Subtype.ext hVal
    rw [he]
    exact hJ

end DiamondIntegral.Section6
