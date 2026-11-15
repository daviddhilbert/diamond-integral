import IntegrationSection5.NonrectangleProfiles
import IntegrationSection5.GammaFiniteCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

theorem unary_key_fixed_representative (V : DefSet (M := M) S 1 m)
    (hV : IsRVPullback (carrier V)) (a : rvObjectDomain (pullbackObject V))
    (z : VF (M := M)) (hz : rv z = (rvObjectVolume (pullbackObject V) a).val 0) :
    ∃ p : V, vfAt p.val 0 = z ∧ Map.toImage (rawKeyMap V) p = a := by
  obtain ⟨q,rfl⟩ := rawKeyImage_surjective V a
  rw [pullbackObject_value_key] at hz
  let pval : Point (M := M) 1 m := (fun _ => z,q.val.2)
  have hcell : SameRV pval q.val := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,rfl⟩
    intro i; fin_cases i; exact hz
  let p : V := ⟨pval,(isRVPullback_iff _).mp hV q.val q.property pval hcell.symm⟩
  exact ⟨p,rfl,Subtype.ext ((rawKeyMap_eq_iff p q).mpr hcell)⟩

namespace PositionedCellLabelInjection.NonrectangleMatchedHeads
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A}

theorem profileA_key_recover (Q : NonrectangleMatchedHeads T) (p : Q.unary.targetA) :
    (Q.profileA (Map.toImage (rawKeyMap Q.unary.targetA) p)).val 0 =
      (Q.recoverA.equiv p).val.2 0 := by
  rw [Q.recoverA_values]
  exact Q.profileA_key_zero p

theorem profileB_key_recover (Q : NonrectangleMatchedHeads T) (p : Q.unary.targetB) :
    (Q.profileB (Map.toImage (rawKeyMap Q.unary.targetB) p)).val 0 =
      (Q.recoverB.equiv p).val.2 0 := by
  rw [Q.recoverB_values]
  exact Q.profileB_key_zero p

theorem profileB_hom_key (Q : NonrectangleMatchedHeads T) (p : Q.unary.targetA) :
    (Q.profileB (unaryIsoHomMap Q.unary.iso (Map.toImage (rawKeyMap Q.unary.targetA) p))).val 0 =
      (Q.first.headIso.equiv (Q.recoverA.equiv p)).val.2 0 := by
  rw [Q.unary.square,Q.profileB_key_zero]
  change (Q.unary.specialB.inverseMap (Q.unary.specialB.toMap
      (Q.unary.map (Q.unary.specialA.inverseMap p)))).val.2 0 = _
  rw [Q.unary.specialB.inverse_apply,Q.unary.map_spec]
  apply congrArg (fun z => (Q.first.headIso.equiv z).val.2 0)
  apply Subtype.ext
  exact (Q.recoverA_values p).symm

end PositionedCellLabelInjection.NonrectangleMatchedHeads
end IntegrationInACVF.Section5
