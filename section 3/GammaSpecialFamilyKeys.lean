import «section 3».GammaSpecialFamilyLifts
import «section 3».GammaFamilyKeyProjections
import IntegrationSection6.GammaPreparedFamilyKeyCharacterization

/-! The extended special preparation has exactly the existing indexed
family key domain. This identifies actual presentations and every old
label, rather than only their numerical classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a : ℕ}
variable {X : SpecialTransformations.Section5.DefSet (M := M) S p 0}
variable {Z : SpecialTransformations.Section5.DefSet (M := M) S p l}
variable {H : SpecialTransformations.Section5.DefSet (M := M) S p a}
variable {T : SpecialBijection X Z}
variable {hHX : ∀ q ∈ carrier H, (q.1,Fin.elim0) ∈ carrier X}

theorem gammaSpecialFamilyLift_key_at_source (L : GammaSpecialFamilyLift (B := B) T H hHX) (q : H) :
    gammaFamilyKeyCode L.projection (gammaChainOldLabelIndex L.special.chain)
        (flatKey (L.special.toMap q).val).2 =
      Fin.append (flatKey (T.toMap ⟨(q.val.1,Fin.elim0),hHX q.val q.property⟩).val).2 q.val.2 := by
  have hv := congrArg Prod.fst (L.square q)
  have hr := congrArg Prod.snd (L.square q)
  have ho := gammaChain_old_labels L.special.chain q
  change gammaFamilyKeyCode L.projection (gammaChainOldLabelIndex L.special.chain)
    (Fin.append (fun j => rv ((L.special.toMap q).val.1 j)) (L.special.toMap q).val.2) = _
  rw [gammaFamilyKeyCode_append]
  change (L.special.toMap q).val.2 ∘ gammaChainOldLabelIndex L.special.chain = q.val.2 at ho
  refine congrArg₂ Fin.append ?_ ho
  exact congrArg₂ Fin.append
    (congrArg (fun x : Fin p → VF (M := M) => fun j => rv (x j)) hv) hr

theorem gammaSpecialFamilyLift_key_image
    (L : GammaSpecialFamilyLift (B := B) T H hHX)
    (F : GammaFiniteRVSchema B p a 0) (G : GammaFiniteRVSchema B (p+l) a 0 (fun _ => .rv))
    (hSource : carrier H = vfSchemaSource (carrier X) F)
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (T.inverseMap q).val) G (rawPreparedKey q.val)) :
    gammaFamilyKeyCode L.projection (gammaChainOldLabelIndex L.special.chain) '' preparedKeyDomain L.target =
      indexedDomain (preparedKeyDomain Z) (fun t => G.rowDomain (rvValues t)) := by
  ext t
  constructor
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    let u := L.special.inverseMap q
    let b : X := ⟨(u.val.1,Fin.elim0),hHX u.val u.property⟩
    let c := T.toMap b
    have hu : u.val.2 ∈ F.rowDomain (rawVFParameter (T.inverseMap c).val) := by
      have he : T.inverseMap c = b := T.inverse_apply b
      rw [he]
      exact ((Set.ext_iff.mp hSource u.val).mp u.property).2
    have hrow : u.val.2 ∈ G.rowDomain (rawPreparedKey c.val) := (hRows c).domains.le hu
    have hq : L.special.toMap u = q := L.special.apply_inverse q
    rw [← hq,gammaSpecialFamilyLift_key_at_source]
    have hrow' : u.val.2 ∈ G.rowDomain (rvValues (flatKey c.val).2) := hrow
    simpa only [indexedDomain,Set.mem_setOf_eq,indexedLeft,indexedRight,Function.comp_def,
      Fin.append_left,Fin.append_right] using And.intro (show (flatKey c.val).2 ∈ preparedKeyDomain Z from ⟨c,rfl⟩) hrow'
  · intro ht
    obtain ⟨c,hc⟩ := ht.1
    let b := T.inverseMap c
    have hrow : indexedRight t ∈ F.rowDomain (rawVFParameter b.val) := by
      apply (hRows c).domains.ge
      change indexedRight t ∈ G.rowDomain (rvValues (flatKey c.val).2)
      rw [hc]
      exact ht.2
    have hb : (b.val.1,Fin.elim0) ∈ carrier X := by
      have he : (b.val.1,Fin.elim0) = b.val := Prod.ext rfl (Subsingleton.elim _ _)
      exact he.symm ▸ b.property
    let u : H := ⟨(b.val.1,indexedRight t),(Set.ext_iff.mp hSource _).mpr ⟨hb,hrow⟩⟩
    let q := L.special.toMap u
    refine ⟨(flatKey q.val).2,⟨q,rfl⟩,?_⟩
    rw [gammaSpecialFamilyLift_key_at_source]
    have he : (⟨(u.val.1,Fin.elim0),hHX u.val u.property⟩ : X) = b :=
      Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
    change Fin.append (flatKey (T.toMap ⟨(u.val.1,Fin.elim0),hHX u.val u.property⟩).val).2 (indexedRight t) = t
    rw [he,T.apply_inverse,hc]
    exact Fin.append_castAdd_natAdd

end DiamondIntegral.Section3
