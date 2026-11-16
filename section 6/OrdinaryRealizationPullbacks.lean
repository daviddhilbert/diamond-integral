import «section 6».OrdinaryLabelledRealization
import «section 6».OrdinaryFrameRestrictions
import «section 6».UnaryPullbackPreservation

/-! The actual extra RV labels of the covariant realization do not
fragment an ordinary whole-disc endpoint. This is proved from the full
label certificate and literal endpoint commutation, rather than assumed
for an arbitrary proper restricted ordinary target. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}

def OrdinaryUnaryFocusFrame.labelsFaithful (X : OrdinaryUnaryFocusFrame hc A hA q) : Prop :=
  ∀ p q : X.source,SpecialTransformations.Section5.SameRV (X.oldMap p).val (X.oldMap q).val → p.val.2=q.val.2

theorem OrdinaryUnaryFocusFrame.labelsFaithful_restrict
    (X : OrdinaryUnaryFocusFrame hc A hA q) (hX : X.labelsFaithful)
    (H : DefSet (rawMixedSpace (M := M) 1 q) S) (hH : H.carrier ⊆ X.source.carrier)
    (hProper : ProperInvariant S H.carrier) : (X.restrict H hH hProper).labelsFaithful := by
  intro p q hSame
  exact hX ⟨p.val,hH p.property⟩ ⟨q.val,hH q.property⟩ hSame

def ordinaryFrameEndpointImage (X : OrdinaryUnaryFocusFrame hc A hA q)
    (T : SpecialTransformations.Section5.Chain R 1 A B) : Set (Mixed M 1 s) :=
  Set.range (fun p : X.source => (T.toMap (X.oldMap p)).val)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem OrdinaryChainLabelledRealization.target_rvPullback
    {X : OrdinaryUnaryFocusFrame hc A hA q}
    {T : SpecialTransformations.Section5.Chain R 1 A B}
    {hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T}
    (F : OrdinaryChainLabelledRealization (G := G) X T hT)
    (h00 : M ⊨ Axioms.ACVF00) (hFaithful : X.labelsFaithful)
    (hOld : IsRVPullback (ordinaryFrameEndpointImage X T)) :
    IsRVPullback F.targetFrame.source.carrier := by
  have hPoint (p : X.source) : (T.toMap (X.oldMap p)).val=
      ((F.map p).val.1,(F.map p).val.2 ∘ F.targetFrame.labels) :=
    (F.commutes p).symm.trans (F.targetFrame.point (F.map p))
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨z,hz,hVF,hRV⟩ := (mem_rvHull_iff F.targetFrame.source.carrier q).mp hq
  obtain ⟨a,ha⟩ := (F.special.bijective h00).surjective ⟨z,hz⟩
  have haMap : (F.map a).val=z := congrArg Subtype.val ha
  let oldQ : Mixed M 1 s := (q.1,q.2 ∘ F.targetFrame.labels)
  have haOld : (T.toMap (X.oldMap a)).val=(z.1,z.2 ∘ F.targetFrame.labels) := by
    rw [hPoint a,haMap]
  have hOldVF : tupleRV M (T.toMap (X.oldMap a)).val.1=tupleRV M oldQ.1 := by
    rw [haOld]
    exact hVF
  have hOldRV : (T.toMap (X.oldMap a)).val.2=oldQ.2 := by
    rw [haOld]
    exact congrArg (fun u => u ∘ F.targetFrame.labels) hRV
  have hOldQ : oldQ ∈ ordinaryFrameEndpointImage X T :=
    rvPullback_mem_of_sameRV hOld (Set.mem_range_self a) hOldVF hOldRV
  obtain ⟨b,hbOld⟩ := hOldQ
  change (T.toMap (X.oldMap b)).val=oldQ at hbOld
  have hEndSame : SpecialTransformations.Section5.SameRV
      (T.toMap (X.oldMap b)).val (T.toMap (X.oldMap a)).val := by
    apply (ordinary_sameRV_iff _ _).mpr
    rw [hbOld]
    exact ⟨hOldVF.symm,hOldRV.symm⟩
  have hStartSame := T.sameRV_of (X.oldMap b) (X.oldMap a) hEndSame
  have hInputTags := hFaithful b a hStartSame
  have hCurrentTags := F.labelControl b a hInputTags hEndSame
  have hField : (F.map b).val.1=q.1 :=
    (congrArg (fun w : Mixed M 1 s => w.1) (hPoint b)).symm.trans
      (congrArg (fun w : Mixed M 1 s => w.1) hbOld)
  have hFull : (F.map b).val=q := Prod.ext hField
    (hCurrentTags.trans ((congrArg (fun w : Mixed M 1 F.arity => w.2) haMap).trans hRV))
  exact hFull ▸ (F.map b).property

end DiamondIntegral.Section6
