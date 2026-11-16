import «section 6».OrdinaryRealizationPullbacks
import «section 6».UnaryRelativeApertureChains

/-! An ordinary comparison is required only on the live part of a unary
preparation. Entire retained-label fibres may already have been frozen
as full RV discs. This avoids imposing a false VF-identity certificate
on finite cores whose zero value has already been moved to an endpoint.
The terminal RV-pullback assembly is proved from the actual old range. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}

structure LiveOrdinaryUnaryFrame
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) R 1 r)
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A)) (q : ℕ) where
  current : DefSet (rawMixedSpace (M := M) 1 q) S
  liveLabels : DefSet (rawRVSpace (M := M) q) S
  oldMap : Map (focusActive current liveLabels) (originalBaseOrdinarySet hc A hA)
  labels : Fin r → Fin q
  point : ∀ p : focusActive current liveLabels,(oldMap p).val=(p.val.1,p.val.2 ∘ labels)
  proper : ProperInvariant S current.carrier
  doublyBounded : VFDoublyBounded current.carrier
  tagged : ∀ p ∈ current.carrier,∀ z ∈ current.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1
  faithful : ∀ p z : focusActive current liveLabels,
    SpecialTransformations.Section5.SameRV (oldMap p).val (oldMap z).val → p.val.2=z.val.2
  frozenPullback : IsRVPullback {p | p ∈ current.carrier ∧ p.2 ∉ liveLabels.carrier}

namespace LiveOrdinaryUnaryFrame
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}

def liveFrame (X : LiveOrdinaryUnaryFrame hc A hA q) : OrdinaryUnaryFocusFrame hc A hA q where
  source := focusActive X.current X.liveLabels
  oldMap := X.oldMap
  labels := X.labels
  point := X.point
  proper := focusActive_properInvariant X.current X.proper X.liveLabels
  doublyBounded := by
    obtain ⟨γ,hγ⟩ := X.doublyBounded
    exact ⟨γ,fun p hp => hγ p hp.1⟩
  tagged := fun p hp z hz he => X.tagged p hp.1 z hz.1 he

theorem liveFrame_faithful (X : LiveOrdinaryUnaryFrame hc A hA q) : X.liveFrame.labelsFaithful :=
  X.faithful

def oldRange (X : LiveOrdinaryUnaryFrame hc A hA q) : Set (Mixed M 1 r) :=
  Set.range (fun p : focusActive X.current X.liveLabels => (X.oldMap p).val)

theorem live_rvPullback (X : LiveOrdinaryUnaryFrame hc A hA q)
    (hOld : IsRVPullback X.oldRange) : IsRVPullback (focusActive X.current X.liveLabels).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro z hz
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff (focusActive X.current X.liveLabels).carrier z).mp hz
  let a : focusActive X.current X.liveLabels := ⟨p,hp⟩
  let oldZ : Mixed M 1 r := (z.1,z.2 ∘ X.labels)
  have hOldVF : tupleRV M (X.oldMap a).val.1=tupleRV M oldZ.1 := by
    rw [X.point a]
    exact hVF
  have hOldRV : (X.oldMap a).val.2=oldZ.2 := by
    rw [X.point a]
    exact congrArg (fun u => u ∘ X.labels) hRV
  have hzOld : oldZ ∈ X.oldRange :=
    rvPullback_mem_of_sameRV hOld (Set.mem_range_self a) hOldVF hOldRV
  obtain ⟨b,hb⟩ := hzOld
  change (X.oldMap b).val=oldZ at hb
  have hSame : SpecialTransformations.Section5.SameRV (X.oldMap b).val (X.oldMap a).val := by
    apply (ordinary_sameRV_iff _ _).mpr
    rw [hb]
    exact ⟨hOldVF.symm,hOldRV.symm⟩
  have hTags : b.val.2=z.2 := (X.faithful b a hSame).trans hRV
  have hField : b.val.1=z.1 :=
    (congrArg Prod.fst (X.point b)).symm.trans (congrArg Prod.fst hb)
  have he : b.val=z := Prod.ext hField hTags
  exact he ▸ b.property

theorem current_rvPullback (X : LiveOrdinaryUnaryFrame hc A hA q)
    (hOld : IsRVPullback X.oldRange) : IsRVPullback X.current.carrier := by
  have hLive := X.live_rvPullback hOld
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro z hz
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff X.current.carrier z).mp hz
  by_cases hl : p.2 ∈ X.liveLabels.carrier
  · exact (rvPullback_mem_of_sameRV hLive ⟨hp,hl⟩ hVF hRV).1
  · exact (rvPullback_mem_of_sameRV X.frozenPullback ⟨hp,hl⟩ hVF hRV).1

def ofFrame (X : OrdinaryUnaryFocusFrame hc A hA q) (hFaithful : X.labelsFaithful) :
    LiveOrdinaryUnaryFrame hc A hA q where
  current := X.source
  liveLabels := DefSet.univ (rawRVSpace (M := M) q) S
  oldMap := X.oldMap.comp (Map.inclusion (fun _ hp => hp.1))
  labels := X.labels
  point p := X.point ⟨p.val,p.property.1⟩
  proper := X.proper
  doublyBounded := X.doublyBounded
  tagged := X.tagged
  faithful p z h := hFaithful ⟨p.val,p.property.1⟩ ⟨z.val,z.property.1⟩ h
  frozenPullback := by
    have he : {p : Mixed M 1 q | p ∈ X.source.carrier ∧
        p.2 ∉ (DefSet.univ (rawRVSpace (M := M) q) S).carrier}=∅ := by
      ext p
      simp only [DefSet.univ,Set.mem_univ,not_true_eq_false,and_false,Set.mem_empty_iff_false,Set.mem_setOf_eq]
    rw [he]
    apply Set.Subset.antisymm _ (subset_rvHull _)
    intro z hz
    obtain ⟨p,hp,_,_⟩ := (mem_rvHull_iff (∅ : Set (Mixed M 1 q)) z).mp hz
    exact hp.elim

end LiveOrdinaryUnaryFrame
end DiamondIntegral.Section6
