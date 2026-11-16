import «section 6».LiveOrdinaryUnaryFrames
import «section 6».OrdinaryFrameTransitions

/-! A legitimate canonical primitive on the whole current source also
regularizes its live comparison. The frozen complement remains a full
RV-pullback; no new arbitrary graph-grafting operation is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem OrdinaryUnaryFocusFrame.afterCanonical_faithful
    (X : OrdinaryUnaryFocusFrame hc A hA q) (hFaithful : X.labelsFaithful)
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    (X.afterCanonical h00 hκ hs hv).labelsFaithful := by
  intro p z hSame
  obtain ⟨a,rfl⟩ := (regularization_bijective X.source).surjective p
  obtain ⟨b,rfl⟩ := (regularization_bijective X.source).surjective z
  rw [X.afterCanonical_at_step h00 hκ hs hv a,X.afterCanonical_at_step h00 hκ hs hv b] at hSame
  have hOld : SpecialTransformations.Section5.SameRV (X.oldMap a).val (X.oldMap b).val :=
    (SpecialTransformations.Section5.Primitive.canonical A).sameRV_of (X.oldMap a) (X.oldMap b) hSame
  have hTags := hFaithful a b hOld
  have hVF := ((ordinary_sameRV_iff _ _).mp hOld).1
  rw [X.point a,X.point b] at hVF
  change Fin.append (tupleRV M a.val.1) a.val.2=Fin.append (tupleRV M b.val.1) b.val.2
  rw [hVF,hTags]

namespace LiveOrdinaryUnaryFrame
variable (X : LiveOrdinaryUnaryFrame hc A hA q)

def canonicalLiveLabels : DefSet (rawRVSpace (M := M) (1+q)) S :=
  selectedRVTagSet X.liveLabels (Fin.natAdd 1)

def canonicalLiveDomain : DefSet (rawMixedSpace (M := M) 1 (1+q)) S :=
  focusActive (regularizeMap X.current).image X.canonicalLiveLabels

theorem canonicalLive_eq : X.canonicalLiveDomain.carrier=
    (regularizeMap (focusActive X.current X.liveLabels)).image.carrier := by
  ext z
  constructor
  · rintro ⟨hz,hLive⟩
    rw [regularization_carrier] at hz ⊢
    obtain ⟨a,ha,rfl⟩ := hz
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    change (regularize a).2 ∘ Fin.natAdd 1 ∈ X.liveLabels.carrier at hLive
    simpa only [regularize,Function.comp_def,Fin.append_right] using hLive
  · intro hz
    rw [regularization_carrier] at hz
    obtain ⟨a,ha,rfl⟩ := hz
    refine ⟨?_,?_⟩
    · rw [regularization_carrier]
      exact ⟨a,ha.1,rfl⟩
    · change (regularize a).2 ∘ Fin.natAdd 1 ∈ X.liveLabels.carrier
      simpa only [regularize,Function.comp_def,Fin.append_right] using ha.2

def canonicalLiveInclusion : Map X.canonicalLiveDomain
    (regularizeMap (focusActive X.current X.liveLabels)).image :=
  Map.inclusion (fun p hp => (Set.ext_iff.mp X.canonicalLive_eq p).mp hp)

theorem canonical_frozen_rvPullback : IsRVPullback
    {p | p ∈ (regularizeMap X.current).image.carrier ∧ p.2 ∉ X.canonicalLiveLabels.carrier} := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro z hz
  obtain ⟨p,⟨hp,hLive⟩,hVF,hRV⟩ := (mem_rvHull_iff _ z).mp hz
  rw [regularization_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  have haLive : a.2 ∉ X.liveLabels.carrier := by
    change (regularize a).2 ∘ Fin.natAdd 1 ∉ X.liveLabels.carrier at hLive
    simpa only [regularize,Function.comp_def,Fin.append_right] using hLive
  change tupleRV M a.1=tupleRV M z.1 at hVF
  let b : Mixed M 1 q := (z.1,a.2)
  have hb : b ∈ {p | p ∈ X.current.carrier ∧ p.2 ∉ X.liveLabels.carrier} :=
    rvPullback_mem_of_sameRV X.frozenPullback ⟨ha,haLive⟩ hVF rfl
  have he : regularize b=z := by
    apply Prod.ext
    · rfl
    · change Fin.append (tupleRV M z.1) a.2=z.2
      rw [← hRV]
      change Fin.append (tupleRV M z.1) a.2=Fin.append (tupleRV M a.1) a.2
      rw [hVF]
  refine ⟨?_,?_⟩
  · rw [regularization_carrier]
    exact ⟨b,hb.1,he⟩
  · have hTail : z.2 ∘ Fin.natAdd 1=a.2 := by
      rw [← hRV]
      funext i
      exact Fin.append_right _ _ i
    change z.2 ∘ Fin.natAdd 1 ∉ X.liveLabels.carrier
    rw [hTail]
    exact haLive

def afterCanonical
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    LiveOrdinaryUnaryFrame hc (SpecialTransformations.Section5.canonicalImage A)
      (OrdinaryUnaryFocusFrame.canonicalTarget_gamma (hA := hA)) (1+q) := by
  let Y := X.liveFrame.afterCanonical h00 hκ hs hv
  refine {
    current := (regularizeMap X.current).image
    liveLabels := X.canonicalLiveLabels
    oldMap := Y.oldMap.comp X.canonicalLiveInclusion
    labels := Y.labels
    point := fun p => Y.point (X.canonicalLiveInclusion p)
    proper := regularization_properInvariant h00 hc hκ hs hv X.current X.proper X.doublyBounded
    doublyBounded := regularized_vfDoublyBounded X.doublyBounded
    tagged := ?_
    faithful := ?_
    frozenPullback := X.canonical_frozen_rvPullback }
  · rw [regularization_carrier]
    exact regularized_tagged _
  · intro p z hSame
    exact X.liveFrame.afterCanonical_faithful X.liveFrame_faithful h00 hκ hs hv
      (X.canonicalLiveInclusion p) (X.canonicalLiveInclusion z) hSame

end LiveOrdinaryUnaryFrame
end DiamondIntegral.Section6
