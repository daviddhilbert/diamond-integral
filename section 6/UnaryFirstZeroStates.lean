import «section 6».UnaryCorePlans
import «section 6».LiveOrdinaryFocusPointMaps
import «section 6».OrdinaryUniformCoreRadii
import «section 6».OrdinaryPullbackRealization

/-! Exact invariants for a prescribed-core first-zero induction. The
ordinary comparison is asserted only on the live locus. Every original
core has its actual full affine chart; once frozen its centre has the
prescribed endpoint value. Initial states are constructed, not assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure UnaryFirstZeroState (hc : CanonicalStructure.IsCanonical (M := M)) (K : UnaryCorePlan A₀)
    {r s : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) where
  source_pullback : IsRVPullback A₀.carrier
  arity : ℕ
  frame : LiveOrdinaryUnaryFrame hc A
    (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT) arity
  pullback : IsRVPullback frame.current.carrier
  map : Map A₀ frame.current
  chain : UnaryRelativeApertureChain (G := G) A₀ frame.current map
  ordinaryMap : Map A₀ (originalBaseOrdinarySet hc A
    (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT))
  live_agrees : ∀ a : A₀,∀ hLive : (map a).val.2 ∈ frame.liveLabels.carrier,
    frame.oldMap ⟨(map a).val,(map a).property,hLive⟩=ordinaryMap a
  zero_cover : ∀ a : A₀,(T.toMap (ordinaryMap a)).val.1 0=(0 : VF M) ↔ a.val ∈ K.centres.carrier
  core_chart : ∀ p : K.centres,UnaryCoreChart map (K.centre p) (K.radius p)
  centre_status : ∀ p : K.centres,(map (K.centre p)).val.2 ∈ frame.liveLabels.carrier ↔
    (ordinaryMap (K.centre p)).val.1 0≠(0 : VF M)
  frozen_value : ∀ p : K.centres,(map (K.centre p)).val.2 ∉ frame.liveLabels.carrier →
    vfValue ((map (K.centre p)).val.1 0)=(K.radius p).val
  future_bound : ∀ p : K.centres,ordinaryChainPointRadius T (ordinaryMap (K.centre p))<K.radius p
  outside_exact : ∀ a : A₀,(map a).val.2 ∈ frame.liveLabels.carrier ↔
    ¬ ∃ p : K.centres,(map (K.centre p)).val.2 ∉ frame.liveLabels.carrier ∧ a.val ∈ K.disc p

namespace UnaryFirstZeroState

def initial (hc : CanonicalStructure.IsCanonical (M := M)) (K : UnaryCorePlan A₀)
    {s : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r₀}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (hSub : A₀.carrier ⊆ SpecialTransformations.Section5.carrier A)
    (hProper : ProperInvariant S A₀.carrier) (hDB : VFDoublyBounded A₀.carrier)
    (hPullback : IsRVPullback A₀.carrier)
    (hTag : ∀ a ∈ A₀.carrier,∀ b ∈ A₀.carrier,a.2=b.2 → tupleRV M a.1=tupleRV M b.1)
    (hCover : ∀ a : A₀,(T.toMap ⟨a.val,hSub a.property⟩).val.1 0=(0 : VF M) ↔ a.val ∈ K.centres.carrier)
    (hBound : ∀ p : K.centres,ordinaryChainPointRadius T ⟨p.val,hSub (K.subset p.property)⟩<K.radius p) :
    UnaryFirstZeroState (G := G) hc K T hT := by
  let F := originalOrdinaryFocusFrame (hc := hc)
    (hA := SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT)
    A₀ hSub hProper hDB hTag
  let X := LiveOrdinaryUnaryFrame.ofFrame F
    (originalOrdinaryFocusFrame_labelsFaithful A₀ hSub hProper hDB hTag)
  refine {
    source_pullback := hPullback
    arity := r₀
    frame := X
    pullback := hPullback
    map := Map.id A₀
    chain := .original (.identity A₀ hProper)
    ordinaryMap := Map.inclusion hSub
    live_agrees := ?_
    zero_cover := hCover
    core_chart := fun p => UnaryCoreChart.identity (K.centre p) (K.radius p)
    centre_status := ?_
    frozen_value := ?_
    future_bound := hBound
    outside_exact := ?_ }
  · intro a hLive
    exact Subtype.ext rfl
  · intro p
    exact ⟨fun _ => K.centre_nonzero p,fun _ => Set.mem_univ _⟩
  · intro p hNot
    exact (hNot (Set.mem_univ _)).elim
  · intro a
    constructor
    · intro hLive
      rintro ⟨p,hNot,hDisc⟩
      exact hNot (Set.mem_univ _)
    · intro hNo
      exact Set.mem_univ _

end UnaryFirstZeroState
end DiamondIntegral.Section6
