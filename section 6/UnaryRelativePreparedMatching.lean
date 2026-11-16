import «section 6».UnaryFirstZeroPairedFibres
import «section 6».UnaryRelativeRetainedTags

/-! Actual source and target auxiliary preparations together with the
literal global conjugate taking whole prepared label fibres to whole
prepared label fibres. The record contains no supplied disc-matching
witness: its constructor uses the completed first-zero states. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r₀ s₀ : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure UnaryRelativePreparedMatching
    (A : DefSet (rawMixedSpace (M := M) 1 r₀) S) (B : DefSet (rawMixedSpace (M := M) 1 s₀) S) (f : Map A B) where
  sourceArity : ℕ
  targetArity : ℕ
  source : DefSet (rawMixedSpace (M := M) 1 sourceArity) S
  target : DefSet (rawMixedSpace (M := M) 1 targetArity) S
  sourceMap : Map A source
  targetMap : Map B target
  sourceChain : UnaryRelativeApertureChain (G := G) A source sourceMap
  targetChain : UnaryRelativeApertureChain (G := G) B target targetMap
  sourceProper : ProperInvariant S source.carrier
  targetProper : ProperInvariant S target.carrier
  sourceBounded : VFDoublyBounded source.carrier
  targetBounded : VFDoublyBounded target.carrier
  sourcePullback : IsRVPullback source.carrier
  targetPullback : IsRVPullback target.carrier
  sourceTagged : ∀ p ∈ source.carrier,∀ q ∈ source.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1
  targetTagged : ∀ p ∈ target.carrier,∀ q ∈ target.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1
  map : Map source target
  bijective : Function.Bijective map
  commutes : ∀ a : A,map (sourceMap a)=targetMap (f a)
  wholeFibres : MapsWholeTagFibres map

variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {B₀ : DefSet (rawMixedSpace (M := M) 1 s₀) S}

def relativePreparedMatchingOfTerminal
    {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀} {L : UnaryCorePlan B₀}
    {R Q : Set M} {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) Q 1 s}
    {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S) (SpecialTransformations.Section5.carrier A)}
    {hB : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S) (SpecialTransformations.Section5.carrier B)}
    (Z : UnaryFirstZeroState (G := G) hc K (.nil A) hA)
    (Y : UnaryFirstZeroState (G := G) hc L (.nil B) hB)
    (f : Map A₀ B₀) (hf : Function.Bijective f) (h00 : M ⊨ Axioms.ACVF00)
    (C : K.centres → L.centres) (hC : Function.Surjective C)
    (hPaired : ∀ (p : K.centres) (a : A₀),a.val ∈ K.disc p ↔ (f a).val ∈ L.disc (C p))
    (hOrdinary : ∀ a b : A₀,
      SpecialTransformations.Section5.SameRV (Z.ordinaryMap a).val (Z.ordinaryMap b).val ↔
        SpecialTransformations.Section5.SameRV (Y.ordinaryMap (f a)).val (Y.ordinaryMap (f b)).val) :
    UnaryRelativePreparedMatching (G := G) A₀ B₀ f where
  sourceArity := Z.arity
  targetArity := Y.arity
  source := Z.frame.current
  target := Y.frame.current
  sourceMap := Z.map
  targetMap := Y.map
  sourceChain := Z.chain
  targetChain := Y.chain
  sourceProper := Z.frame.proper
  targetProper := Y.frame.proper
  sourceBounded := Z.frame.doublyBounded
  targetBounded := Y.frame.doublyBounded
  sourcePullback := Z.pullback
  targetPullback := Y.pullback
  sourceTagged := Z.frame.tagged
  targetTagged := Y.frame.tagged
  map := firstZeroConjugate Z Y f h00
  bijective := firstZeroConjugate_bijective Z Y f h00 hf
  commutes := firstZeroConjugate_at Z Y f h00
  wholeFibres := firstZeroConjugate_whole_fibres Z Y f C hC hPaired h00 hf hOrdinary

end DiamondIntegral.Section6
