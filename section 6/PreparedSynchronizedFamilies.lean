import «section 6».SynchronizedChainTransport
import «section 6».PreparedCentripetalFamilies

/-! Strong preparation witnesses retain common focus and coefficient
compatibility at every component. Forgetting that extra information
gives the existing complete simultaneous preparation witness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
structure PreparedSynchronizedFamily (A : DefSet (rawMixedSpace (M := M) n r) S)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) n arity) S
  map : Map A target
  chain : SynchronizedCentripetalChain (G := G) I A target map P
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  pullback : IsRVPullback target.carrier
  prepared : ∀ i,IsRVPullback (map.restrict (hPA i)).image.carrier


def PreparedSynchronizedFamily.toPrepared
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) : PreparedCentripetalFamily (G := G) A P hPA :=
  ⟨F.arity,F.target,F.map,F.chain.toSimultaneous,F.proper,F.doublyBounded,F.pullback,F.prepared⟩

end DiamondIntegral.Section6
