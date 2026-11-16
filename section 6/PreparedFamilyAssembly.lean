import «section 6».PreparedTagBranchCompletion
import «section 6».CoveredJointPreparation

/-! Exact source transport and prefix composition for actual
prepared families, and branch frames from full retained-label slices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t k : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def PreparedSynchronizedFamily.changeSource
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hPC : ∀ i,(P i).carrier ⊆ C.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) (hAC : A=C) :
    PreparedSynchronizedFamily (G := G) C P hPC := by
  cases hAC
  exact F

def SynchronizedTagBranchFrame.of_slice
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (U : DefSet (rawRVSpace (M := M) r) S) :
    SynchronizedTagBranchFrame (focusActive A U) (fun i => focusActive (P i) U) where
  ambient := A
  pieces := P
  tags := U
  proper := hA
  doublyBounded := hD
  pieces_subset := hPA
  pieces_proper := hP
  source_eq := rfl
  pieces_eq _ := rfl
  outside_tagged p hp z hz hTags _ := hTag p hp z hz hTags

def PreparedSynchronizedFamily.precompose
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    {hPB : ∀ i,(f.restrict (hPA i)).image.carrier ⊆ B.carrier}
    (F : PreparedSynchronizedFamily (G := G) B (fun i => (f.restrict (hPA i)).image) hPB)
    (h : SynchronizedCentripetalChain (G := G) I A B f P) :
    PreparedSynchronizedFamily (G := G) A P hPA where
  arity := F.arity
  target := F.target
  map := F.map.comp f
  chain := .comp P hPA h F.chain
  proper := F.proper
  doublyBounded := F.doublyBounded
  pullback := F.pullback
  prepared i := by
    have he : ((F.map.comp f).restrict (hPA i)).image=(F.map.restrict (hPB i)).image := by
      apply defSet_eq_of_carrier_eq
      ext z
      constructor
      · rintro ⟨p,rfl⟩
        exact ⟨⟨(f ⟨p.val,hPA i p.property⟩).val,⟨p,rfl⟩⟩,rfl⟩
      · rintro ⟨p,rfl⟩
        obtain ⟨a,ha⟩ := p.property
        refine ⟨a,?_⟩
        exact congrArg (fun b : B => (F.map b).val) (Subtype.ext ha)
    rw [he]
    exact F.prepared i

end DiamondIntegral.Section6
