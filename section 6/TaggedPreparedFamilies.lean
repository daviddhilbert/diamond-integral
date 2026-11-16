import «section 6».PreparedFamilyAssembly
import «section 6».CentripetalPullbackPreservation

/-! A prepared synchronized family can finish with a tagged target
by one permitted regularization. All full protected images remain
prepared, supporting successive whole-label branch extensions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def prepared_regularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (hP : ∀ i,ProperInvariant S (P i).carrier) (hPRP : ∀ i,IsRVPullback (P i).carrier) :
    PreparedSynchronizedFamily (G := G) A P hPA where
  arity := n+r
  target := (regularizeMap A).image
  map := regularization A
  chain := .regularize A hA hD P hPA hP (fun i => hD.mono (hPA i))
  proper := regularization_properInvariant h00 hc hκ hs hv A hA hD
  doublyBounded := regularized_vfDoublyBounded hD
  pullback := regularization_rvPullback A hRP
  prepared i := by
    have he : ((regularization A).restrict (hPA i)).image=(regularizeMap (P i)).image :=
      defSet_eq_of_carrier_eq rfl
    rw [he]
    exact regularization_rvPullback (P i) (hPRP i)

def PreparedSynchronizedFamily.taggedTarget
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) : PreparedSynchronizedFamily (G := G) A P hPA :=
  (prepared_regularization h00 hc hκ hs hv F.target F.proper F.doublyBounded F.pullback
    (fun i => (F.map.restrict (hPA i)).image)
    (fun i z hz => by obtain ⟨p,hp⟩ := hz; exact hp ▸ (F.map.restrict (hPA i) p).property)
    (fun i => ((F.chain.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv)
    F.prepared).precompose hPA F.chain

theorem PreparedSynchronizedFamily.taggedTarget_tagged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) :
    ∀ p ∈ (F.taggedTarget h00 hc hκ hs hv).target.carrier,
    ∀ z ∈ (F.taggedTarget h00 hc hκ hs hv).target.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
  change ∀ p ∈ (regularizeMap F.target).image.carrier,
    ∀ z ∈ (regularizeMap F.target).image.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1
  rw [regularization_carrier]
  exact regularized_tagged _

end DiamondIntegral.Section6
