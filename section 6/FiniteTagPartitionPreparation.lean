import «section 6».ComplementaryBranchPreparation
import «section 6».FusionBranchSlices

/-! Finite disjoint formula-choice pieces are assembled by actual
complementary branch extensions. Empty ambient and empty choice families
are handled without an inhabitedness assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem focusActive_disjoint_complement
    (A : DefSet (rawMixedSpace (M := M) n r) S) (U V : DefSet (rawRVSpace (M := M) r) S)
    (h : ∀ u ∈ V.carrier,u ∉ U.carrier) :
    focusActive (focusActive A (rvTagComplement U)) V=focusActive A V := by
  apply defSet_eq_of_carrier_eq
  ext p
  change ((p ∈ A.carrier ∧ p.2 ∉ U.carrier) ∧ p.2 ∈ V.carrier) ↔ (p ∈ A.carrier ∧ p.2 ∈ V.carrier)
  exact ⟨fun hp => ⟨hp.1.1,hp.2⟩,fun hp => ⟨⟨hp.1,h _ hp.2⟩,hp.2⟩⟩

theorem synchronized_preparation_of_finite_tag_partition
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (m : ℕ) :
    ∀ (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier)
      (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
      (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
      (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
      (U : Fin m → DefSet (rawRVSpace (M := M) r) S),
      (∀ p ∈ A.carrier,∃ i,p.2 ∈ (U i).carrier) →
      (∀ i j u,u ∈ (U i).carrier → u ∈ (U j).carrier → i=j) →
      (∀ i,Nonempty (PreparedSynchronizedFamily (G := G) (focusActive A (U i))
        (fun j => focusActive (P j) (U i)) (fun j _ hp => ⟨hPA j hp.1,hp.2⟩))) →
      Nonempty (PreparedSynchronizedFamily (G := G) A P hPA) := by
  induction m with
  | zero =>
    intro A hA hD hRP hTag P hPA hP U hCover hDisjoint hPrep
    have hEmpty : ∀ p ∈ A.carrier,False := by
      intro p hp
      obtain ⟨i,hi⟩ := hCover p hp
      exact i.elim0
    refine ⟨PreparedSynchronizedFamily.identity hA hD hRP P hPA hP (fun i => ?_)⟩
    apply Set.Subset.antisymm _ (subset_rvHull _)
    intro q hq
    obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
    exact False.elim (hEmpty p (hPA i hp))
  | succ m ih =>
    intro A hA hD hRP hTag P hPA hP U hCover hDisjoint hPrep
    obtain ⟨F⟩ := hPrep 0
    let A' := focusActive A (rvTagComplement (U 0))
    let P' (i) := focusActive (P i) (rvTagComplement (U 0))
    have hP' (i) : (P' i).carrier ⊆ A'.carrier := fun _ hp => ⟨hPA i hp.1,hp.2⟩
    have hCover' : ∀ p ∈ A'.carrier,∃ i : Fin m,p.2 ∈ (U i.succ).carrier := by
      intro p hp
      obtain ⟨j,hj⟩ := hCover p hp.1
      have hTail : ∀ j : Fin (m+1),p.2 ∈ (U j).carrier → ∃ i : Fin m,p.2 ∈ (U i.succ).carrier :=
        Fin.cases (fun h => False.elim (hp.2 h)) (fun i h => ⟨i,h⟩)
      exact hTail j hj
    have hPrep' (i : Fin m) : Nonempty (PreparedSynchronizedFamily (G := G) (focusActive A' (U i.succ))
        (fun j => focusActive (P' j) (U i.succ)) (fun j _ hp => ⟨hP' j hp.1,hp.2⟩)) := by
      obtain ⟨G'⟩ := hPrep i.succ
      have hOut : ∀ u ∈ (U i.succ).carrier,u ∉ (U 0).carrier := by
        intro u hi hZero
        exact Fin.succ_ne_zero i (hDisjoint i.succ 0 u hi hZero)
      exact ⟨G'.transportSets (focusActive_disjoint_complement A (U 0) (U i.succ) hOut).symm
        (fun j => (focusActive_disjoint_complement (P j) (U 0) (U i.succ) hOut).symm)⟩
    obtain ⟨G'⟩ := ih A' (focusActive_properInvariant A hA _) (hD.mono (fun _ hp => hp.1))
      (focusActive_rvPullback A _ hRP) (fun p hp z hz => hTag p hp.1 z hz.1)
      P' hP' (fun i => focusActive_properInvariant (P i) (hP i) _) (fun i => U i.succ) hCover'
      (fun i j u hi hj => Fin.succ_injective _ (hDisjoint i.succ j.succ u hi hj)) hPrep'
    exact synchronized_preparation_glue_complementary_tags h00 hc hκ hs hv A hA hD hRP hTag P hPA hP (U 0) F G'

end DiamondIntegral.Section6
