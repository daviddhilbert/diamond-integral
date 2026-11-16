import «section 6».GraphFibres

/-! The clopen graph-domain step used in Lemma 6.7. Every piece of an
open partition of a clopen set is closed, even for an infinite index set. -/

namespace DiamondIntegral.Section6

theorem open_partition_piece_isClopen {X I : Type*} [TopologicalSpace X]
    (D : Set X) (hD : IsClopen D) (P : I → Set X)
    (hsub : ∀ i, P i ⊆ D) (hopen : ∀ i, IsOpen (P i))
    (hcover : ∀ x ∈ D, ∃ i, x ∈ P i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (i : I) : IsClopen (P i) := by
  classical
  have he : (P i)ᶜ = Dᶜ ∪ ⋃ j : {j // j ≠ i}, P j.val := by
    ext x
    constructor
    · intro hx
      by_cases hxD : x ∈ D
      · obtain ⟨j,hj⟩ := hcover x hxD
        have hji : j ≠ i := fun he => hx (he ▸ hj)
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
      · exact Or.inl hxD
    · rintro (hx | hx)
      · exact fun hxi => hx (hsub i hxi)
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
        exact fun hxi => Set.disjoint_left.mp (hdisjoint j.val i j.property) hj hxi
  refine ⟨isOpen_compl_iff.mp ?_,hopen i⟩
  rw [he]
  exact hD.isClosed.isOpen_compl.union (isOpen_iUnion (fun j => hopen j.val))

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem graphFibreSource_isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hA : ProperInvariant S A.carrier)
    (hopen : ∀ u v, IsOpen (graphFibreSource f u v))
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    IsClopen (graphFibreSource f u v) :=
  open_partition_piece_isClopen (vfFibre A.carrier u) (hA.clopen_fibres hv u)
    (graphFibreSource f u) (graphFibreSource_subset f u) (hopen u)
    (fun _ h => graphFibreSource_cover f u h) (graphFibreSource_disjoint f u) v

theorem graphFibreRange_isClopen_of_bijective
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hf : Function.Bijective f) (hB : ProperInvariant S B.carrier)
    (hopen : ∀ u v, IsOpen (graphFibreRange f u v))
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    IsClopen (graphFibreRange f u v) :=
  open_partition_piece_isClopen (vfFibre B.carrier v) (hB.clopen_fibres hv v)
    (fun u => graphFibreRange f u v) (fun u => graphFibreRange_subset f u v) (fun u => hopen u v)
    (fun _ h => graphFibreRange_cover f hf.surjective v h)
    (graphFibreRange_disjoint f hf.injective v) u

end DiamondIntegral.Section6
