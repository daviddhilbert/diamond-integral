import «section 6».ContinuousRVFamilyMaps

/-! Exact complete raw graphs of the actual family maps, with the
current source restriction retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m : ℕ}

theorem rvFamilyMap_graph_code (A : DefSet (rawMixedSpace (M := M) n r) S)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (rvVFGraph f)) :
    (rawMixedSpace n r).relation (rawVFSpace m) (rvFamilyMap A f hf).graph=
      {z | z ∘ Sum.inl ∈ (rawMixedSpace n r).preimage A.carrier ∧
        z ∘ rvFamilyGraphIndex n r m ∈ rvVFGraph f} := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) m
  have hRelation := rvVFGraph_relation_code f
  ext z
  constructor
  · rintro ⟨hx,hy,p,hp,hfValue⟩
    refine ⟨⟨hx,hp ▸ p.property⟩,?_⟩
    apply (Set.ext_iff.mp hRelation z).mp
    refine ⟨hx,hy,?_⟩
    change f (P.decode ⟨z ∘ Sum.inl,hx⟩).2 (P.decode ⟨z ∘ Sum.inl,hx⟩).1=Q.decode ⟨z ∘ Sum.inr,hy⟩
    rw [← hp]
    exact hfValue
  · rintro ⟨hA,hFamily⟩
    obtain ⟨hx,hy,hValue⟩ := (Set.ext_iff.mp hRelation z).mpr hFamily
    obtain ⟨hx',hSource⟩ := hA
    exact ⟨hx,hy,⟨⟨P.decode ⟨z ∘ Sum.inl,hx⟩,hSource⟩,rfl,hValue⟩⟩

end DiamondIntegral.Section6
