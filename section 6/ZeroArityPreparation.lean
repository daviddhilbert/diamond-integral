import «section 6».SpecialCovariantRestrictions

/-! The zero-VF-arity case of simultaneous proper preparation. The
empty field tuple is a singleton, so every ambient set and every piece
is already an RV-pullback. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem zero_arity_rvPullback (A : Set (Mixed M 0 r)) : IsRVPullback A := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff A q).mp hq
  have he : p = q := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact hRV
  exact he ▸ hp

theorem lemma_6_19_zero_arity (h00 : M ⊨ Axioms.ACVF00)
    (A : DefSet (rawMixedSpace (M := M) 0 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 0 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    SpecialCovariantChain (G := G) A A (Map.id A) ∧ VFDoublyBounded A.carrier ∧ IsRVPullback A.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) ((Map.id A).restrict (hCA i)).image
        ((Map.id A).restrict (hCA i)).toImage ∧ IsRVPullback ((Map.id A).restrict (hCA i)).image.carrier := by
  refine ⟨.identity A hA,⟨1,fun _ _ i => i.elim0⟩,zero_arity_rvPullback _,fun i => ?_⟩
  exact ⟨(SpecialCovariantChain.identity (G := G) (C i) (hC i)).restriction_of_liesOver h00
    (Map.id A) (hCA i) (fun _ => rfl),zero_arity_rvPullback _⟩

end DiamondIntegral.Section6
