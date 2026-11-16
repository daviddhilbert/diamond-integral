import «section 6».FiniteDefSetUnions

/-! Finite intersections inside an actual definable domain, including
the empty family. All representatives are kept in the defining graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M}

def finiteDefSetIntersection {P : Space LRV M} {I : Type} [Finite I]
    (A : DefSet P S) (C : I → DefSet P S) : DefSet P S where
  carrier := {x | x ∈ A.carrier ∧ ∀ i, x ∈ (C i).carrier}
  definable := by
    have h := Set.Definable.inter
      (show S.Definable LRV (P.preimage A.carrier) from A.definable)
      (Set.definable_iInter_of_finite (fun i => (C i).definable))
    change S.Definable LRV (P.preimage {x | x ∈ A.carrier ∧ ∀ i, x ∈ (C i).carrier})
    convert h using 1
    ext z
    simp only [Space.preimage,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    constructor
    · rintro ⟨hz,hA,hC⟩
      exact ⟨⟨hz,hA⟩,fun i => ⟨hz,hC i⟩⟩
    · rintro ⟨⟨hz,hA⟩,hC⟩
      exact ⟨hz,hA,fun i => (hC i).2⟩

end DiamondIntegral.Section6
