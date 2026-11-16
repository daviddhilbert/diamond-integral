import «section 6».OrdinaryUnaryRelations

/-! Lemma 6.16 for the full original-base definable membership relation.
The source is literally unary VF; the RV output arity is arbitrary.
The actual ordinary special bijection and both raw map graphs are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- The powerset-valued contraction in Lemma 6.16, including empty values.
The supplied relation is prepared simultaneously with source membership. -/
theorem lemma_6_16
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) 1 0) S) (R : DefSet (rawMixedSpace (M := M) 1 k) S) :
    ∃ r : ℕ, ∃ B : SpecialTransformations.Section5.DefSet (M := M) S 1 r,
      ∃ T : SpecialTransformations.Section5.SpecialBijection (toOrdinarySet hc A) B,
      Function.Bijective (fromOrdinaryMap hc T.toMap) ∧
      IsRVPullback (fromOrdinarySet hc B).carrier ∧
      ∀ p q : fromOrdinarySet hc B, rvCoordinates M p.val = rvCoordinates M q.val →
        ∀ u : Fin k → RVInfinity M,
          (((fromOrdinaryMap hc T.inverseMap p).val.1,u) ∈ R.carrier ↔
            ((fromOrdinaryMap hc T.inverseMap q).val.1,u) ∈ R.carrier) := by
  let R' := toOrdinarySet hc R
  obtain ⟨r,B,T,hB,hR⟩ := Ordinary.unary_relation_preparation h00 (toOrdinarySet hc A)
    (SpecialTransformations.Section5.rawUnarySet R') (SpecialTransformations.Section5.rawUnarySet_definable R')
  refine ⟨r,B,T,T.bijective,(ordinary_pullback_iff _).mp hB,?_⟩
  intro p q hpq u
  have hPQ : SpecialTransformations.Section5.SameRV p.val q.val :=
    (ordinary_sameRV_iff _ _).mpr (Prod.mk.inj hpq)
  have h := hR p q hPQ (rvValues u) (fun i => (u i).property)
  exact (SpecialTransformations.Section5.mem_rawUnarySet_values R'
    ((fromOrdinaryMap hc T.inverseMap p).val.1,u)).symm.trans
      (h.trans (SpecialTransformations.Section5.mem_rawUnarySet_values R'
        ((fromOrdinaryMap hc T.inverseMap q).val.1,u)))

end DiamondIntegral.Section6
