import «section 3».NamedVFCategories
import «section 3».TupleRVMap
import «section 3».Lifting

/-! The full-label object lift is definable over the same imaginary
names. Its dimension bound and finite RV fibres require no generation
hypothesis and no lift of an isomorphism. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Space LRV M} {p : P.Carrier} {S : Set M} {k : ℕ}

def namedObjectLift (U : NamedRVObject P p S k) : NamedDefSet P p (rawMixedSpace (M := M) k U.arity) S where
  carrier := {q | ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1}
  definable := U.volume.graph_definable.preimage (universalLiftGraphMap S k U.arity)

theorem mem_namedObjectLift (U : NamedRVObject P p S k) (q : Section2.Mixed M k U.arity) :
    q ∈ (namedObjectLift U).carrier ↔
      ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1 := Iff.rfl

theorem namedObjectLift_finite_rv_fibres (U : NamedRVObject P p S k) (a : Fin k → Section2.VF M) :
    {t | (a, t) ∈ (namedObjectLift U).carrier}.Finite := by
  let T : Set (Fin U.arity → CanonicalRV.RVSort M) := {t | (a, t) ∈ (namedObjectLift U).carrier}
  by_cases hT : T.Nonempty
  · obtain ⟨t₀, u₀, hu₀, hv₀⟩ := hT
    apply ((U.finite (U.volume u₀)).image Subtype.val).subset
    rintro t ⟨u, hu, hv⟩
    refine ⟨u, ?_, hu⟩
    exact Subtype.ext (hv.trans hv₀.symm)
  · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    change T.Finite
    rw [he]
    exact Set.finite_empty

def namedObjectLiftVF [TopologicalSpace (Section2.VF M)] (U : NamedRVObject P p S k) : NamedVFObject P p S k :=
  ⟨k, U.arity, namedObjectLift U, vf_dimension_le_arity _, namedObjectLift_finite_rv_fibres U⟩

theorem namedObjectLift_overRealCode (U : NamedRVObject P p S k) (c : P.domain) (hp : P.decode c = p) :
    (namedObjectLift U).overRealCode c hp = objectLift (U.overRealCode c hp) := rfl

theorem namedObjectLiftVF_overRealCode [TopologicalSpace (Section2.VF M)]
    (U : NamedRVObject P p S k) (c : P.domain) (hp : P.decode c = p) :
    (namedObjectLiftVF U).overRealCode c hp = objectLiftVF (U.overRealCode c hp) := rfl

theorem namedObjectLift_vf_coordinates_nonzero (U : NamedRVObject P p S k)
    (q : Section2.Mixed M k U.arity) (hq : q ∈ (namedObjectLift U).carrier) (i : Fin k) : q.1 i ≠ 0 := by
  obtain ⟨u, _, hu⟩ := (mem_namedObjectLift U q).mp hq
  intro hz
  have hrv := congrArg (fun t => (t i).val) hu
  have hzero : (Section2.tupleRV M q.1 i).val = iRVZero := by
    rw [Section2.tupleRV, hz, Section2.rv_zero]
    rfl
  exact U.nonzero u i (hrv.trans hzero)

end DiamondIntegral.Section3
