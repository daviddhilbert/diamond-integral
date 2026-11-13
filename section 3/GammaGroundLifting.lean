import «section 3».GammaGroundVFCategories
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundObjectLift (U : GammaGroundRVObject hc ground k) : GammaGroundDefSet hc ground (rawMixedSpace (M := M) k U.arity) where
  carrier := {q | ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1}
  definable := U.volume.graph_definable.preimage (universalLiftGraphMap ground.real k U.arity)

theorem mem_gammaGroundObjectLift (U : GammaGroundRVObject hc ground k) (q : Section2.Mixed M k U.arity) :
    q ∈ (gammaGroundObjectLift U).carrier ↔
      ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1 := Iff.rfl

theorem gammaGroundObjectLift_finite_rv_fibres (U : GammaGroundRVObject hc ground k) (a : Fin k → Section2.VF M) :
    {t | (a, t) ∈ (gammaGroundObjectLift U).carrier}.Finite := by
  let T : Set (Fin U.arity → CanonicalRV.RVSort M) := {t | (a, t) ∈ (gammaGroundObjectLift U).carrier}
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

def gammaGroundObjectLiftVF [TopologicalSpace (Section2.VF M)] (U : GammaGroundRVObject hc ground k) : GammaGroundVFObject hc ground k :=
  ⟨k, U.arity, gammaGroundObjectLift U, vf_dimension_le_arity _, gammaGroundObjectLift_finite_rv_fibres U⟩

theorem gammaGroundObjectLift_vf_coordinates_nonzero (U : GammaGroundRVObject hc ground k)
    (q : Section2.Mixed M k U.arity) (hq : q ∈ (gammaGroundObjectLift U).carrier) (i : Fin k) : q.1 i ≠ 0 := by
  obtain ⟨u, _, hu⟩ := (mem_gammaGroundObjectLift U q).mp hq
  intro hz
  have hrv := congrArg (fun t => (t i).val) hu
  have hzero : (Section2.tupleRV M q.1 i).val = iRVZero := by
    rw [Section2.tupleRV, hz, Section2.rv_zero]
    rfl
  exact U.nonzero u i (hrv.trans hzero)


end DiamondIntegral.Section3
