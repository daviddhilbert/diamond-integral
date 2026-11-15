import «section 5».NativeFiniteRVRowObjects
import «section 5».NativeFiniteRVLiftDomains

/-! A finite label map to RV including its absorbing element represents
the paper's RV[<=k] convention. Its lift retains the zero VF coordinates.
This is finite graded bookkeeping, with the original ground unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

structure NativeWeakRVObject (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) where
  arity : ℕ
  domain : GammaGroundDefSet hc B (rawRVSpace (M := M) arity)
  volume : GammaGroundMap domain (GammaGroundDefSet.univ hc B (rawRVSpace k))
  finite : volume.FiniteFibres

def nativeWeakRVObjectLift (U : NativeWeakRVObject hc B k) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity) where
  carrier := {q | ∃ u : U.domain,u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1}
  definable := U.volume.graph_definable.preimage (universalLiftGraphMap B.real k U.arity)

theorem nativeWeakRVObjectLift_finite (U : NativeWeakRVObject hc B k) :
    ∀ a : Fin k → Section2.VF M,{t | (a,t) ∈ (nativeWeakRVObjectLift U).carrier}.Finite := by
  intro a
  let T : Set (Fin U.arity → CanonicalRV.RVSort M) := {t | (a,t) ∈ (nativeWeakRVObjectLift U).carrier}
  by_cases hT : T.Nonempty
  · obtain ⟨t₀,u₀,hu₀,hv₀⟩ := hT
    apply ((U.finite (U.volume u₀)).image Subtype.val).subset
    rintro t ⟨u,hu,hv⟩
    exact ⟨u,Subtype.ext (hv.trans hv₀.symm),hu⟩
  · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    change T.Finite
    rw [he]
    exact Set.finite_empty

end DiamondIntegral.Section5
