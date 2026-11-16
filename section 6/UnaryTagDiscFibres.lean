import «section 6».RVTagMatching

/-! Every nonempty old-tag fiber of a tagged doubly bounded unary
RV-pullback is exactly its full centered RV disc. This identifies the
constructed tag quotient with the actual disc quotient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

theorem unary_tag_fiber_eq_centered_disc
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : IsRVPullback A.carrier)
    (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (p : A) :
    vfFibre A.carrier p.val.2 = {x : Fin 1 → VF M | x 0 ∈
      centeredGammaDisc (p.val.1 0) (finiteValue (p.val.1 0) (hD.nonzero p.property 0))} := by
  have hp0 := hD.nonzero p.property 0
  ext x
  rw [Set.mem_setOf_eq,mem_centeredGammaDisc]
  change (x,p.val.2) ∈ A.carrier ↔ vfValue (p.val.1 0) < vfValue (x 0-p.val.1 0)
  constructor
  · intro hx
    have hRV := congrFun (hTag (x,p.val.2) hx p.val p.property rfl) 0
    exact (rv_eq_iff_value_close hp0).mp hRV
  · intro hx
    have hRV : tupleRV M p.val.1 = tupleRV M x := by
      funext i
      fin_cases i
      exact ((rv_eq_iff_value_close hp0).mpr hx).symm
    exact rvPullback_mem_of_sameRV hA p.property hRV rfl

end DiamondIntegral.Section6
