import «section 6».ProjectedFocusComponents

/-! An actual projected focus whose leading term belongs to its
source coordinate inherits a lower valuation bound from that source.
This applies even when the focus image is infinite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {U : DefSet (rawRVSpace (M := M) r) S}

theorem projectedFocus_image_lowerBound
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hA : VFDoublyBounded A.carrier)
    (hFocusRV : ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last n))) :
    ∃ η : Gamma M, ∀ a ∈ scalarFocusImage f, η.val ≤ vfValue a := by
  obtain ⟨δ,hδ⟩ := hA
  refine ⟨δ⁻¹,?_⟩
  rintro a ⟨p,rfl⟩
  obtain ⟨q,hq⟩ := p.property
  have hp : p = (⟨(Fin.init q.val.1,q.val.2),⟨q,rfl⟩⟩ : projectedActiveDomain A U) :=
    Subtype.ext hq.symm
  rw [hp]
  have hRV := hFocusRV q.val q.property.1 q.property.2
  have hAt := congrFun (totalFocusFibre_at f q.val.2 (Fin.init q.val.1) (by exact ⟨q,rfl⟩)) 0
  rw [hAt] at hRV
  have hValue := congrArg Values.vrv hRV
  change vfValue ((f ⟨(Fin.init q.val.1,q.val.2),⟨q,rfl⟩⟩).val 0) = vfValue (q.val.1 (Fin.last n)) at hValue
  rw [hValue]
  exact (hδ q.val q.property.1 (Fin.last n)).1

end DiamondIntegral.Section6
