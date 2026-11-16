import «section 6».EverywhereMeasuredLiftGluing
import Section9.FiniteLabelPartition

/-! A finite original-base cover of whole label domains suffices for
everywhere measured lifting. Actual local lifts are restricted to a
disjoint refinement before gluing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_everywhere_measured_lift_of_finite_cover {I : Type} [Finite I]
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (P : I → DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hP : ∀ i,(P i).carrier ⊆ U.object.domain.carrier)
    (hCover : ∀ u : U.object.domain,∃ i,u.val ∈ (P i).carrier)
    (hLift : ∀ i,Nonempty (EverywhereMeasuredRVLift (e.restrict (P i) (hP i)))) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  obtain ⟨Q,hQP,hQCover,hDisj⟩ := exists_disjoint_definable_refinement P
  let hQ (i) : (Q i).carrier ⊆ U.object.domain.carrier := (hQP i).trans (hP i)
  have hLocal (i) : Nonempty (EverywhereMeasuredRVLift (e.restrict (Q i) (hQ i))) := by
    let F := Classical.choice (hLift i)
    exact exists_everywhere_measured_lift_restrict F (Q i) (hQP i)
  exact exists_glued_everywhere_measured_lift e Q hQ
    (fun u => hQCover u.val (hCover u)) hDisj (fun i => Classical.choice (hLocal i))

end DiamondIntegral.Section6
