import IntegrationSection5.UniformTraceProjection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.UniformRelativeTrace
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem restrict_source (T : UniformRelativeTrace S n A B) :
    ∀ (H : DefSet (M := M) S n m) (hHA : carrier H ⊆ carrier A),
    ∃ K : DefSet (M := M) S n l, ∃ W : UniformRelativeTrace S n H K,
      ∀ p : H, (W.toMap p).val = (T.toMap ⟨p.val,hHA p.property⟩).val := by
  induction T with
  | nil A =>
    intro H hHA
    exact ⟨H,.nil H,fun _ => rfl⟩
  | @canonical m l A B i tail ih =>
    intro H hHA
    let H' := coordinateCanonicalImage H i
    let can := coordinateCanonicalBijection H i
    have hSub : carrier H' ⊆ carrier (coordinateCanonicalImage A i) := by
      rintro q ⟨p,rfl⟩
      exact ⟨⟨p.val,hHA p.property⟩,rfl⟩
    obtain ⟨K,W,hW⟩ := ih H' hSub
    refine ⟨K,.canonical i W,?_⟩
    intro p
    change (W.toMap (can p)).val = _
    exact hW (can p)
  | @focus m l A B i k D tail ih =>
    intro H hHA
    let F := D.projectionPullback id Function.injective_id id (fun p hp => hHA hp)
    have hSub : carrier F.image ⊆ carrier D.image := by
      rintro q ⟨p,rfl⟩
      exact ⟨⟨p.val,hHA p.property⟩,rfl⟩
    obtain ⟨K,W,hW⟩ := ih F.image hSub
    refine ⟨K,.focus F W,?_⟩
    intro p
    change (W.toMap (F.toImage p)).val = _
    exact hW (F.toImage p)

end IntegrationInACVF.Section5.UniformRelativeTrace
