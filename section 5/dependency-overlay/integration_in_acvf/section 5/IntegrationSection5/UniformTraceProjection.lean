import IntegrationSection5.UniformRelativeTrace
import IntegrationSection5.FibreFocusProjection

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
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n N m l : ℕ}

theorem vfRVProjection_coordinateCanonical (ι : Fin n → Fin N) (ρ : Fin m → Fin l)
    (i : Fin n) (p : Point (M := M) N l) :
    vfRVProjection ι (activeCanonicalProjection ρ) (coordinateCanonical (ι i) p) =
      coordinateCanonical i (vfRVProjection ι ρ p) := by
  refine Prod.ext rfl ?_
  funext j
  cases j using Fin.addCases <;> simp [vfRVProjection,activeCanonicalProjection,coordinateCanonical,vfAt]

namespace UniformRelativeTrace
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem lift_projection (T : UniformRelativeTrace S n A B) :
    ∀ {a : ℕ} (H : DefSet (M := M) S N a) (ι : Fin n → Fin N) (hι : Function.Injective ι)
      (ρ : Fin m → Fin a) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A),
    ∃ b, ∃ K : DefSet (M := M) S N b, ∃ σ : Fin l → Fin b,
      ∃ W : UniformRelativeTrace S N H K,
        (∀ p : H, vfRVProjection ι σ (W.toMap p).val =
          (T.toMap ⟨vfRVProjection ι ρ p.val,hHA _ p.property⟩).val) ∧
        ∀ p : H, ∀ j : Fin N, (∀ i, ι i ≠ j) → vfAt (W.toMap p).val j = vfAt p.val j := by
  induction T with
  | nil A =>
    intro a H ι hι ρ hHA
    exact ⟨a,H,ρ,.nil H,fun _ => rfl,fun _ _ _ => rfl⟩
  | @canonical m l A B i tail ih =>
    intro a H ι hι ρ hHA
    let H' := coordinateCanonicalImage H (ι i)
    let can := coordinateCanonicalBijection H (ι i)
    let ρ' := activeCanonicalProjection ρ
    have hSub : ∀ q ∈ carrier H', vfRVProjection ι ρ' q ∈ carrier (coordinateCanonicalImage A i) := by
      rintro q ⟨p,rfl⟩
      have he := vfRVProjection_coordinateCanonical ι ρ i p.val
      exact he.symm ▸ (show coordinateCanonical i (vfRVProjection ι ρ p.val) ∈ carrier (coordinateCanonicalImage A i) from
        ⟨⟨vfRVProjection ι ρ p.val,hHA _ p.property⟩,rfl⟩)
    obtain ⟨b,K,σ,W,hComm,hOther⟩ := ih H' ι hι ρ' hSub
    refine ⟨b,K,σ,.canonical (ι i) W,?_,?_⟩
    · intro p
      change vfRVProjection ι σ (W.toMap (can p)).val = _
      rw [hComm]
      apply congrArg (fun z : coordinateCanonicalImage A i => (tail.toMap z).val)
      exact Subtype.ext (vfRVProjection_coordinateCanonical ι ρ i p.val)
    · intro p j hj
      exact hOther (can p) j hj
  | @focus m l A B i k D tail ih =>
    intro a H ι hι ρ hHA
    let F := D.projectionPullback ι hι ρ hHA
    have hSub : ∀ q ∈ carrier F.image, vfRVProjection ι ρ q ∈ carrier D.image := by
      rintro q ⟨p,rfl⟩
      have he := D.projectionPullback_eta ι hι ρ hHA p.val
      exact he.symm ▸ (show D.eta (vfRVProjection ι ρ p.val) ∈ carrier D.image from
        ⟨⟨vfRVProjection ι ρ p.val,hHA _ p.property⟩,rfl⟩)
    obtain ⟨b,K,σ,W,hComm,hOther⟩ := ih F.image ι hι ρ hSub
    refine ⟨b,K,σ,.focus F W,?_,?_⟩
    · intro p
      change vfRVProjection ι σ (W.toMap (F.toImage p)).val = _
      rw [hComm]
      apply congrArg (fun z : D.image => (tail.toMap z).val)
      exact Subtype.ext (D.projectionPullback_eta ι hι ρ hHA p.val)
    · intro p j hj
      exact (hOther (F.toImage p) j hj).trans (F.eta_other p.val j (hj i).symm)

end UniformRelativeTrace
end IntegrationInACVF.Section5
