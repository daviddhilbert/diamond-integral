import IntegrationSection5.GammaTraceProjection
import IntegrationSection5.UniformTraceRestriction

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
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem gamma_restrict_source (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    ∀ (H : DefSet (M := M) S n m) (hHA : carrier H ⊆ carrier A) (hH : GammaSetDefinable G (carrier H)),
    ∃ K : DefSet (M := M) S n l, ∃ W : UniformRelativeTrace S n H K, GammaUniformTrace (G := G) W ∧
      ∀ p : H, (W.toMap p).val = (T.toMap ⟨p.val,hHA p.property⟩).val := by
  induction T with
  | nil A =>
    intro H hHA hH
    exact ⟨H,.nil H,hH,fun _ => rfl⟩
  | @canonical m l A B i tail ih =>
    intro H hHA hH
    let H' := coordinateCanonicalImage H i
    let can := coordinateCanonicalBijection H i
    have hSub : carrier H' ⊆ carrier (coordinateCanonicalImage A i) := by
      rintro q ⟨p,rfl⟩
      exact ⟨⟨p.val,hHA p.property⟩,rfl⟩
    obtain ⟨K,W,hWG,hW⟩ := ih hT.2 H' hSub (gamma_coordinateCanonicalImage H hH i)
    refine ⟨K,.canonical i W,⟨hH,hWG⟩,?_⟩
    intro p
    change (W.toMap (can p)).val = _
    exact hW (can p)
  | @focus m l A B i k D tail ih =>
    intro H hHA hH
    let F := D.projectionPullback id Function.injective_id id (fun p hp => hHA hp)
    have hSub : carrier F.image ⊆ carrier D.image := by
      rintro q ⟨p,rfl⟩
      exact ⟨⟨p.val,hHA p.property⟩,rfl⟩
    have hFG := GammaFibreFocusDefinable.projectionPullback D hT.2.1 hH id Function.injective_id id (fun p hp => hHA hp)
    let e : GammaIso G (carrier H) (carrier F.image) :=
      ⟨Equiv.ofBijective F.toImage F.toImage_bijective,gamma_fibre_eta_graph F hH hFG⟩
    obtain ⟨K,W,hWG,hW⟩ := ih hT.2.2 F.image hSub (e.target_definable (gammaLogicInput G))
    refine ⟨K,.focus F W,⟨hH,hFG,hWG⟩,?_⟩
    intro p
    change (W.toMap (F.toImage p)).val = _
    exact hW (F.toImage p)

end IntegrationInACVF.Section5.UniformRelativeTrace
