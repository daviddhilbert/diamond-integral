import IntegrationSection5.RVSliceMapImage
import IntegrationSection5.PaddedExtensionInactive
import IntegrationSection5.PaddedProductCompletion
import IntegrationSection5.ProjectionPaddingOperations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l c e v : ℕ}
variable {AN : DefSet (M := M) S 1 a} {BN : DefSet (M := M) S 1 b}
variable {AE : DefSet (M := M) S 1 e} {BE : DefSet (M := M) S 1 v}
variable {H D : DefSet (M := M) S 1 l} {C0 : DefSet (M := M) S 1 c}
variable {uN : SpecialBijection AN BN} {ρN : Fin a → Fin l} {EN : Set (Fin a → RV (M := M))}
variable {previous : Option Bool}

theorem complementary_padded_completion
    (N : PaddedUnaryBranchExtension (G := G) uN H ρN EN previous)
    (uE : SpecialBijection AE BE) (huE : GammaChainDefinable G uE.chain) (hBE : IsRVPullback (carrier BE))
    (ρ : Fin c → Fin l) (σ : Fin e → Fin c) (ER : Set (Fin e → RV (M := M)))
    (P : RVProjectionPadding (G := G) D C0 ρ)
    (Q : Point (M := M) 1 c → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hC : carrier C0 = {p | activeUnaryProjection 0 σ p ∈ carrier AE ∧ Q p})
    (hClass : ∀ p ∈ carrier AE, ∀ q ∈ carrier AE, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (hD : carrier D = {p | p ∈ carrier H ∧ p.2 ∘ (ρ ∘ σ) ∈ ER})
    (hComplement : ∀ s : Fin l → RV (M := M), s ∘ (ρ ∘ σ) ∈ ER ↔ s ∘ ρN ∉ EN)
    (hFlag : ∀ p ∈ carrier AE, p.2 ∈ ER) :
    Nonempty (PaddedProductCompletion (G := G) uE N.lift.target
      ((suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ ρ) ∘ σ)
      ER (uN.chain.lastKind N.start)) := by
  let τ := suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))
  have hSub : carrier D ⊆ carrier H := fun p hp => ((Set.ext_iff.mp hD p).mp hp).1
  have hOff (p : D) : p.val.2 ∘ ρN ∉ EN :=
    (hComplement p.val.2).mp (((Set.ext_iff.mp hD p.val).mp p.property).2)
  have hDG := (P.iso.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)
  let I := restrictPointImage N.map D hSub
  let R := inactiveProjectionPadding N.map
    (specialRelative_bijective (specialRelativeBoundary_forget N.special)) hSub hDG N.graph
    (fun p => N.inactive_vf ⟨p.val,hSub p.property⟩ (hOff p)) τ N.oldLabels
    (fun p q he => N.inactive_sameRV ⟨p.val,hSub p.property⟩ ⟨q.val,hSub q.property⟩ (hOff p) (hOff q) he)
  have hI : carrier I = {p | p ∈ carrier N.lift.target ∧ p.2 ∘ ((τ ∘ ρ) ∘ σ) ∈ ER} := by
    exact rvSlice_map_image N.map
      (specialRelative_bijective (specialRelativeBoundary_forget N.special)).2 (ρ ∘ σ) τ N.oldLabels ER hD
  have hInactive : HeadSaturated {p | p ∈ carrier N.lift.target ∧ p.2 ∘ ((τ ∘ ρ) ∘ σ) ∉ ER} := by
    have he : {p | p ∈ carrier N.lift.target ∧ p.2 ∘ ((τ ∘ ρ) ∘ σ) ∉ ER} = carrier N.lift.active_image := by
      rw [N.active_slice]
      ext p
      change (p ∈ carrier N.lift.target ∧ ¬ (p.2 ∘ τ) ∘ (ρ ∘ σ) ∈ ER) ↔
        (p ∈ carrier N.lift.target ∧ (p.2 ∘ τ) ∘ ρN ∈ EN)
      rw [hComplement]
      exact and_congr_right (fun _ => not_not)
    exact he.symm ▸ N.lift.active_saturated
  exact padded_product_completion uE huE hBE N.lift.target_gamma (τ ∘ ρ) σ ER (P.trans R) Q hQ hC hClass hI hFlag hInactive
    (uN.chain.lastKind N.start) (fun h => N.lift.ending_tag (by rw [h]; decide))

end IntegrationInACVF.Section5
