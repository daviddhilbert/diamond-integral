import «section 3».GammaRVProjectionFocus
import «section 3».GammaChainRetainedLabels

/-! Extend an already constructed special chain across additional RV
labels. The proof retains the existing primitives, alternation, full
Gamma certificates, and an explicit cover of every output label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
variable {D : SpecialTransformations.Section5.DefSet (M := M) S n b}

theorem gammaRVProjection_chain_lift (T : Chain S n A D) (hT : GammaChainDefinable B T) :
    ∀ {l : ℕ} (H : SpecialTransformations.Section5.DefSet (M := M) S n l)
      (hH : GammaSetDefinable B (carrier H)) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
    ∃ r : ℕ, ∃ K : SpecialTransformations.Section5.DefSet (M := M) S n r, ∃ σ : Fin b → Fin r,
    ∃ W : Chain S n H K, W.Alternating previous ∧ GammaChainDefinable B W ∧
      (∀ p : H, gammaRVProjection σ (W.toMap p).val =
        (T.toMap ⟨gammaRVProjection ρ p.val,hHA p.val p.property⟩).val) ∧
      (∀ j, σ (gammaChainOldLabelIndex T j) = gammaChainOldLabelIndex W (ρ j)) ∧
      ∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, gammaChainOldLabelIndex W k = j := by
  revert hT
  induction T with
  | nil A =>
    intro _ l H hH ρ hHA previous _
    exact ⟨l,H,ρ,.nil H,trivial,hH,fun _ => rfl,fun _ => rfl,fun j => Or.inr ⟨j,rfl⟩⟩
  | @cons a' b' c' A' D' E' step tail ih =>
    intro hT
    cases step with
    | canonical =>
      intro l H hH ρ hHA previous hAlt
      let H' := canonicalImage H
      let ρ' := gammaRVCanonicalProjection (n := n) ρ
      have hsub : ∀ p ∈ carrier H', gammaRVProjection ρ' p ∈ carrier (canonicalImage A') := by
        rintro _ ⟨q,rfl⟩
        change gammaRVProjection ρ' (canonical q.val) ∈ carrier (canonicalImage A')
        rw [gammaRVProjection_canonical]
        exact ⟨⟨gammaRVProjection ρ q.val,hHA q.val q.property⟩,rfl⟩
      have hH' : GammaSetDefinable B (carrier H') :=
        GammaPrimitiveDefinable.target (gammaLogicInput B) (.canonical H) hH
      obtain ⟨r,K,σ,U,hU,hUG,hu,hcompat,hcover⟩ := ih hT.2 H' hH' ρ' hsub (some false) hAlt.2
      let W : Chain S n H K := .cons (.canonical H) U
      refine ⟨r,K,σ,W,⟨hAlt.1,hU⟩,⟨hH,hUG⟩,?_,?_,?_⟩
      · intro p
        change gammaRVProjection σ (U.toMap ((SpecialBijection.canonical H).toMap p)).val = _
        rw [hu]
        have he : (⟨gammaRVProjection ρ' ((SpecialBijection.canonical H).toMap p).val,
            hsub _ ((SpecialBijection.canonical H).toMap p).property⟩ : canonicalImage A') =
            (SpecialBijection.canonical A').toMap ⟨gammaRVProjection ρ p.val,hHA _ p.property⟩ := by
          apply Subtype.ext
          exact gammaRVProjection_canonical ρ p.val
        rw [he]
        rfl
      · intro j
        change σ (gammaChainOldLabelIndex tail (Fin.natAdd n j)) =
          gammaChainOldLabelIndex U (Fin.natAdd n (ρ j))
        simpa only [ρ',gammaRVCanonicalProjection,Fin.addCases_right] using hcompat (Fin.natAdd n j)
      · intro j
        rcases hcover j with h | ⟨k,hk⟩
        · exact Or.inl h
        · cases k using Fin.addCases with
          | left k =>
            refine Or.inl ⟨gammaChainOldLabelIndex tail (Fin.castAdd a' k),?_⟩
            have h := hcompat (Fin.castAdd a' k)
            simp only [ρ',gammaRVCanonicalProjection,Fin.addCases_left] at h
            exact h.trans hk
          | right k => exact Or.inr ⟨k,hk⟩
    | @centripetal X j k F =>
      intro l H hH ρ hHA previous hAlt
      let E := gammaRVProjectionFocus F ρ hHA
      have hEG : GammaFocusDefinable B E := gammaRVProjectionFocus_gamma F ρ hHA hH hT.1.2
      have hsub : ∀ p ∈ carrier E.etaImage, gammaRVProjection ρ p ∈ carrier F.etaImage := by
        rintro _ ⟨q,rfl⟩
        change gammaRVProjection ρ (E.toFocusGeometry.eta q.val) ∈ carrier F.etaImage
        rw [gammaRVProjectionFocus_eta F ρ hHA q.val q.property]
        exact ⟨⟨gammaRVProjection ρ q.val,hHA q.val q.property⟩,rfl⟩
      have hImage : GammaSetDefinable B (carrier E.etaImage) :=
        GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal E) ⟨hH,hEG⟩
      obtain ⟨r,K,σ,U,hU,hUG,hu,hcompat,hcover⟩ := ih hT.2 E.etaImage hImage ρ hsub (some true) hAlt.2
      let W : Chain S n H K := .cons (.centripetal E) U
      refine ⟨r,K,σ,W,⟨hAlt.1,hU⟩,⟨⟨hH,hEG⟩,hUG⟩,?_,hcompat,hcover⟩
      intro p
      change gammaRVProjection σ (U.toMap ((SpecialBijection.centripetal E).toMap p)).val = _
      rw [hu]
      have he : (⟨gammaRVProjection ρ ((SpecialBijection.centripetal E).toMap p).val,
          hsub _ ((SpecialBijection.centripetal E).toMap p).property⟩ : F.etaImage) =
          (SpecialBijection.centripetal F).toMap ⟨gammaRVProjection ρ p.val,hHA _ p.property⟩ := by
        apply Subtype.ext
        exact gammaRVProjectionFocus_eta F ρ hHA p.val p.property
      rw [he]
      rfl

end DiamondIntegral.Section3
