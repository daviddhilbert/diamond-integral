import «section 3».GammaVFProjectionFocus
import «section 3».GammaChainRetainedLabels

/-! A base special chain lifts across additional VF and RV coordinates.
The lifted chain is genuinely special, retains the original Gamma
certificates and old RV labels, and fixes every complementary VF value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n N a b l : ℕ}

def gammaVFCanonicalProjection (ι : Fin n → Fin N) (ρ : Fin a → Fin l) : Fin (n+a) → Fin (N+l) :=
  Fin.addCases (fun i => Fin.castAdd l (ι i)) (fun j => Fin.natAdd N (ρ j))

theorem gammaVFProjection_canonical (ι : Fin n → Fin N) (ρ : Fin a → Fin l) (p : Point (M := M) N l) :
    vfRVProjection ι (gammaVFCanonicalProjection ι ρ) (canonical p) = canonical (vfRVProjection ι ρ p) := by
  refine Prod.ext rfl ?_
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [vfRVProjection,gammaVFCanonicalProjection,canonical]

variable {A : DefSet (M := M) S n a} {D : DefSet (M := M) S n b}

theorem gammaVFProjection_chain_lift (T : Chain S n A D) (hT : GammaChainDefinable B T)
    (ι : Fin n → Fin N) (hι : Function.Injective ι) :
    ∀ {l : ℕ} (H : DefSet (M := M) S N l) (hH : GammaSetDefinable B (carrier H)) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
    ∃ r : ℕ, ∃ K : DefSet (M := M) S N r, ∃ σ : Fin b → Fin r, ∃ W : Chain S N H K,
      W.Alternating previous ∧ GammaChainDefinable B W ∧
      (∀ p : H, vfRVProjection ι σ (W.toMap p).val =
        (T.toMap ⟨vfRVProjection ι ρ p.val,hHA _ p.property⟩).val) ∧
      (∀ j, σ (gammaChainOldLabelIndex T j) = gammaChainOldLabelIndex W (ρ j)) ∧
      ∀ p : H, ∀ j : Fin N, j ∉ Set.range ι → (W.toMap p).val.1 j = p.val.1 j := by
  revert hT
  induction T with
  | nil A =>
    intro _ l H hH ρ hHA previous _
    exact ⟨l,H,ρ,.nil H,trivial,hH,fun _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
  | @cons a' b' c' A' D' E' step tail ih =>
    intro hT
    cases step with
    | canonical =>
      intro l H hH ρ hHA previous hAlt
      let H' := canonicalImage H
      let ρ' := gammaVFCanonicalProjection ι ρ
      have hSub : ∀ p ∈ carrier H', vfRVProjection ι ρ' p ∈ carrier (canonicalImage A') := by
        rintro _ ⟨q,rfl⟩
        change vfRVProjection ι ρ' (canonical q.val) ∈ carrier (canonicalImage A')
        rw [gammaVFProjection_canonical]
        exact ⟨⟨vfRVProjection ι ρ q.val,hHA _ q.property⟩,rfl⟩
      have hH' : GammaSetDefinable B (carrier H') :=
        GammaPrimitiveDefinable.target (gammaLogicInput B) (.canonical H) hH
      obtain ⟨r,K,σ,V,hV,hVG,hSquare,hLabels,hOther⟩ := ih hT.2 H' hH' ρ' hSub (some false) hAlt.2
      let W : Chain S N H K := .cons (.canonical H) V
      refine ⟨r,K,σ,W,⟨hAlt.1,hV⟩,⟨hH,hVG⟩,?_,?_,?_⟩
      · intro p
        change vfRVProjection ι σ (V.toMap ((SpecialBijection.canonical H).toMap p)).val = _
        rw [hSquare]
        have he : (⟨vfRVProjection ι ρ' ((SpecialBijection.canonical H).toMap p).val,
            hSub _ ((SpecialBijection.canonical H).toMap p).property⟩ : canonicalImage A') =
            (SpecialBijection.canonical A').toMap ⟨vfRVProjection ι ρ p.val,hHA _ p.property⟩ :=
          Subtype.ext (gammaVFProjection_canonical ι ρ p.val)
        rw [he]
        rfl
      · intro j
        change σ (gammaChainOldLabelIndex tail (Fin.natAdd n j)) =
          gammaChainOldLabelIndex V (Fin.natAdd N (ρ j))
        simpa only [ρ',gammaVFCanonicalProjection,Fin.addCases_right] using hLabels (Fin.natAdd n j)
      · intro p j hj
        exact hOther ((SpecialBijection.canonical H).toMap p) j hj
    | @centripetal X j k F =>
      intro l H hH ρ hHA previous hAlt
      let E := gammaVFProjectionFocus F ι hι ρ hHA
      have hEG : GammaFocusDefinable B E := gammaVFProjectionFocus_gamma F ι hι ρ hHA hH hT.1.2
      have hSub : ∀ p ∈ carrier E.etaImage, vfRVProjection ι ρ p ∈ carrier F.etaImage := by
        rintro _ ⟨q,rfl⟩
        change vfRVProjection ι ρ (E.toFocusGeometry.eta q.val) ∈ carrier F.etaImage
        rw [gammaVFProjectionFocus_eta F ι hι ρ hHA q.val q.property]
        exact ⟨⟨vfRVProjection ι ρ q.val,hHA _ q.property⟩,rfl⟩
      have hImage : GammaSetDefinable B (carrier E.etaImage) :=
        GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal E) ⟨hH,hEG⟩
      obtain ⟨r,K,σ,V,hV,hVG,hSquare,hLabels,hOther⟩ := ih hT.2 E.etaImage hImage ρ hSub (some true) hAlt.2
      let W : Chain S N H K := .cons (.centripetal E) V
      refine ⟨r,K,σ,W,⟨hAlt.1,hV⟩,⟨⟨hH,hEG⟩,hVG⟩,?_,hLabels,?_⟩
      · intro p
        change vfRVProjection ι σ (V.toMap ((SpecialBijection.centripetal E).toMap p)).val = _
        rw [hSquare]
        have he : (⟨vfRVProjection ι ρ ((SpecialBijection.centripetal E).toMap p).val,
            hSub _ ((SpecialBijection.centripetal E).toMap p).property⟩ : F.etaImage) =
            (SpecialBijection.centripetal F).toMap ⟨vfRVProjection ι ρ p.val,hHA _ p.property⟩ :=
          Subtype.ext (gammaVFProjectionFocus_eta F ι hι ρ hHA p.val p.property)
        rw [he]
        rfl
      · intro p i hi
        exact (hOther ((SpecialBijection.centripetal E).toMap p) i hi).trans
          (E.toFocusGeometry.eta_other p.val i (fun he => hi ⟨j,he.symm⟩))

end DiamondIntegral.Section3
