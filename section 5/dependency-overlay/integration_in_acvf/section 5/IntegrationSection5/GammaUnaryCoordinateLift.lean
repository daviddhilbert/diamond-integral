import IntegrationSection5.UnaryChainCoordinateLift
import IntegrationSection5.GammaActiveUnaryFocus
import IntegrationSection5.RelativeLabelPreservation

/-! Constructed coordinate lifts of actual unary chains, with their full
original-Gamma graphs and no extra parameter-base smallness hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n a b : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}

theorem gamma_unary_coordinateLift (T : Chain S 1 A B) (hT : GammaChainDefinable G T) :
    ∀ {l : ℕ} (H : DefSet (M := M) S n l) (hH : GammaSetDefinable G (carrier H))
      (i : Fin n) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
    ∃ r : ℕ, ∃ K : DefSet (M := M) S n r, ∃ σ : Fin b → Fin r,
    ∃ hle : l ≤ r, ∃ f : Map H K, SpecialRelativeBoundary f i previous (T.lastKind previous) ∧
      (Function.Bijective ρ → Function.Bijective σ) ∧
      GammaSetDefinable G (carrier K) ∧ GammaGraphDefinable G (pointMapGraph f) ∧
      (∀ j, σ (suffixIndex (special_chain_rvArity_le T) j) = suffixIndex hle (ρ j)) ∧
      (∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j) ∧
      ∀ p : H, activeUnaryProjection i σ (f p).val =
        (T.toMap ⟨activeUnaryProjection i ρ p.val,hHA p.val p.property⟩).val := by
  revert hT
  induction T with
  | nil A =>
    intro _ l H hH i ρ hHA previous _
    refine ⟨l,H,ρ,le_rfl,Map.id H,specialRelativeBoundary_id H i previous,fun h => h,
      hH,gamma_identity_graph H hH,?_,?_,fun _ => rfl⟩
    · intro j
      have hs (j : Fin _) : suffixIndex (special_chain_rvArity_le (Chain.nil A)) j = j := by
        apply Fin.ext
        simp [suffixIndex]
      rw [hs]
      apply Fin.ext
      simp [suffixIndex]
    · intro j
      exact Or.inr ⟨j,by apply Fin.ext; simp [suffixIndex]⟩
  | @cons a' b' c' A' B' C' step tail ih =>
    intro hT
    cases step with
    | canonical =>
      intro l H hH i ρ hHA previous hAlt
      let H' := coordinateCanonicalImage H i
      let ρ' := activeCanonicalProjection ρ
      let can := coordinateCanonicalBijection H i
      have hsub : ∀ p ∈ carrier H', activeUnaryProjection i ρ' p ∈ carrier (canonicalImage A') := by
        rintro _ ⟨q,rfl⟩
        change activeUnaryProjection i ρ' (coordinateCanonical i q.val) ∈ carrier (canonicalImage A')
        rw [activeUnaryProjection_canonical]
        exact ⟨⟨activeUnaryProjection i ρ q.val,hHA q.val q.property⟩,rfl⟩
      obtain ⟨r,K,σ,hle,f,hf,hσ,hK,hfG,hcompat,hcover,hcomm⟩ := ih hT.2 H' (gamma_coordinateCanonicalImage H hH i)
        i ρ' hsub (some false) hAlt.2
      have hle' : l ≤ r := by change 1+l ≤ r at hle; omega
      have hlow := special_chain_rvArity_le tail
      change 1+a' ≤ c' at hlow
      refine ⟨r,K,σ,hle',Map.comp f can,?_,?_,hK,?_,?_,?_,?_⟩
      · exact specialRelativeBoundary_comp can f i
          (coordinateCanonical_specialRelativeBoundary H i previous hAlt.1) hf
      · exact fun h => hσ (activeCanonicalProjection_bijective ρ h)
      · exact gamma_composition_graph can f (gamma_coordinateCanonical_graph H hH i) hfG
      · intro j
        have hj : suffixIndex (special_chain_rvArity_le (Chain.cons (Primitive.canonical A') tail)) j =
            suffixIndex (special_chain_rvArity_le tail) (Fin.natAdd 1 j) := by
          apply Fin.ext
          change c'-a'+j.val = c'-(1+a')+(1+j.val)
          omega
        rw [hj,hcompat]
        simp only [ρ',activeCanonicalProjection,Fin.addCases_right]
        apply Fin.ext
        change r-(1+l)+(1+(ρ j).val) = r-l+(ρ j).val
        change 1+l ≤ r at hle
        omega
      · intro j
        rcases hcover j with h | ⟨k,hk⟩
        · exact Or.inl h
        · cases k using Fin.addCases with
          | left k =>
            fin_cases k
            exact Or.inl ⟨suffixIndex (special_chain_rvArity_le tail) 0,(hcompat 0).trans hk⟩
          | right k =>
            refine Or.inr ⟨k,?_⟩
            have he : suffixIndex hle (Fin.natAdd 1 k) = suffixIndex hle' k := by
              apply Fin.ext
              change r-(1+l)+(1+k.val) = r-l+k.val
              change 1+l ≤ r at hle
              omega
            exact he.symm.trans hk
      · intro p
        change activeUnaryProjection i σ (f (can p)).val = _
        rw [hcomm]
        have he : (⟨activeUnaryProjection i ρ' (can p).val,hsub _ (can p).property⟩ : canonicalImage A') =
            (SpecialBijection.canonical A').toMap ⟨activeUnaryProjection i ρ p.val,hHA _ p.property⟩ := by
          apply Subtype.ext
          exact activeUnaryProjection_canonical i ρ p.val
        rw [he]
        rfl
    | @centripetal X j k D =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      intro l H hH i ρ hHA previous hAlt
      let F := Focus.coordinateLift D i ρ hHA
      have hFG : GammaFocusDefinable G F := gamma_coordinateLift_focus D i ρ hHA hH hT.1.2
      have hsub : ∀ p ∈ carrier F.etaImage, activeUnaryProjection i ρ p ∈ carrier D.etaImage := by
        rintro _ ⟨q,rfl⟩
        change activeUnaryProjection i ρ (F.toFocusGeometry.eta q.val) ∈ carrier D.etaImage
        rw [Focus.coordinateLift_eta D i ρ hHA q.val q.property]
        exact ⟨⟨activeUnaryProjection i ρ q.val,hHA q.val q.property⟩,rfl⟩
      have hImage : GammaSetDefinable G (carrier F.etaImage) :=
        GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal F) ⟨hH,hFG⟩
      obtain ⟨r,K,σ,hle,f,hf,hσ,hK,hfG,hcompat,hcover,hcomm⟩ := ih hT.2 F.etaImage hImage i ρ hsub (some true) hAlt.2
      let eta := (SpecialBijection.centripetal F).toMap
      refine ⟨r,K,σ,hle,Map.comp f eta,?_,hσ,hK,?_,hcompat,hcover,?_⟩
      · exact specialRelativeBoundary_comp eta f i (centripetal_specialRelativeBoundary F previous hAlt.1) hf
      · exact gamma_composition_graph eta f
          (GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal F) ⟨hH,hFG⟩) hfG
      · intro p
        change activeUnaryProjection i σ (f (eta p)).val = _
        rw [hcomm]
        have he : (⟨activeUnaryProjection i ρ (eta p).val,hsub _ (eta p).property⟩ : D.etaImage) =
            (SpecialBijection.centripetal D).toMap ⟨activeUnaryProjection i ρ p.val,hHA _ p.property⟩ := by
          apply Subtype.ext
          exact Focus.coordinateLift_eta D i ρ hHA p.val p.property
        rw [he]
        rfl

end IntegrationInACVF.Section5
