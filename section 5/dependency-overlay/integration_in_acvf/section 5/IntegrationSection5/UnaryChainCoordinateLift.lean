import IntegrationSection5.ActiveUnaryCanonical
import IntegrationSection5.RelativeSpecialBoundary

/-! Lift an actual alternating unary special chain at any selected VF
coordinate. Passive VF coordinates and RV labels remain available. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}

theorem unary_chain_coordinateLift (T : Chain S 1 A B) :
    ∀ {l : ℕ} (H : DefSet (M := M) S n l) (i : Fin n) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
    ∃ r : ℕ, ∃ K : DefSet (M := M) S n r, ∃ σ : Fin b → Fin r,
    ∃ f : Map H K, SpecialRelativeBoundary f i previous (T.lastKind previous) ∧
      (Function.Bijective ρ → Function.Bijective σ) ∧
      ∀ p : H, activeUnaryProjection i σ (f p).val =
        (T.toMap ⟨activeUnaryProjection i ρ p.val,hHA p.val p.property⟩).val := by
  induction T with
  | nil A =>
    intro l H i ρ hHA previous _
    exact ⟨l,H,ρ,Map.id H,specialRelativeBoundary_id H i previous,fun h => h,fun _ => rfl⟩
  | @cons a' b' c' A' B' C' step tail ih =>
    cases step with
    | canonical =>
      intro l H i ρ hHA previous hAlt
      let H' := coordinateCanonicalImage H i
      let ρ' := activeCanonicalProjection ρ
      let can := coordinateCanonicalBijection H i
      have hsub : ∀ p ∈ carrier H', activeUnaryProjection i ρ' p ∈ carrier (canonicalImage A') := by
        rintro _ ⟨q,rfl⟩
        change activeUnaryProjection i ρ' (coordinateCanonical i q.val) ∈ carrier (canonicalImage A')
        rw [activeUnaryProjection_canonical]
        exact ⟨⟨activeUnaryProjection i ρ q.val,hHA q.val q.property⟩,rfl⟩
      obtain ⟨r,K,σ,f,hf,hσ,hcomm⟩ := ih H' i ρ' hsub (some false) hAlt.2
      refine ⟨r,K,σ,Map.comp f can,?_,?_,?_⟩
      · exact specialRelativeBoundary_comp can f i
          (coordinateCanonical_specialRelativeBoundary H i previous hAlt.1) hf
      · exact fun h => hσ (activeCanonicalProjection_bijective ρ h)
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
      intro l H i ρ hHA previous hAlt
      let F := Focus.coordinateLift D i ρ hHA
      have hsub : ∀ p ∈ carrier F.etaImage, activeUnaryProjection i ρ p ∈ carrier D.etaImage := by
        rintro _ ⟨q,rfl⟩
        change activeUnaryProjection i ρ (F.toFocusGeometry.eta q.val) ∈ carrier D.etaImage
        rw [Focus.coordinateLift_eta D i ρ hHA q.val q.property]
        exact ⟨⟨activeUnaryProjection i ρ q.val,hHA q.val q.property⟩,rfl⟩
      obtain ⟨r,K,σ,f,hf,hσ,hcomm⟩ := ih F.etaImage i ρ hsub (some true) hAlt.2
      let eta := (SpecialBijection.centripetal F).toMap
      refine ⟨r,K,σ,Map.comp f eta,?_,hσ,?_⟩
      · exact specialRelativeBoundary_comp eta f i (centripetal_specialRelativeBoundary F previous hAlt.1) hf
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
