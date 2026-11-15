import IntegrationSection5.RVPredicateFocus
import IntegrationSection5.UnaryChainCoordinateLift
import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection5.GammaUnaryCoordinateLift
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
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {S : Set M} {n a b : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}

theorem coordinateCanonical_sameRV (i : Fin n) {l : ℕ}
    {p q : Point (M := M) n l} (h : SameRV p q) :
    SameRV (coordinateCanonical i p) (coordinateCanonical i q) := by
  obtain ⟨hv,hr⟩ := (sameRV_iff _ _).mp h
  apply (sameRV_iff _ _).mpr
  refine ⟨hv,?_⟩
  funext j
  cases j using Fin.addCases with
  | left j =>
    fin_cases j
    exact hv i
  | right j =>
    simpa only [coordinateCanonical,Fin.append_right] using congrFun hr j

theorem gamma_unary_chain_rvPredicateLift (T : Chain S 1 A B) (hT : GammaChainDefinable G T) :
    ∀ (E : Set (Fin a → RV (M := M))) (hA : ∀ p ∈ carrier A, p.2 ∈ E)
      {l : ℕ} (H : DefSet (M := M) S n l) (hH : GammaSetDefinable G (carrier H)) (i : Fin n) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ E → activeUnaryProjection i ρ p ∈ carrier A)
      (previous : Option Bool)
      (hTag : previous ≠ some true → ∃ kH, Tagged (carrier H) i kH), T.Alternating previous →
    ∃ r : ℕ, ∃ K : DefSet (M := M) S n r, ∃ σ : Fin b → Fin r,
    ∃ hle : l ≤ r, ∃ f : Map H K, SpecialRelativeBoundary f i previous (T.lastKind previous) ∧
      GammaSetDefinable G (carrier K) ∧ GammaGraphDefinable G (pointMapGraph f) ∧
      (∀ k, σ (suffixIndex (special_chain_rvArity_le T) k) = suffixIndex hle (ρ k)) ∧
      (∀ k : Fin r, (∃ t, σ t = k) ∨ ∃ t, suffixIndex hle t = k) ∧
      (∀ p : H, ∀ hp : p.val.2 ∘ ρ ∈ E,
        activeUnaryProjection i σ (f p).val =
          (T.toMap ⟨activeUnaryProjection i ρ p.val,hHA p.val p.property hp⟩).val) ∧
      (∀ p : H, p.val.2 ∘ ρ ∉ E → vfAt (f p).val i = vfAt p.val i) ∧
      (∀ p q : H, p.val.2 ∘ ρ ∉ E → q.val.2 ∘ ρ ∉ E → SameRV p.val q.val →
        SameRV (f p).val (f q).val) ∧
      (T.lastKind previous ≠ some true → ∃ kH, Tagged (carrier K) i kH) := by
  revert hT
  induction T with
  | nil A =>
    intro _ E hA l H hH i ρ hHA previous hTag _
    refine ⟨l,H,ρ,le_rfl,Map.id H,specialRelativeBoundary_id H i previous,
      hH,gamma_identity_graph H hH,?_,?_,fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ _ h => h,hTag⟩
    · intro k
      have hs (k : Fin _) : suffixIndex (special_chain_rvArity_le (Chain.nil A)) k = k := by
        apply Fin.ext
        simp [suffixIndex]
      rw [hs]
      apply Fin.ext
      simp [suffixIndex]
    · intro k
      exact Or.inr ⟨k,by apply Fin.ext; simp [suffixIndex]⟩
  | @cons a' b' c' A' B' C' step tail ih =>
    intro hT
    cases step with
    | canonical =>
      intro E hA l H hH i ρ hHA previous hTag hAlt
      let H' := coordinateCanonicalImage H i
      let ρ' := activeCanonicalProjection ρ
      let can := coordinateCanonicalBijection H i
      let E' : Set (Fin (1+a') → RV (M := M)) := {s | s ∘ Fin.natAdd 1 ∈ E}
      have hA' : ∀ p ∈ carrier (canonicalImage A'), p.2 ∈ E' := by
        rintro _ ⟨p,rfl⟩
        have he : (canonical p.val).2 ∘ Fin.natAdd 1 = p.val.2 := by
          funext j; simp only [Function.comp_apply,canonical,Fin.append_right]
        change (canonical p.val).2 ∘ Fin.natAdd 1 ∈ E
        rw [he]
        exact hA p.val p.property
      have hFlag : ∀ p : H, (can p).val.2 ∘ ρ' ∈ E' ↔ p.val.2 ∘ ρ ∈ E := by
        intro p
        change ((coordinateCanonical i p.val).2 ∘ activeCanonicalProjection ρ) ∘ Fin.natAdd 1 ∈ E ↔ _
        have he : ((coordinateCanonical i p.val).2 ∘ activeCanonicalProjection ρ) ∘ Fin.natAdd 1 = p.val.2 ∘ ρ := by
          funext j
          simp only [Function.comp_apply,activeCanonicalProjection,Fin.addCases_right,coordinateCanonical,Fin.append_right]
        rw [he]
      have hsub : ∀ p ∈ carrier H', p.2 ∘ ρ' ∈ E' →
          activeUnaryProjection i ρ' p ∈ carrier (canonicalImage A') := by
        rintro _ ⟨q,rfl⟩ hq
        change activeUnaryProjection i ρ' (coordinateCanonical i q.val) ∈ carrier (canonicalImage A')
        rw [activeUnaryProjection_canonical]
        exact ⟨⟨activeUnaryProjection i ρ q.val,hHA q.val q.property ((hFlag q).mp hq)⟩,rfl⟩
      have hTag' : (some false : Option Bool) ≠ some true → ∃ kH, Tagged (carrier H') i kH :=
        fun _ => ⟨0,coordinateCanonical_tagged H i⟩
      obtain ⟨r,K,σ,hle,f,hf,hK,hfG,hcompat,hcover,hcomm,hoff,hoffkey,htag⟩ :=
        ih hT.2 E' hA' H' (gamma_coordinateCanonicalImage H hH i) i ρ' hsub (some false) hTag' hAlt.2
      have hle' : l ≤ r := by change 1+l ≤ r at hle; omega
      have hlow := special_chain_rvArity_le tail
      change 1+a' ≤ c' at hlow
      refine ⟨r,K,σ,hle',Map.comp f can,?_,hK,?_,?_,?_,?_,?_,?_,htag⟩
      · exact specialRelativeBoundary_comp can f i
          (coordinateCanonical_specialRelativeBoundary H i previous hAlt.1) hf
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
      · intro p hp
        change activeUnaryProjection i σ (f (can p)).val = _
        rw [hcomm (can p) ((hFlag p).mpr hp)]
        have he : (⟨activeUnaryProjection i ρ' (can p).val,hsub _ (can p).property ((hFlag p).mpr hp)⟩ : canonicalImage A') =
            (SpecialBijection.canonical A').toMap ⟨activeUnaryProjection i ρ p.val,hHA _ p.property hp⟩ := by
          apply Subtype.ext
          exact activeUnaryProjection_canonical i ρ p.val
        rw [he]
        rfl
      · intro p hp
        exact hoff (can p) (fun hh => hp ((hFlag p).mp hh))
      · intro p q hp hq he
        exact hoffkey (can p) (can q) (fun hh => hp ((hFlag p).mp hh))
          (fun hh => hq ((hFlag q).mp hh)) (coordinateCanonical_sameRV i he)
    | @centripetal X jD k D =>
      have hjD : jD = 0 := Subsingleton.elim _ _
      subst jD
      intro E hA l H hH i ρ hHA previous hTag hAlt
      obtain ⟨kH,hTagged⟩ := hTag hAlt.1
      let F := Focus.rvPredicateLift D i ρ E hA hHA kH hTagged
      let eta := (SpecialBijection.centripetal F).toMap
      have hFG : GammaFocusDefinable G F :=
        Focus.rvPredicateLift_gamma D i ρ E hA hHA kH hTagged hH hT.1.2
      have hImage : GammaSetDefinable G (carrier F.etaImage) :=
        GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal F) ⟨hH,hFG⟩
      have hA' : ∀ p ∈ carrier D.etaImage, p.2 ∈ E := by
        rintro _ ⟨p,rfl⟩
        change (D.toFocusGeometry.eta p.val).2 ∈ E
        rw [D.toFocusGeometry.eta_labels]
        exact hA p.val p.property
      have hFlag : ∀ p : H, (eta p).val.2 ∘ ρ ∈ E ↔ p.val.2 ∘ ρ ∈ E := by
        intro p
        change (F.toFocusGeometry.eta p.val).2 ∘ ρ ∈ E ↔ _
        rw [F.toFocusGeometry.eta_labels]
      have hsub : ∀ p ∈ carrier F.etaImage, p.2 ∘ ρ ∈ E →
          activeUnaryProjection i ρ p ∈ carrier D.etaImage := by
        rintro _ ⟨q,rfl⟩ hq
        have hqFlag : q.val.2 ∘ ρ ∈ E := (hFlag q).mp hq
        change activeUnaryProjection i ρ (F.toFocusGeometry.eta q.val) ∈ carrier D.etaImage
        have he := Focus.rvPredicateLift_projection D i ρ E hA hHA kH hTagged q
        have hm : D.toFocusGeometry.eta (activeUnaryProjection i ρ q.val) ∈ carrier D.etaImage :=
          ⟨⟨activeUnaryProjection i ρ q.val,hHA q.val q.property hqFlag⟩,rfl⟩
        exact he.symm ▸ hm
      have hTag' : (some true : Option Bool) ≠ some true → ∃ kH, Tagged (carrier F.etaImage) i kH :=
        fun h => (h rfl).elim
      obtain ⟨r,K,σ,hle,f,hf,hK,hfG,hcompat,hcover,hcomm,hoff,hoffkey,htag⟩ :=
        ih hT.2 E hA' F.etaImage hImage i ρ hsub (some true) hTag' hAlt.2
      refine ⟨r,K,σ,hle,Map.comp f eta,?_,hK,?_,hcompat,hcover,?_,?_,?_,htag⟩
      · exact specialRelativeBoundary_comp eta f i (centripetal_specialRelativeBoundary F previous hAlt.1) hf
      · exact gamma_composition_graph eta f
          (GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal F) ⟨hH,hFG⟩) hfG
      · intro p hp
        change activeUnaryProjection i σ (f (eta p)).val = _
        rw [hcomm (eta p) ((hFlag p).mpr hp)]
        have he : (⟨activeUnaryProjection i ρ (eta p).val,hsub _ (eta p).property ((hFlag p).mpr hp)⟩ : D.etaImage) =
            (SpecialBijection.centripetal D).toMap ⟨activeUnaryProjection i ρ p.val,hHA _ p.property hp⟩ := by
          apply Subtype.ext
          exact Focus.rvPredicateLift_projection D i ρ E hA hHA kH hTagged p
        rw [he]
        rfl
      · intro p hp
        have hOff := Focus.rvPredicateLift_inactive D i ρ E hA hHA kH hTagged p hp
        exact (hoff (eta p) (fun hh => hp ((hFlag p).mp hh))).trans
          (congrArg (fun z : Point (M := M) n l => vfAt z i) hOff)
      · intro p q hp hq he
        apply hoffkey (eta p) (eta q) (fun hh => hp ((hFlag p).mp hh))
          (fun hh => hq ((hFlag q).mp hh))
        change SameRV ((Focus.rvPredicateLift D i ρ E hA hHA kH hTagged).etaMap p).val
          ((Focus.rvPredicateLift D i ρ E hA hHA kH hTagged).etaMap q).val
        rw [Focus.rvPredicateLift_inactive D i ρ E hA hHA kH hTagged p hp,
          Focus.rvPredicateLift_inactive D i ρ E hA hHA kH hTagged q hq]
        exact he

end IntegrationInACVF.Section5
