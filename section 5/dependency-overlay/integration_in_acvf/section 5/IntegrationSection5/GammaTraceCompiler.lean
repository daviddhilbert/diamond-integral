import IntegrationSection5.GammaTraceFlags
import IntegrationSection5.GammaCompilerFocus
import Section5.ZeroNormalization

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
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m l r : ℕ}

def coordinateFullSelector (i : Fin n) (ρ : Fin m → Fin l) : Fin (1+m) → Fin (n+l) :=
  Fin.addCases (fun _ => Fin.castAdd l i) (fun j => Fin.natAdd n (ρ j))

theorem fullRVProjection_canonical (i : Fin n) (ρ : Fin m → Fin l) (p : Point (M := M) n l) :
    fullRVProjection (coordinateFullSelector i ρ) (canonical p) = coordinateCanonical i (fullRVProjection ρ p) := by
  refine Prod.ext rfl ?_
  funext j
  cases j using Fin.addCases <;> simp [fullRVProjection,coordinateFullSelector,canonical,coordinateCanonical,vfAt]

theorem fullRVProjection_old_canonical (ρ : Fin m → Fin l) (p : Point (M := M) n l) :
    fullRVProjection (fun j => Fin.natAdd n (ρ j)) (canonical p) = fullRVProjection ρ p := by
  refine Prod.ext rfl ?_
  funext j
  change Fin.append (fun j : Fin n => rv (vfAt p j)) p.2 (Fin.natAdd n (ρ j)) = p.2 (ρ j)
  exact Fin.append_right _ _ _

namespace UniformRelativeTrace
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

/-- Compile the finite uniform trace using its retained activity flags. -/
theorem gamma_compile (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    ∀ {a : ℕ} (H : DefSet (M := M) S n a) (ρ : Fin m → Fin a)
      (τ : Fin T.flagCount → Fin a)
      (hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A)
      (hFlags : ∀ p : H, ∀ j, p.val.2 (τ j) = (T.flagMap ⟨fullRVProjection ρ p.val,hHA _ p.property⟩).val.2 j)
      (previous : Option Bool), (previous = some false → AllTagged H) → GammaSetDefinable G (carrier H) →
    ∃ b, ∃ K : DefSet (M := M) S n b, ∃ σ : Fin l → Fin b,
      ∃ W : Chain S n H K, W.Alternating previous ∧ GammaChainDefinable G W ∧
        ∀ p : H, fullRVProjection σ (W.toMap p).val =
          (T.toMap ⟨fullRVProjection ρ p.val,hHA _ p.property⟩).val := by
  induction T with
  | nil A =>
    intro a H ρ τ hHA hFlags previous hTags hH
    exact ⟨a,H,ρ,.nil H,trivial,hH,fun _ => rfl⟩
  | @canonical m l A B i tail ih =>
    intro a H ρ τ hHA hFlags previous hTags hH
    obtain ⟨H',V,hV,hLast,hAll,hVG,hShape⟩ := gamma_global_canonical_prefix H hH i previous hTags
    have hH' := GammaChainDefinable.target G V hVG
    let ρ' := coordinateFullSelector i ρ
    let τ' := fun j => Fin.natAdd n (τ j)
    have hSub : ∀ q ∈ carrier H', fullRVProjection ρ' q ∈ carrier (coordinateCanonicalImage A i) := by
      intro q hq
      obtain ⟨p,hp⟩ := V.bijective.2 ⟨q,hq⟩
      have he := (hShape p).symm.trans (congrArg (fun z : H' => z.val) hp)
      have heq : fullRVProjection ρ' q = coordinateCanonical i (fullRVProjection ρ p.val) :=
        (congrArg (fullRVProjection ρ') he).symm.trans (fullRVProjection_canonical i ρ p.val)
      exact heq.symm ▸ (show coordinateCanonical i (fullRVProjection ρ p.val) ∈ carrier (coordinateCanonicalImage A i) from
        ⟨⟨fullRVProjection ρ p.val,hHA _ p.property⟩,rfl⟩)
    have hFlags' : ∀ q : H', ∀ j, q.val.2 (τ' j) =
        (tail.flagMap ⟨fullRVProjection ρ' q.val,hSub _ q.property⟩).val.2 j := by
      intro q j
      obtain ⟨p,rfl⟩ := V.bijective.2 q
      have he : (⟨fullRVProjection ρ' (V.toMap p).val,hSub _ (V.toMap p).property⟩ : coordinateCanonicalImage A i) =
          coordinateCanonicalBijection A i ⟨fullRVProjection ρ p.val,hHA _ p.property⟩ := by
        apply Subtype.ext
        change fullRVProjection ρ' (V.toMap p).val = coordinateCanonical i (fullRVProjection ρ p.val)
        exact (congrArg (fullRVProjection ρ') (hShape p)).trans (fullRVProjection_canonical i ρ p.val)
      rw [he,hShape]
      change Fin.append (fun j => rv (vfAt p.val j)) p.val.2 (Fin.natAdd n (τ j)) = _
      rw [Fin.append_right]
      exact hFlags p j
    obtain ⟨b,K,σ,W,hW,hWG,hComm⟩ := ih hT.2 H' ρ' τ' hSub hFlags' (some false) (fun _ => hAll) hH'
    refine ⟨b,K,σ,V.append W,V.append_alternating W previous hV (hLast.symm ▸ hW),gamma_chain_append V W hVG hWG,?_⟩
    intro p
    rw [Chain.append_toMap]
    change fullRVProjection σ (W.toMap (V.toMap p)).val = _
    rw [hComm]
    apply congrArg (fun z : coordinateCanonicalImage A i => (tail.toMap z).val)
    apply Subtype.ext
    change fullRVProjection ρ' (V.toMap p).val = coordinateCanonical i (fullRVProjection ρ p.val)
    exact (congrArg (fullRVProjection ρ') (hShape p)).trans (fullRVProjection_canonical i ρ p.val)
  | @focus m l A B i k D tail ih =>
    intro a H ρ τ hHA hFlags previous hTags hH
    obtain ⟨H',V,hV,hLast,hAll,hVG,hShape⟩ := gamma_global_canonical_prefix H hH i previous hTags
    have hH' := GammaChainDefinable.target G V hVG
    let ρ' := fun j => Fin.natAdd n (ρ j)
    let τ' : Fin (1+tail.flagCount) → Fin (n+a) := fun j => Fin.natAdd n (τ j)
    have hSub : ∀ q ∈ carrier H', fullRVProjection ρ' q ∈ carrier A := by
      intro q hq
      obtain ⟨p,hp⟩ := V.bijective.2 ⟨q,hq⟩
      have he := (hShape p).symm.trans (congrArg (fun z : H' => z.val) hp)
      have heq : fullRVProjection ρ' q = fullRVProjection ρ p.val :=
        (congrArg (fullRVProjection ρ') he).symm.trans (fullRVProjection_old_canonical ρ p.val)
      exact heq.symm ▸ hHA _ p.property
    have hFlags' : ∀ q : H', ∀ j, q.val.2 (τ' j) =
        ((UniformRelativeTrace.focus D tail).flagMap ⟨fullRVProjection ρ' q.val,hSub _ q.property⟩).val.2 j := by
      intro q j
      obtain ⟨p,rfl⟩ := V.bijective.2 q
      have he : (⟨fullRVProjection ρ' (V.toMap p).val,hSub _ (V.toMap p).property⟩ : A) =
          ⟨fullRVProjection ρ p.val,hHA _ p.property⟩ := by
        apply Subtype.ext
        change fullRVProjection ρ' (V.toMap p).val = fullRVProjection ρ p.val
        exact (congrArg (fullRVProjection ρ') (hShape p)).trans (fullRVProjection_old_canonical ρ p.val)
      rw [he,hShape]
      change Fin.append (fun j => rv (vfAt p.val j)) p.val.2 (Fin.natAdd n (τ j)) = _
      rw [Fin.append_right]
      exact hFlags p j
    let E := {t : Fin (n+a) → RV (M := M) | t (τ' 0) ≠ rv (0 : VF (M := M))}
    have hE : SetDefinable (pointSpace n (n+a)) S {p | p.2 ∈ E} := nonzeroTag_definable (τ' 0)
    have hFlag : ∀ q ∈ carrier H', q.2 ∈ E ↔ fullRVProjection ρ' q ∈ D.locus := by
      intro q hq
      change q.2 (τ' 0) ≠ rv (0 : VF (M := M)) ↔ _
      rw [hFlags' ⟨q,hq⟩ 0]
      exact focus_flag_nonzero D tail _
    let F := D.presentationFocus ρ' hSub E hE hFlag
    have hEG : GammaSetDefinable G {p : Point (M := M) n (n+a) | p.2 ∈ E} :=
      (gammaLogicInput G).real_set _ (nonzeroTag_definable (S := G.real) (τ' 0))
    have hFG := gamma_presentationFocus D hT.2.1 hH' ρ' hSub E hE hEG hFlag
    have hFImage := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal F) ⟨hH',hFG⟩
    let f := (SpecialBijection.centripetal F).toMap
    have hSub' : ∀ q ∈ carrier F.etaImage, fullRVProjection ρ' q ∈ carrier D.image := by
      rintro q ⟨p,rfl⟩
      have he := D.presentationFocus_eta ρ' hSub E hE hFlag p
      exact he.symm ▸ (show D.eta (fullRVProjection ρ' p.val) ∈ carrier D.image from
        ⟨⟨fullRVProjection ρ' p.val,hSub _ p.property⟩,rfl⟩)
    let τ'' := fun j : Fin tail.flagCount => τ' (Fin.natAdd 1 j)
    have hFlags'' : ∀ q : F.etaImage, ∀ j, q.val.2 (τ'' j) =
        (tail.flagMap ⟨fullRVProjection ρ' q.val,hSub' _ q.property⟩).val.2 j := by
      intro q j
      obtain ⟨p,rfl⟩ := (SpecialBijection.centripetal F).bijective.2 q
      have he : (⟨fullRVProjection ρ' (f p).val,hSub' _ (f p).property⟩ : D.image) =
          D.toImage ⟨fullRVProjection ρ' p.val,hSub _ p.property⟩ := by
        apply Subtype.ext
        exact D.presentationFocus_eta ρ' hSub E hE hFlag p
      rw [he]
      have hp := hFlags' p (Fin.natAdd 1 j)
      change p.val.2 (τ'' j) = Fin.append _ (tail.flagMap (D.toImage _)).val.2 (Fin.natAdd 1 j) at hp
      rw [Fin.append_right] at hp
      exact (F.toFocusGeometry.eta_labels p.val ▸ hp)
    obtain ⟨b,K,σ,W,hW,hWG,hComm⟩ := ih hT.2.2 F.etaImage ρ' τ'' hSub' hFlags'' (some true) (by intro h; cases h) hFImage
    let U : Chain S n H' K := .cons (.centripetal F) W
    have hU : U.Alternating (some false) := ⟨by decide,hW⟩
    refine ⟨b,K,σ,V.append U,V.append_alternating U previous hV (hLast.symm ▸ hU),gamma_chain_append V U hVG ⟨⟨hH',hFG⟩,hWG⟩,?_⟩
    intro p
    rw [Chain.append_toMap]
    change fullRVProjection σ (W.toMap (f (V.toMap p))).val = _
    rw [hComm]
    apply congrArg (fun z : D.image => (tail.toMap z).val)
    apply Subtype.ext
    exact (D.presentationFocus_eta ρ' hSub E hE hFlag (V.toMap p)).trans
      (congrArg D.eta ((congrArg (fullRVProjection ρ') (hShape p)).trans (fullRVProjection_old_canonical ρ p.val)))

end UniformRelativeTrace
end IntegrationInACVF.Section5
