import IntegrationSection5.GammaTraceCore
import IntegrationSection5.EmptyFocus

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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ}

theorem gamma_presentationFocus {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {i : Fin n} {k : Fin m} (D : FibreFocusData A i k) (hD : GammaFibreFocusDefinable G D)
    (hH : GammaSetDefinable G (carrier H)) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A)
    (E : Set (Fin l → RV (M := M))) (hE : SetDefinable (pointSpace n l) S {p | p.2 ∈ E})
    (hEG : GammaSetDefinable G {p : Point (M := M) n l | p.2 ∈ E})
    (hFlag : ∀ p ∈ carrier H, p.2 ∈ E ↔ fullRVProjection ρ p ∈ D.locus) :
    GammaFocusDefinable G (D.presentationFocus ρ hHA E hE hFlag) := by
  let L := gammaLogicInput G
  refine ⟨L.inter hEG (L.hull hH),?_⟩
  let F := fullRVProjectionMap ρ (PresentedSet.univ (pointSpace n l) G.real)
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 1 0) G.real)
  apply GammaGraphDefinable.congr (L.restrict_graph hH (hD.center.preimage_maps F I))
  intro p z
  constructor
  · rintro ⟨hp,⟨ha,hl⟩,hc⟩
    exact ⟨⟨hp,(hFlag p hp).mpr hl,subset_hull _ hp⟩,hc⟩
  · rintro ⟨⟨hp,he,hh⟩,hc⟩
    exact ⟨hp,⟨hHA p hp,(hFlag p hp).mp he⟩,hc⟩

theorem gamma_global_canonical_prefix (H : DefSet (M := M) S n m)
    (hH : GammaSetDefinable G (carrier H)) (i : Fin n) (previous : Option Bool)
    (hTags : previous = some false → AllTagged H) :
    ∃ K : DefSet (M := M) S n (n+m), ∃ W : Chain S n H K,
      W.Alternating previous ∧ W.lastKind previous = some false ∧ AllTagged K ∧
      GammaChainDefinable G W ∧ ∀ p : H, (W.toMap p).val = canonical p.val := by
  by_cases hp : previous = some false
  · subst previous
    obtain ⟨k,hk⟩ := hTags rfl i
    let D := Focus.empty i k hk
    let K := canonicalImage D.etaImage
    let W : Chain S n H K := .cons (.centripetal D) (.cons (.canonical _) (.nil _))
    have hD : GammaFocusDefinable G D := Focus.empty_gamma i k hk
    have hImage := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal D) ⟨hH,hD⟩
    have hK := GammaPrimitiveDefinable.target (gammaLogicInput G) (.canonical D.etaImage) hImage
    refine ⟨K,W,⟨by decide,by decide,trivial⟩,rfl,canonicalImage_allTagged _,⟨⟨hH,hD⟩,hImage,hK⟩,?_⟩
    intro p
    exact congrArg canonical (Focus.empty_eta i k hk p.val)
  · let K := canonicalImage H
    let W : Chain S n H K := .cons (.canonical H) (.nil _)
    have hK := GammaPrimitiveDefinable.target (gammaLogicInput G) (.canonical H) hH
    exact ⟨K,W,⟨hp,trivial⟩,rfl,canonicalImage_allTagged H,⟨hH,hK⟩,fun _ => rfl⟩

end IntegrationInACVF.Section5
