import IntegrationSection5.GammaTraceCompiler
import IntegrationSection5.TraceInputPresentation

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

theorem gamma_fullRVProjectionInto {a b : ℕ} (ρ : Fin a → Fin b)
    (X : DefSet (M := M) S n b) (Y : DefSet (M := M) S n a)
    (hXY : ∀ p ∈ carrier X, fullRVProjection ρ p ∈ carrier Y)
    (hX : GammaSetDefinable G (carrier X)) :
    GammaGraphDefinable G (pointMapGraph (fullRVProjectionInto ρ X Y hXY)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hX
    ((gammaLogicInput G).real_map_graph (fullRVProjectionMap ρ (PresentedSet.univ (pointSpace n b) G.real))))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    exact ⟨⟨p,hp⟩,rfl,(congrArg (fullRVProjection ρ) ha).symm.trans hq⟩
  · rintro ⟨a,rfl,hq⟩
    exact ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,hq⟩

namespace UniformRelativeTrace
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem gamma_inputPresentation (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    GammaSetDefinable G (carrier T.inputPresentation) := by
  let P := gammaRVMapOfPointMap T.flagMap (GammaUniformTrace.flagMap T hT)
  have h := (gammaLogicInput G).image_graph P.attachment_graph
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

/-- Actual special chains between explicit VF-fixed RV presentations of the trace's ends. -/
theorem gamma_special_presentation (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    ∃ b, ∃ K : DefSet (M := M) S n b, ∃ σ : Fin l → Fin b,
      ∃ W : SpecialBijection T.inputPresentation K, GammaChainDefinable G W.chain ∧
      ∃ hKB : ∀ p ∈ carrier K, fullRVProjection σ p ∈ carrier B,
        Function.Bijective (fullRVProjectionInto σ K B hKB) ∧
        ∀ p : T.inputPresentation,
          fullRVProjection σ (W.toMap p).val = (T.toMap (T.inputProjection p)).val := by
  let H := T.inputPresentation
  let ρ : Fin m → Fin (m+T.flagCount) := Fin.castAdd T.flagCount
  let τ : Fin T.flagCount → Fin (m+T.flagCount) := Fin.natAdd m
  have hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A := fun p hp => (T.inputProjection ⟨p,hp⟩).property
  have hFlags : ∀ p : H, ∀ j, p.val.2 (τ j) =
      (T.flagMap ⟨fullRVProjection ρ p.val,hHA _ p.property⟩).val.2 j := by
    rintro ⟨q,a,rfl⟩ j
    have he : (⟨fullRVProjection ρ (attachRV a.val (T.flagMap a).val.2),hHA _ ⟨a,rfl⟩⟩ : A) = a := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      funext j
      exact Fin.append_left _ _ j
    change (attachRV a.val (T.flagMap a).val.2).2 (τ j) =
      (T.flagMap ⟨fullRVProjection ρ (attachRV a.val (T.flagMap a).val.2),hHA _ ⟨a,rfl⟩⟩).val.2 j
    rw [he]
    exact Fin.append_right _ _ j
  obtain ⟨b,K,σ,V,hV,hVG,hComm⟩ := T.gamma_compile hT H ρ τ hHA hFlags none (by intro h; cases h) (T.gamma_inputPresentation hT)
  let W : SpecialBijection H K := ⟨V,hV⟩
  have hKB : ∀ p ∈ carrier K, fullRVProjection σ p ∈ carrier B := by
    intro p hp
    obtain ⟨a,ha⟩ := W.bijective.2 ⟨p,hp⟩
    have he : fullRVProjection σ p = (T.toMap (T.inputProjection a)).val :=
      (congrArg (fullRVProjection σ) (congrArg (fun z : K => z.val) ha)).symm.trans (hComm a)
    exact he.symm ▸ (T.toMap (T.inputProjection a)).property
  let g := fullRVProjectionInto σ K B hKB
  have hsquare (a : H) : g (W.toMap a) = T.toMap (T.inputProjection a) := Subtype.ext (hComm a)
  have hgb : Function.Bijective g := by
    constructor
    · intro p q hpq
      obtain ⟨a,rfl⟩ := W.bijective.2 p
      obtain ⟨c,rfl⟩ := W.bijective.2 q
      have hac := T.bijective.1 ((hsquare a).symm.trans (hpq.trans (hsquare c)))
      exact congrArg W.toMap (T.inputProjection_bijective.1 hac)
    · intro z
      obtain ⟨a,ha⟩ := T.bijective.2 z
      obtain ⟨p,hp⟩ := T.inputProjection_bijective.2 a
      exact ⟨W.toMap p,(hsquare p).trans ((congrArg T.toMap hp).trans ha)⟩
  exact ⟨b,K,σ,W,hVG,hKB,hgb,hComm⟩

end UniformRelativeTrace
end IntegrationInACVF.Section5
