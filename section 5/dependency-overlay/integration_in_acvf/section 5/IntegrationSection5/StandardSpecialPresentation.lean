import IntegrationSection5.GammaTracePresentation
import IntegrationSection5.GammaStandardTrace

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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

/-- The natural map is an actual global special bijection after explicit VF-fixed RV presentations. -/
structure StandardSpecialPresentation (G : GammaParameters.Base (M := M)) (C : StandardContraction A σ) where
  sourceArity : ℕ
  targetArity : ℕ
  source : DefSet (M := M) S n sourceArity
  target : DefSet (M := M) S n targetArity
  sourceProjection : Fin m → Fin sourceArity
  targetProjection : Fin C.arity → Fin targetArity
  special : SpecialBijection source target
  special_gamma : GammaChainDefinable G special.chain
  sourceChart : GammaIso G (carrier source) (carrier A)
  source_chart_projection : ∀ p : source, (sourceChart.equiv p).val = fullRVProjection sourceProjection p.val
  targetChart : GammaIso G (carrier target) (carrier (rawLift C.contractionObject))
  target_chart_projection : ∀ p : target, (targetChart.equiv p).val = fullRVProjection targetProjection p.val
  square : ∀ p : source, targetChart.equiv (special.toMap p) = C.naturalLiftMap (sourceChart.equiv p)

theorem standard_special_presentation_of_trace (C : StandardContraction A σ)
    (R : StandardNaturalTrace C) (hR : GammaUniformTrace (G := G) R.trace) :
    Nonempty (StandardSpecialPresentation G C) := by
  obtain ⟨b,K,τ,W,hWG,hKB,hProj,hComm⟩ := R.trace.gamma_special_presentation hR
  let H := R.trace.inputPresentation
  let src := R.trace.inputProjection
  have hSrc := R.trace.inputProjection_bijective
  let ρ : Fin C.arity → Fin b := τ ∘ R.projection
  have hPoint (p : H) : fullRVProjection ρ (W.toMap p).val = (C.naturalMap (src p)).val :=
    (congrArg (fullRVProjection R.projection) (hComm p)).trans (R.square (src p))
  have hInto : ∀ p ∈ carrier K, fullRVProjection ρ p ∈ carrier (rawLift C.contractionObject) := by
    intro p hp
    obtain ⟨q,hq⟩ := W.bijective.2 ⟨p,hp⟩
    have he : fullRVProjection ρ p = (C.naturalLiftMap (src q)).val :=
      (congrArg (fullRVProjection ρ) (congrArg (fun z : K => z.val) hq)).symm.trans (hPoint q)
    exact he.symm ▸ (C.naturalLiftMap (src q)).property
  let f : K → {q : Point (M := M) n C.arity // q ∈ carrier (rawLift C.contractionObject)} := fun p => ⟨fullRVProjection ρ p.val,hInto _ p.property⟩
  have hSquare (p : H) : f (W.toMap p) = C.naturalLiftMap (src p) := Subtype.ext (hPoint p)
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      obtain ⟨x,rfl⟩ := W.bijective.2 p
      obtain ⟨y,rfl⟩ := W.bijective.2 q
      have hxy := C.naturalLiftMap_bijective.1 ((hSquare x).symm.trans (he.trans (hSquare y)))
      exact congrArg W.toMap (hSrc.1 hxy)
    · intro z
      obtain ⟨a,ha⟩ := C.naturalLiftMap_bijective.2 z
      obtain ⟨p,hp⟩ := hSrc.2 a
      exact ⟨W.toMap p,(hSquare p).trans ((congrArg C.naturalLiftMap hp).trans ha)⟩
  have hHG := R.trace.gamma_inputPresentation hR
  have hKG := GammaChainDefinable.target G W.chain hWG
  have hSrcG : GammaGraphDefinable G (pointMapGraph src) :=
    gamma_fullRVProjectionInto (Fin.castAdd R.trace.flagCount) H A _ hHG
  let sChart : GammaIso G (carrier H) (carrier A) := ⟨Equiv.ofBijective src hSrc,hSrcG⟩
  have hfG : GammaGraphDefinable G (fun p q => ∃ a : K, a.val = p ∧ (f a).val = q) :=
    gamma_fullRVProjectionInto ρ K (PresentedSet.univ (pointSpace n C.arity) S) (fun _ _ => Set.mem_univ _) hKG
  let tChart : GammaIso G (carrier K) (carrier (rawLift C.contractionObject)) := ⟨Equiv.ofBijective f hf,hfG⟩
  exact ⟨{
    sourceArity := m+R.trace.flagCount
    targetArity := b
    source := H
    target := K
    sourceProjection := Fin.castAdd R.trace.flagCount
    targetProjection := ρ
    special := W
    special_gamma := hWG
    sourceChart := sChart
    source_chart_projection := fun _ => rfl
    targetChart := tChart
    target_chart_projection := fun _ => rfl
    square := hSquare }⟩

/-- Full global-special presentation statement, with actual internally chosen programs in every order. -/
theorem standard_contraction_exists_with_special_presentation {κ : Cardinal}
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real) (hGS : G.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable G (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, GammaProgramDefinable G C.program ∧ Nonempty (StandardSpecialPresentation G C) := by
  obtain ⟨C,hC,R,hR⟩ := standard_contraction_exists_gamma_traced hs h00 G hsmall F hGS A hA σ
  exact ⟨C,hC,standard_special_presentation_of_trace C R hR⟩

end IntegrationInACVF.Section5
