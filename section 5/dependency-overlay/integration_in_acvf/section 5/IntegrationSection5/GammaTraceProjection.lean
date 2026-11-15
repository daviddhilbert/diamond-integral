import IntegrationSection5.GammaTraceCore
import IntegrationSection5.FibreFocusProjection
import IntegrationSection5.UniformTraceExtension

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
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {n m l N : ℕ}

theorem gamma_vfRVProjection_preimage (ι : Fin n → Fin N) (ρ : Fin m → Fin l)
    {D : Set (Point (M := M) n m)} (hD : GammaSetDefinable G D) :
    GammaSetDefinable G {p | vfRVProjection ι ρ p ∈ D} := by
  have h := (gammaLogicInput G).preimage_real (vfRVProjectionMap ι ρ (PresentedSet.univ (pointSpace N l) G.real)) hD
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
  · rintro ⟨a,ha,hp⟩
    exact ha ▸ hp

theorem GammaFibreFocusDefinable.projectionPullback
    {A : DefSet (M := M) S n m} {H : DefSet (M := M) S N l} {i : Fin n} {k : Fin m}
    (D : FibreFocusData A i k) (hD : GammaFibreFocusDefinable G D)
    (hH : GammaSetDefinable G (carrier H))
    (ι : Fin n → Fin N) (hι : Function.Injective ι) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) :
    GammaFibreFocusDefinable G (D.projectionPullback ι hι ρ hHA) := by
  refine ⟨gamma_vfRVProjection_preimage ι ρ hD.locus,?_⟩
  let F := vfRVProjectionMap ι ρ (PresentedSet.univ (pointSpace N l) G.real)
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 1 0) G.real)
  have h := (gammaLogicInput G).restrict_graph hH (hD.center.preimage_maps F I)
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,⟨ha,hl⟩,hc⟩
    exact ⟨⟨hp,hl⟩,hc⟩
  · rintro ⟨⟨hp,hl⟩,hc⟩
    exact ⟨hp,⟨hHA p hp,hl⟩,hc⟩

theorem GammaFibreFocusDefinable.extendBase {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}
    (D : FibreFocusData A i k) (hD : GammaFibreFocusDefinable G D) (hSR : S ⊆ R) :
    GammaFibreFocusDefinable G (D.extendBase hSR) := ⟨hD.locus,hD.center⟩

theorem GammaUniformTrace.source {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    {T : UniformRelativeTrace S n A B} (hT : GammaUniformTrace (G := G) T) : GammaSetDefinable G (carrier A) := by
  cases T with
  | nil A => exact hT
  | canonical i tail => exact hT.1
  | focus D tail => exact hT.1

theorem GammaUniformTrace.graph {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    GammaGraphDefinable G (pointMapGraph T.toMap) := by
  induction T with
  | nil A => exact gamma_identity_graph A hT
  | canonical i tail ih =>
    exact gamma_composition_graph (coordinateCanonicalBijection _ i) tail.toMap
      (gamma_coordinateCanonical_graph _ hT.1 i) (ih hT.2)
  | focus D tail ih =>
    exact gamma_composition_graph D.toImage tail.toMap (gamma_fibre_eta_graph D hT.1 hT.2.1) (ih hT.2.2)

def gammaUniformTraceIso {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    GammaIso G (carrier A) (carrier B) := ⟨Equiv.ofBijective T.toMap T.bijective,GammaUniformTrace.graph T hT⟩

end IntegrationInACVF.Section5
