import IntegrationSection5.FiniteStandardContractionData
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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n l : ℕ}

theorem gamma_toFirstVolume_graph (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l)
    (hD : GammaSetDefinable G {p : Point (M := M) 0 l | p.2 ∈ carrier D}) :
    GammaGraphDefinable G (rvMapGraph (toFirstVolume D ρ)) := by
  let f := rvCoordinatePointMap (prependVolumeIndex ρ) G.real
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hD ((gammaLogicInput G).real_map_graph f))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    refine ⟨⟨p.2,hp⟩,rfl,?_⟩
    have hv : a.val.2 ∘ prependVolumeIndex ρ = q.2 := congrArg Prod.snd hq
    exact (congrArg (fun z : Point (M := M) 0 l => z.2 ∘ prependVolumeIndex ρ) ha).symm.trans hv
  · rintro ⟨u,hu,hq⟩
    have hp : p.2 ∈ carrier D := hu ▸ u.property
    refine ⟨hp,⟨p,Set.mem_univ _⟩,rfl,?_⟩
    exact Prod.ext (Subsingleton.elim _ _)
      ((congrArg (fun z => z ∘ prependVolumeIndex ρ) hu).symm.trans hq)

def gamma_firstVolumeIso (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l)
    (hD : GammaSetDefinable G {p : Point (M := M) 0 l | p.2 ∈ carrier D}) :
    GammaRVIso G (selectedVolumeObject D ρ) (firstVolumeObject D ρ) :=
  GammaRVIso.ofVolumePreserving (toFirstVolume D ρ) (toFirstVolume_bijective D ρ)
    (toFirstVolume_volume D ρ) (gamma_toFirstVolume_graph D ρ hD)

def FiniteStandardContractionData.gammaNormalizationIso {n m : ℕ} {A : Set (Point (M := M) n m)}
    {σ : Equiv.Perm (Fin n)} (D : FiniteStandardContractionData G A σ) :
    GammaRVFiniteIso G D.rvObject D.normalizedRVObject :=
  GammaRVIso.toFinite (gamma_firstVolumeIso (Map.image (rawLabelMap D.contraction.target)) D.contraction.volumeIndex
    (D.contraction.gamma_rv_domain (gamma_program_final_set D.contraction.program D.program_gamma)))
    D.finite_volume D.finite_normalized_volume

end IntegrationInACVF.Section5
