import IntegrationSection5.ActiveUnaryProjection
import IntegrationSection5.GammaGraphOperations

/-! The selected-coordinate lift retains the complete original-Gamma
locus and centre graphs, including all free passive coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ}

theorem gamma_activeUnaryProjection_preimage (i : Fin n) (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) 1 m)) (hD : GammaSetDefinable G D) :
    GammaSetDefinable G {p | activeUnaryProjection i ρ p ∈ D} := by
  let X := PresentedSet.univ (pointSpace (M := M) n l) G.real
  have h := (gammaLogicInput G).preimage_real (activeUnaryProjectionMap i ρ X) hD
  convert h using 1
  ext p
  exact ⟨fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩,fun ⟨a,ha,hp⟩ => ha ▸ hp⟩

theorem gamma_coordinateLift_focus {A : DefSet (M := M) S 1 m}
    {H : DefSet (M := M) S n l} {k : Fin m}
    (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A)
    (hH : GammaSetDefinable G (carrier H)) (hD : GammaFocusDefinable G D) :
    GammaFocusDefinable G (Focus.coordinateLift D i ρ hHA) := by
  let L := gammaLogicInput G
  refine ⟨L.inter (gamma_activeUnaryProjection_preimage i ρ D.locus hD.1) (L.hull hH),?_⟩
  let X := PresentedSet.univ (pointSpace (M := M) n l) G.real
  have h := L.restrict_graph hH (L.comp_graph (L.real_map_graph (activeUnaryProjectionMap i ρ X)) hD.2)
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,q,⟨a,ha,hq⟩,hqA,hz⟩
    have he : q = activeUnaryProjection i ρ p := by
      exact hq.symm.trans (congrArg (activeUnaryProjection i ρ) ha)
    rw [he] at hqA hz
    exact ⟨⟨hp,hqA.2,subset_hull _ hp⟩,hz⟩
  · rintro ⟨⟨hp,hd,hh⟩,hz⟩
    exact ⟨hp,activeUnaryProjection i ρ p,⟨⟨p,Set.mem_univ _⟩,rfl,rfl⟩,⟨hHA p hp,hd⟩,hz⟩

end IntegrationInACVF.Section5
