import «section 6».CoordinateGammaObstacles
import «section 6».CoordinateRootTerminationGeometry
import «section 6».FiniteCoordinateObstacles

/-! Root-free last-coordinate discs control a complete Gamma form.
Empty roots give descent through the retained coordinate projection;
neither an individual Gamma level nor a representative is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def CoordinateFormRootControl (R : CoordinateRootFamily A) (ω : Mixed M (n+1) r → Gamma M) : Prop :=
  ∀ (b : Fin n → VF M) (u : Fin r → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G),
    (∀ x ∈ Balls.openDisc Valued.v a ρ, (Fin.snoc b x,u) ∈ A.carrier) →
    (∀ x ∈ R.fibre b u, x ∉ Balls.openDisc Valued.v a ρ) →
    ∀ x ∈ Balls.openDisc Valued.v a ρ, ∀ y ∈ Balls.openDisc Valued.v a ρ,
      ω (Fin.snoc b x,u) = ω (Fin.snoc b y,u)

theorem coordinateFormRootControl_of_levels (R : CoordinateRootFamily A) (ω : Mixed M (n+1) r → Gamma M)
    (hLevels : ∀ γ, CoordinateRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ}) :
    CoordinateFormRootControl (G := G) R ω := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  have h := hLevels (ω (Fin.snoc b x,u)) b u a ρ hAmbient hAvoid x hx y hy
  exact ((h.mp ⟨hAmbient x hx,rfl⟩).2).symm

theorem CoordinateFormRootControl.levels {R : CoordinateRootFamily A} {ω : Mixed M (n+1) r → Gamma M}
    (h : CoordinateFormRootControl (G := G) R ω) (γ : Gamma M) :
    CoordinateRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  have he := h b u a ρ hAmbient hAvoid x hx y hy
  exact ⟨fun hγ => ⟨hAmbient y hy,he.symm.trans hγ.2⟩,
    fun hγ => ⟨hAmbient x hx,he.trans hγ.2⟩⟩

theorem CoordinateFormRootControl.mono {R Q : CoordinateRootFamily A} {ω : Mixed M (n+1) r → Gamma M}
    (h : CoordinateFormRootControl (G := G) R ω) (hRQ : R.roots.carrier ⊆ Q.roots.carrier) :
    CoordinateFormRootControl (G := G) Q ω :=
  coordinateFormRootControl_of_levels Q ω (fun γ => (h.levels γ).mono hRQ)

theorem CoordinateFormRootControl.empty_roots_projection_constant
    {R : CoordinateRootFamily A} {ω : Mixed M (n+1) r → Gamma M}
    (h : CoordinateFormRootControl (G := G) R ω)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEmpty : R.roots.carrier = ∅) (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, Fin.init p.1 = Fin.init q.1 → p.2 = q.2 → ω p = ω q := by
  intro p hp q hq hInit hTags
  let C := {x | x ∈ A.carrier ∧ ω x = ω p}
  have hSat := (h.levels (ω p)).empty_roots_coordinate_saturated hv hEmpty hA hD
    (fun _ hx => hx.1) p ⟨hp,rfl⟩ (q.1 (Fin.last n))
    (congrFun (hTag p hp q hq hTags) (Fin.last n)).symm
  have he : (Function.update p.1 (Fin.last n) (q.1 (Fin.last n)),p.2) = q := by
    apply Prod.ext
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.update_self]
      · simpa only [Function.update_of_ne (Fin.castSucc_ne_last j),Fin.init] using congrFun hInit j
    · exact hTags
  rw [he] at hSat
  exact hSat.2.symm

theorem exists_coordinate_form_controlling_roots
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (ω : Mixed M (n+1) r → Gamma M)
    (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω)) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧ CoordinateFormRootControl (G := G) R ω := by
  obtain ⟨R,N,hBound,hLevels⟩ := exists_coordinate_gamma_controlling_roots hc hs hsmall hv A hARV ω hGraph
  exact ⟨R,N,hBound,coordinateFormRootControl_of_levels R ω hLevels⟩

end DiamondIntegral.Section6
