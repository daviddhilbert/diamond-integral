import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryGammaObstacles

/-! (Row-form version for Remark 6.20, translated from `UnaryFormRootControl`.)
 Root-free-disc control of an entire Gamma form, rather than a finite
list of its levels. This is equivalent to simultaneous level control and
at zero roots gives actual RV-label constancy on a tagged pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def UnaryFormRootControlRow (R : UnaryRootFamily A) (ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier) : Prop :=
  ∀ (u : Fin r → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G),
    (∀ x ∈ Balls.openDisc Valued.v a ρ, ((fun _ : Fin 1 => x),u) ∈ A.carrier) →
    (∀ x ∈ R.fibre u, x ∉ Balls.openDisc Valued.v a ρ) →
    ∀ x ∈ Balls.openDisc Valued.v a ρ, ∀ y ∈ Balls.openDisc Valued.v a ρ,
      ω ((fun _ : Fin 1 => x),u) = ω ((fun _ : Fin 1 => y),u)

theorem unaryFormRootControl_of_levels_row (R : UnaryRootFamily A) (ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier)
    (hLevels : ∀ γ, UnaryRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ}) :
    UnaryFormRootControlRow (G := G) R ω := by
  intro u a ρ hAmbient hAvoid x hx y hy
  have h := (hLevels (ω ((fun _ : Fin 1 => x),u))) u a ρ hAmbient hAvoid x hx y hy
  exact ((h.mp ⟨hAmbient x hx,rfl⟩).2).symm

theorem UnaryFormRootControlRow.levels {R : UnaryRootFamily A} {ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier}
    (h : UnaryFormRootControlRow (G := G) R ω) (γ : Set (rawRVSpace (M := M) qR).Carrier) :
    UnaryRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  intro u a ρ hAmbient hAvoid x hx y hy
  have he := h u a ρ hAmbient hAvoid x hx y hy
  exact ⟨fun hγ => ⟨hAmbient y hy,he.symm.trans hγ.2⟩,fun hγ => ⟨hAmbient x hx,he.trans hγ.2⟩⟩

theorem UnaryFormRootControlRow.empty_roots_tag_constant
    {R : UnaryRootFamily A} {ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier}
    (h : UnaryFormRootControlRow (G := G) R ω)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hRoots : R.roots.carrier = ∅) (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → ω p = ω q := by
  intro p hp q hq hTags
  let C := {x | x ∈ A.carrier ∧ ω x = ω p}
  have hC : IsRVPullback C := (h.levels (ω p)).empty_roots_rvPullback hv hRoots hA hD (fun _ hx => hx.1)
  have hqC : q ∈ C := rvPullback_mem_of_sameRV hC ⟨hp,rfl⟩ (hTag p hp q hq hTags) hTags
  exact hqC.2.symm

theorem exists_unary_form_controlling_roots_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier)
    (hGraph : MixedRowGraphDefinable S A.carrier ω) :
    ∃ R : UnaryRootFamily A, ∃ N : ℕ, (∀ u, (R.fibre u).card ≤ N) ∧ UnaryFormRootControlRow (G := G) R ω := by
  obtain ⟨R,N,hBound,hLevels⟩ := exists_unary_gamma_controlling_roots_row hc hv A ω hGraph
  exact ⟨R,N,hBound,unaryFormRootControl_of_levels_row R ω hLevels⟩

end DiamondIntegral.Section6
