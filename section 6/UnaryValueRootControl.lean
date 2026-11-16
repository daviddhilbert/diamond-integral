import «section 6».UnaryInverseIsometry

/-! Root control for the complete value of arbitrary data, including
powerset-valued RV rows with no bound on the RV output. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ} {T : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
def UnaryValueRootControl (R : UnaryRootFamily A) (ω : Mixed M 1 r → T) : Prop :=
  ∀ (u : Fin r → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G),
    (∀ x ∈ Balls.openDisc Valued.v a ρ, ((fun _ : Fin 1 => x),u) ∈ A.carrier) →
    (∀ x ∈ R.fibre u, x ∉ Balls.openDisc Valued.v a ρ) →
    ∀ x ∈ Balls.openDisc Valued.v a ρ, ∀ y ∈ Balls.openDisc Valued.v a ρ,
      ω ((fun _ : Fin 1 => x),u) = ω ((fun _ : Fin 1 => y),u)

theorem unaryValueRootControl_of_levels (R : UnaryRootFamily A) (ω : Mixed M 1 r → T)
    (hLevels : ∀ γ : T, UnaryRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ}) :
    UnaryValueRootControl (G := G) R ω := by
  intro u a ρ hAmbient hAvoid x hx y hy
  have h := (hLevels (ω ((fun _ : Fin 1 => x),u))) u a ρ hAmbient hAvoid x hx y hy
  exact ((h.mp ⟨hAmbient x hx,rfl⟩).2).symm

theorem UnaryValueRootControl.levels {R : UnaryRootFamily A} {ω : Mixed M 1 r → T}
    (h : UnaryValueRootControl (G := G) R ω) (γ : T) :
    UnaryRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  intro u a ρ hAmbient hAvoid x hx y hy
  have he := h u a ρ hAmbient hAvoid x hx y hy
  exact ⟨fun hγ => ⟨hAmbient y hy,he.symm.trans hγ.2⟩,fun hγ => ⟨hAmbient x hx,he.trans hγ.2⟩⟩

theorem UnaryValueRootControl.empty_roots_tag_constant
    {R : UnaryRootFamily A} {ω : Mixed M 1 r → T}
    (h : UnaryValueRootControl (G := G) R ω)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hRoots : R.roots.carrier = ∅) (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → ω p = ω q := by
  intro p hp q hq hTags
  let C := {x | x ∈ A.carrier ∧ ω x = ω p}
  have hC : IsRVPullback C := (h.levels (ω p)).empty_roots_rvPullback hv hRoots hA hD (fun _ hx => hx.1)
  have hqC : q ∈ C := rvPullback_mem_of_sameRV hC ⟨hp,rfl⟩ (hTag p hp q hq hTags) hTags
  exact hqC.2.symm

end DiamondIntegral.Section6
