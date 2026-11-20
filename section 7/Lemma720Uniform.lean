import «section 7».Lemma720Cells

/-! Lemma 7.20, step 13: the uniform cell data.

For the second stage `T₂` (a unary stage on `B` with label-determined displacement), the
cell data are functions of the RV target point `u`:

* `Dof u`: the disc `c(u) + τ₂(u)^♯` of the second stage over `u`;
* `εU u`: the positioning map `epsHat` on the labels `wOf u` recovered from `u`;
* `tU u`: the leading label of `wOf u` (the paradigm);
* `σU u`: a slope of `εU u` on `Dof u` when one exists, and `t₁U u = σ⁻¹ · (rv(−1) · t)`;
* `kindU u = kindOf (Dof u) (εU u) (tU u)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Final
variable {B : DefSet (rawMixedSpace (M := M) 1 a) S} (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M)) (T₂ : StandardContractionStage (G := G) B)
  (hD₂ : SameLabelShearDisplacement T₂.lift (Fin.last 0))

/-- The labels of the first contracted set recovered from a target point. -/
def wOf (u : Fin T₂.arity → RVInfinity M) : Fin a → RVInfinity M := fun i => u (T₂.oldLabels i)

/-- The centre of the second-stage disc over a target point. -/
def cOf (u : Fin T₂.arity → RVInfinity M) : VF M :=
  if h : ((Fin.elim0 : Fin 0 → VF M), u) ∈ T₂.contracted.carrier then Stage.eps T₂ hD₂ ⟨_, h⟩ else 0

/-- The second-stage disc over a target point. -/
def Dof (u : Fin T₂.arity → RVInfinity M) : Set (VF M) := tdisc (cOf T₂ hD₂ u) (u T₂.leading)

/-- The positioning function over a target point. -/
def εU (u : Fin T₂.arity → RVInfinity M) : VF M → VF M :=
  fun x => epsHat B ε lead Q (mkPoint x (wOf T₂ u))

theorem rv_one_ne : rv M (1 : VF M) ≠ rvZero M := fun h => one_ne_zero ((rv_eq_zero_iff _).mp h)

/-- The paradigm over a target point. -/
def tU (u : Fin T₂.arity → RVInfinity M) : RV M :=
  if h : wOf T₂ u lead ≠ rvZero M then ⟨_, h⟩ else ⟨rv M 1, rv_one_ne⟩

/-- A slope of the positioning function, when one exists. -/
def σU (u : Fin T₂.arity → RVInfinity M) : RV M :=
  if h : ∃ σ : RV M, HasSlope (Dof T₂ hD₂ u) (εU ε lead Q T₂ u) σ then h.choose else tU lead T₂ u

/-- The second paradigm over a target point. -/
def t₁U (u : Fin T₂.arity → RVInfinity M) : RVInfinity M :=
  (σU ε lead Q T₂ hD₂ u).val⁻¹ * (rv M (-1) * (tU lead T₂ u).val)

/-- The kind over a target point. -/
def kindU (u : Fin T₂.arity → RVInfinity M) : Fin 3 :=
  kindOf (Dof T₂ hD₂ u) (εU ε lead Q T₂ u) (tU lead T₂ u)

end Final

end DiamondIntegral.Section7.Lemma720
