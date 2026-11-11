import «section 2».DiscPoints
import «section 2».DiscGeometry

/-! The three unary shapes in Lemma 2.27. The thin-annulus definition
is the author-approved R163 clarification. Open discs use finite Gamma
radii and never the upstream legacy singleton alternative. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def IsOpenDisc (D : Set M) : Prop :=
  ∃ a : VF M, ∃ γ : Gamma M, D = BallImaginaries.underlying (openDiscCode a γ)

def IsClosedDisc (D : Set M) : Prop :=
  ∃ C : ClosedDC M, D = ClosedBallCodes.underlying C

def thinAnnulus (a : VF M) (γ : Gamma M) : Set M :=
  BallImaginaries.underlying (closedDiscCode a γ.val) \
    BallImaginaries.underlying (openDiscCode a γ)

def IsThinAnnulus (D : Set M) : Prop :=
  ∃ a : VF M, ∃ γ : Gamma M, D = thinAnnulus a γ

def IsPrimitiveDisc (D : Set M) : Prop :=
  IsOpenDisc D ∨ IsClosedDisc D ∨ IsThinAnnulus D

private theorem thinAnnulus_points_valuation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) (a : VF M) (γ : Gamma M) :
    {x : VF M | x.val ∈ thinAnnulus a γ} = {x | vfValue (x - a) = γ.val} := by
  let r := radiusRepresentative γ.val
  have hval : vfValue r = γ.val := radiusRepresentative_value _
  have hr : r ≠ 0 := fun hz => γ.property ((radiusRepresentative_zero_iff _).mp hz)
  have hf : finiteValue r hr = γ := Subtype.ext hval
  have hclosed : discPoints (closedDiscCode a γ.val) = {x | v (x - a) ≤ v r} := by
    rw [← hval]
    exact closedDiscCode_points v hv a r
  have hopen : discPoints (openDiscCode a γ) = {x | v (x - a) < v r} := by
    rw [← hf]
    exact openDiscCode_points v hv a r hr
  ext x
  have he : vfValue (x - a) = γ.val ↔ v (x - a) = v r := by
    rw [← hval]
    exact vfValue_eq_iff v hv (x - a) r
  change (x ∈ discPoints (closedDiscCode a γ.val) ∧ x ∉ discPoints (openDiscCode a γ)) ↔ _
  rw [hclosed, hopen]
  change (v (x - a) ≤ v r ∧ ¬ v (x - a) < v r) ↔ vfValue (x - a) = γ.val
  rw [he]
  exact ⟨fun h => le_antisymm h.1 (le_of_not_gt h.2), fun h => ⟨h.le, not_lt_of_ge h.ge⟩⟩

/-- The approved geometric definition agrees with the valuative shell
description, using an actual finite Gamma value. -/
theorem thinAnnulus_points (a : VF M) (γ : Gamma M) :
    {x : VF M | x.val ∈ thinAnnulus a γ} = {x | vfValue (x - a) = γ.val} := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  exact thinAnnulus_points_valuation v hv a γ

end DiamondIntegral.Section2
