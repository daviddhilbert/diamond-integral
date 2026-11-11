import «section 2».Conventions
import Section3.GeneralBallCenters

set_option backward.isDefEq.respectTransparency false

/-!
# §2.1, `disc:exp`, R024: uniform open and closed disc codes

`DC` reuses the quotient of both real code charts by equality of point sets.
Each map takes its radius as an argument. A chosen radius representative is
internal to the construction; the specifications show it does not affect the
disc. Open radii are actual finite Gamma imaginaries. Closed radii also
include infinity, which codes the singleton closed disc. No open disc has
radius infinity.
-/

noncomputable section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev DC := BallImaginaries.Ball M

def discPoints (D : DC (M := M)) : Set (VF M) :=
  {a | a.val ∈ BallImaginaries.underlying D}

def radiusRepresentative (γ : GammaInfinity M) : VF M :=
  Classical.choose (vfValue_surjective γ)

theorem radiusRepresentative_value (γ : GammaInfinity M) :
    vfValue (radiusRepresentative γ) = γ := Classical.choose_spec (vfValue_surjective γ)

theorem radiusRepresentative_zero_iff (γ : GammaInfinity M) :
    radiusRepresentative γ = 0 ↔ γ = Values.infinity (M := M) := by
  rw [← vfValue_eq_infinity_iff, radiusRepresentative_value]

private def closedChart (a r : VF M) : ClosedBallCodes.ClosedBall M :=
  Quotient.mk _ ⟨![a.val, r.val, (1 : VF M).val], by
    intro i
    fin_cases i
    · exact a.property
    · exact r.property
    · exact (1 : VF M).property⟩

private def openChart (a r : VF M) (hr : r ≠ 0) : OpenBallCodes.OpenBall M :=
  Quotient.mk _ ⟨![a.val, r.val], ⟨by
    intro i
    fin_cases i
    · exact a.property
    · exact r.property, fun he => hr (Subtype.ext he)⟩⟩

def closedDiscCode (a : VF M) (γ : GammaInfinity M) : DC (M := M) :=
  BallImaginaries.ofClosed (closedChart a (radiusRepresentative γ))

def openDiscCode (a : VF M) (γ : Gamma M) : DC (M := M) :=
  BallImaginaries.ofOpen (openChart a (radiusRepresentative γ.val)
    (fun he => γ.property ((radiusRepresentative_zero_iff γ.val).mp he)))

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (VF M) Γ₀)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)

include hv

private theorem closedChart_points (a r : VF M) :
    discPoints (BallImaginaries.ofClosed (closedChart a r)) =
      Balls.closedDisc v a (↑(OrderDual.toDual (v r))) := by
  apply ClosedBallCodes.ball_eq_closed v hv
    ![a.val, r.val, (1 : VF M).val]
    (by intro i; fin_cases i; exact a.property; exact r.property; exact (1 : VF M).property)
  intro he
  exact (one_ne_zero : (1 : VF M) ≠ 0) (Subtype.ext he)

private theorem openChart_points (a r : VF M) (hr : r ≠ 0) :
    discPoints (BallImaginaries.ofOpen (openChart a r hr)) =
      {x | v (x - a) < v r} := by
  exact OpenBallCodes.ball_eq_open v hv ![a.val, r.val]
    ⟨by intro i; fin_cases i; exact a.property; exact r.property,
      fun he => hr (Subtype.ext he)⟩

theorem closedDiscCode_points (a r : VF M) :
    discPoints (closedDiscCode a (vfValue r)) =
      Balls.closedDisc v a (↑(OrderDual.toDual (v r))) := by
  have he : v (radiusRepresentative (vfValue r)) = v r :=
    (vfValue_eq_iff v hv _ r).mp (radiusRepresentative_value _)
  simpa only [closedDiscCode, he] using
    closedChart_points v hv a (radiusRepresentative (vfValue r))

theorem openDiscCode_points (a r : VF M) (hr : r ≠ 0) :
    discPoints (openDiscCode a (finiteValue r hr)) =
      Balls.openDisc v a (Balls.openRadius (v r) ((map_ne_zero v).mpr hr)) := by
  have hrep : radiusRepresentative (vfValue r) ≠ 0 := by
    intro he
    exact hr ((vfValue_eq_infinity_iff r).mp ((radiusRepresentative_zero_iff _).mp he))
  have he : v (radiusRepresentative (vfValue r)) = v r :=
    (vfValue_eq_iff v hv _ r).mp (radiusRepresentative_value _)
  simpa only [openDiscCode, finiteValue, he, Balls.openDisc_openRadius] using
    openChart_points v hv a (radiusRepresentative (vfValue r)) hrep

/-- Radius infinity belongs to the closed chart and codes precisely a point. -/
theorem closedDiscCode_infinity_points (a : VF M) :
    discPoints (closedDiscCode a (Values.infinity (M := M))) = {a} := by
  have hz : vfValue (0 : VF M) = Values.infinity (M := M) :=
    (vfValue_eq_infinity_iff _).mpr rfl
  have he := closedDiscCode_points v hv a 0
  rw [hz, Valuation.map_zero] at he
  exact he.trans (Balls.closedDisc_infinity v a)

/-- A finite radius needs the open/closed tag: its two origin discs differ. -/
theorem openDiscCode_ne_closedDiscCode (r : VF M) (hr : r ≠ 0) :
    openDiscCode (0 : VF M) (finiteValue r hr) ≠ closedDiscCode 0 (vfValue r) := by
  intro he
  have hp := congrArg discPoints he
  rw [openDiscCode_points v hv _ _ hr, closedDiscCode_points v hv] at hp
  have hc : r ∈ Balls.closedDisc v (0 : VF M) (↑(OrderDual.toDual (v r))) := by
    change v (r - 0) ≤ v r
    simp
  have ho : r ∈ Balls.openDisc v (0 : VF M) (Balls.openRadius (v r) ((map_ne_zero v).mpr hr)) := hp.symm ▸ hc
  simpa only [Balls.openDisc_openRadius, Set.mem_ofPred_eq, sub_zero, lt_self_iff_false] using ho

end DiamondIntegral.Section2
