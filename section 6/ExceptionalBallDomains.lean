import «section 6».ExceptionalBallCenters

/-! Every actual exceptional ball has the required product condition
on the current focus domain when its radius refines that domain's
invariance radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem sameRadius_value_close
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (OpenBallCodes.OpenBall M)) (s : VF M) (hR : SameOpenRadius (G := G) A s)
    (D : A) (c x : VF M) (hc : c ∈ vfOpenBall D.val) (hx : x ∈ vfOpenBall D.val) :
    vfValue s < vfValue (x-c) := by
  obtain ⟨a,ha⟩ := hR D.val D.property
  have hca : Valued.v (c-a) < Valued.v s := (Set.ext_iff.mp ha c).mp hc
  have hxa : Valued.v (x-a) < Valued.v s := (Set.ext_iff.mp ha x).mp hx
  have hxc : Valued.v (x-c) < Valued.v s :=
    (Balls.strictDisc_recenter_iff Valued.v a c x s hca).mpr hxa
  apply lt_of_not_ge
  intro hle
  have hp : VFValued.predV s (x-c) :=
    (Values.vf_pred_iff_gamma_le s (x-c)).mpr hle
  exact (not_le_of_gt hxc) ((hv s (x-c)).mp hp)

theorem exceptionalOpenBalls_product_domain
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : Set (Mixed M n r)) (δ : Gamma M)
    (hC : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre C u))
    (E : Set (Fin 1 → VF M)) (s : VF M) (hs : s ≠ 0) (hδs : δ.val ≤ vfValue s)
    (c : exceptionalOpenBalls E s hs → VF M)
    (hc : ∀ D, c D ∈ vfOpenBall D.val) (i : Fin n) :
    ∀ D : exceptionalOpenBalls E s hs, CoordinateProductDomain C (vfOpenBall D.val) (c D) i := by
  intro D
  apply coordinateProductDomain_of_invariant C (vfOpenBall D.val) (c D) i δ hC
  intro x hx
  exact hδs.trans_lt (sameRadius_value_close hv _ s
    (exceptionalOpenBalls_sameRadius hv E s hs) D (c D) x (hc D) hx)

end DiamondIntegral.Section6.FMT
