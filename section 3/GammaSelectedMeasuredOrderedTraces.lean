import «section 3».GammaSelectedMeasuredHeads
import «section 3».GammaSelectedOrderedTraces

/-! Ordered contraction induction for specified measured Gamma head steps.
Each trace is an actual sequence of original-base traced preparations;
no contraction comparison is a field of its certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)

inductive GammaSelectedMeasuredOrderedTrace :
    {n k l : ℕ} → GammaSelectedRetainedData hc B n (k+1) → GammaSelectedRetainedData hc B 0 (l+1) → Type
  | zero {k} (U : GammaSelectedRetainedData hc B 0 (k+1)) : GammaSelectedMeasuredOrderedTrace U U
  | step {n k l} {U : GammaSelectedRetainedData hc B (n+1) (k+1)}
      {V : GammaSelectedRetainedData hc B 0 (l+1)} (T : GammaSelectedMeasuredHead U)
      (tail : GammaSelectedMeasuredOrderedTrace (n := n) (k := 1+k) (l := l) (T.next hκ hs hr) V) : GammaSelectedMeasuredOrderedTrace U V

namespace GammaSelectedMeasuredOrderedTrace
variable {hκ hs hr}

theorem degree {n k l : ℕ} {U : GammaSelectedRetainedData hc B n (k+1)}
    {V : GammaSelectedRetainedData hc B 0 (l+1)} (T : GammaSelectedMeasuredOrderedTrace hκ hs hr U V) :
    l+1 = n+(k+1) := by
  induction T with
  | zero U => omega
  | step T tail ih => omega

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem exists_original_base (hunc : Cardinal.aleph0 < κ) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∀ (n k : ℕ) (U : GammaSelectedRetainedData hc B n (k+1)),
      ∃ l : ℕ, ∃ V : GammaSelectedRetainedData hc B 0 (l+1), Nonempty (GammaSelectedMeasuredOrderedTrace hκ hs hr U V) := by
  intro n
  induction n with
  | zero =>
    intro k U
    exact ⟨k,U,⟨.zero U⟩⟩
  | succ n ih =>
    intro k U
    obtain ⟨T₀⟩ := GammaSelectedTracedHead.exists_original_base hunc hs h00 hr U
    let T := GammaSelectedMeasuredHead.ofTraced hκ hs hr hv T₀
    obtain ⟨l,V,tail⟩ := ih (1+k) (T.next hκ hs hr)
    exact ⟨l,V,⟨.step T tail.some⟩⟩

theorem preserves_generic_geometry
    (hunc : Cardinal.aleph0 < κ) (h00 : M ⊨ Axioms.ACVF00) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n k l : ℕ} {U V : GammaSelectedRetainedData hc B n (k+1)}
    {A D : GammaSelectedRetainedData hc B 0 (l+1)}
    (T : GammaSelectedMeasuredOrderedTrace hκ hs hr U A) :
    ∀ E : GammaSelectedMeasuredOrderedTrace hκ hs hr V D,
      GammaGenericSelectedRelated U V → GammaGenericSelectedRelated A D := by
  induction T with
  | zero U =>
    intro E h
    cases E with
    | zero V => exact h
  | step T tail ih =>
    intro E h
    cases E with
    | step E etail =>
      exact ih etail (h.measured_head hunc hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1 T E)

end GammaSelectedMeasuredOrderedTrace
end DiamondIntegral.Section3
