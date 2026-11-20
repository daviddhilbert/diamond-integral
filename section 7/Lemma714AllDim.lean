import «section 7».Lemma714FibreStep

/-! Lemma 7.14, part 43: Lemma 7.14 for prepared contraction data in every VF
dimension, by induction (`lemma714P_all`): the case of one coordinate
(`lemma714P_zero`) and the step (`step_of_fibre` with `pullFibres`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace DiamondIntegral.Section7.Lemma714Reduce

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (DiamondIntegral.Section2.VF M) G]

theorem lemma714P_succ {m : ℕ} (IH : Lemma714P M G m) : Lemma714P M G (m + 1) := by
  intro hc h00 κ hκ hs hv T V hV hVT hTV hnt hsmall hΓ r' r'' k A' A'' ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
    hNZ' hNZ'' hFibre D' D''
  exact step_of_fibre hc h00 hκ hs hv T hsmall hΓ π' π'' hFin' hFin'' hNZ' hNZ'' D' D'' IH V hV hVT hTV hnt
    hA' hA'' hVF (pullFibres hc h00 hκ hs hv T hsmall hΓ π' π'' hFin' hFin'' hNZ' hNZ'' D' D'' V hV hVT hTV hnt
      hA' hA'' hVF hFibre)

/-- **Lemma 7.14 for prepared contraction data, in every VF dimension.** -/
theorem lemma714P_all : ∀ n, Lemma714P M G n
  | 0 => lemma714P_zero
  | m + 1 => lemma714P_succ (lemma714P_all m)

end DiamondIntegral.Section7.Lemma714Reduce
