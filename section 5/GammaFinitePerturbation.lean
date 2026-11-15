import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ZPow
import Mathlib.Topology.Order.DenselyOrdered

/-! Finite Laurent value comparisons remain unchanged under a small
nontrivial perturbation unless two different slopes meet. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical Filter Set
open scoped Topology
namespace DiamondIntegral.Section5.GammaFinitePerturbation
variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
variable [TopologicalSpace G] [OrderTopology G]

theorem comparison_eventually (a b : G) (p q : ℤ) (h : a = b → p = q) :
    ∀ᶠ e in 𝓝 (1 : G), (a * e ^ p ≤ b * e ^ q ↔ a ≤ b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hc : Continuous (fun e : G => a * e ^ p) := continuous_const.mul (continuous_id.zpow p)
    have hd : Continuous (fun e : G => b * e ^ q) := continuous_const.mul (continuous_id.zpow q)
    have ho := (isOpen_lt hc hd).mem_nhds (show a * (1 : G)^p < b * 1^q from by simpa using hab)
    filter_upwards [ho] with e he
    exact iff_of_true (le_of_lt he) (le_of_lt hab)
  · have hpq := h hab
    subst b q
    exact Eventually.of_forall (fun _ => iff_of_true le_rfl le_rfl)
  · have hc : Continuous (fun e : G => a * e ^ p) := continuous_const.mul (continuous_id.zpow p)
    have hd : Continuous (fun e : G => b * e ^ q) := continuous_const.mul (continuous_id.zpow q)
    have ho := (isOpen_lt hd hc).mem_nhds (show b * (1 : G)^q < a * 1^p from by simpa using hab)
    filter_upwards [ho] with e he
    exact iff_of_false (not_le.mpr he) (not_le.mpr hab)

theorem finite_comparisons [DenselyOrdered G] [NoMaxOrder G]
    {J : Type*} (s : Finset J) (a : J → G) (p : J → ℤ)
    (h : ∀ i ∈ s,∀ j ∈ s,a i = a j → p i = p j) :
    ∃ e : G, 1 < e ∧ ∀ i ∈ s,∀ j ∈ s,
      (a i * e ^ p i ≤ a j * e ^ p j ↔ a i ≤ a j) := by
  have he : ∀ᶠ e in 𝓝 (1 : G),∀ i ∈ s,∀ j ∈ s,
      (a i * e ^ p i ≤ a j * e ^ p j ↔ a i ≤ a j) := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    apply (Filter.eventually_all_finset s).mpr
    intro j hj
    exact comparison_eventually (a i) (a j) (p i) (p j) (h i hi j hj)
  have ht : ∀ᶠ e in 𝓝[>] (1 : G),∀ i ∈ s,∀ j ∈ s,
      (a i * e ^ p i ≤ a j * e ^ p j ↔ a i ≤ a j) := he.filter_mono nhdsWithin_le_nhds
  obtain ⟨e,he,hpos⟩ := (ht.and self_mem_nhdsWithin).exists
  exact ⟨e,hpos,he⟩

end DiamondIntegral.Section5.GammaFinitePerturbation
