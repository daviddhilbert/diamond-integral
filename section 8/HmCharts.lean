import «section 8».HmLattice
import «section 8».PuiseuxPolynomials
import FubiniTheorems.Fubini.NativeRESChartClasses
import FubiniTheorems.Decomposition.ElementaryRESExtension
import FubiniTheorems.Prerequisites.Euler.RVFamilyDisjointPresentation
import FubiniTheorems.Prerequisites.Euler.RVBoundedDisjointPresentation

/-! The value of `h_m` on a bounded chart (Lemma 8.2 as the definition).

For a bounded chart `a` and `m ≥ 1`,
`hmValue a m = ∑_w Θ([U^{(m)}_w]) T^{-m w}`,
the sum running over the finitely many weights `w` of the lattice part `U^{(m)}` of the domain,
where `U^{(m)}_w` (`fibreChart`) is the lattice part with weight `w`, an RES chart; `Θ` is the
comparison `RESDimensionFreeReduction.Ring B ≃+* ModifiedRing` of the library (`theta`); and
`T^{-m w}` is the monomial with the rational exponent `-m · ratValue π w`.

`hmValue_eq_sum`: the sum may be taken over any finite superset of the weights. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues
open DiamondIntegral.Section8.ValueMaps DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-- `Θ` for the base of Section 8. -/
def theta : RESDimensionFreeReduction.Ring (base P) ≃+* EquivariantVariety.ModifiedRing :=
  ambientPuiseuxComparisonEquiv P.hc P.e (base P) P.hB (fun _ h => absurd h (Set.notMem_empty _))

/-- A bounded chart, as a structure. -/
abbrev bdd {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a) :
    RVBoundedCharts.BoundedChart (base P) k := ⟨a, ha⟩

/-- The lattice part with weight `w`. -/
def latticeFibre {k : ℕ} (a : Chart (base P) k) (m : ℕ) (w : Γ) : Set (Fin a.arity → P.N) :=
  {u | u ∈ latticeDomain P a m ∧ a.correctedWeight u = w}

theorem latticeFibre_definable' {k : ℕ} (a : Chart (base P) k)
    (ha : RVMeasuredBounds.DomainBounded a) (m : ℕ+) (w : Γ) :
    DefinableOverBase (base P) (fun _ : Fin a.arity => .rv) (latticeFibre P a m w) :=
  latticeFibre_definable P (bdd P a ha) m.ne_zero w

theorem fibre_finite_values {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (w : Γ) :
    (Set.range (RVChartRestrictions.restrict (RVChartDisjointUnion.ofChart a) (latticeFibre P a m w)
      (latticeFibre_definable' P a ha m w) (fun _ hu => hu.1.1)).toChart.valuePattern).Finite := by
  obtain ⟨N, hN⟩ := chart_pow_bound P (bdd P a ha)
  let S : Set (Values.GammaTop (M := P.N)) :=
    insert Values.infinity (Subtype.val '' latticeBox P m N)
  have hS : S.Finite := ((latticeBox_finite P m.ne_zero N).image _).insert _
  refine (Set.Finite.pi (t := fun _ : Fin a.arity => S) fun _ => hS).subset ?_
  rintro p ⟨u, rfl⟩ i -
  have hu := u.property
  have hbox := latticeDomain_eq_box P (bdd P a ha) m N hN
  have hl0 : u.val ∈ latticeDomain P (bdd P a ha).toChart m := hu.1
  have hl := (Set.ext_iff.mp hbox u.val).mp hl0
  set t : CanonicalRV.RVSort P.N := ⟨u.val i, _⟩
  by_cases h0 : t.val = iRVZero
  · exact Or.inl ((Values.vrv_eq_infinity_iff t).mpr h0)
  · right
    refine ⟨codeValue t.val, hl.2 i, ?_⟩
    show (codeValue t.val).val = Values.vrv t
    have hf := RVMeasuredBounds.finiteValue_vrv t
    have hne : Values.vrv t ≠ Values.infinity := fun h => h0 ((Values.vrv_eq_infinity_iff t).mp h)
    rw [← hf]
    simp only [RVMeasuredBounds.finiteValue, hne, ne_eq, not_false_eq_true, ↓reduceDIte]

/-- The lattice part with weight `w`, as an RES chart. -/
def fibreChart {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a) (m : ℕ+)
    (w : Γ) : RESChart (base P) k :=
  ⟨(RVChartRestrictions.restrict (RVChartDisjointUnion.ofChart a) (latticeFibre P a m w)
      (latticeFibre_definable' P a ha m w) (fun _ hu => hu.1.1)).toChart,
    fibre_finite_values P a ha m w⟩

theorem fibreChart_domain {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (w : Γ) : (fibreChart P a ha m w).domain = latticeFibre P a m w := rfl

/-- The weights occurring on the lattice part, as a finite set. -/
def weights {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a) (m : ℕ+) :
    Finset Γ :=
  (latticeWeights_finite P (bdd P a ha) m.ne_zero).toFinset

theorem mem_weights {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (w : Γ) : w ∈ weights P a ha m ↔ (latticeFibre P a m w).Nonempty := by
  simp only [weights, Set.Finite.mem_toFinset]
  exact ⟨fun ⟨u, hu, huw⟩ => ⟨u, hu, huw⟩, fun ⟨u, hu, huw⟩ => ⟨u, hu, huw⟩⟩

/-- The term of `h_m` of weight `w`. -/
def hmTerm {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a) (m : ℕ+)
    (w : Γ) : PuiseuxPolynomial EquivariantVariety.ModifiedRing :=
  AddMonoidAlgebra.single (-(m : ℚ) * ratValue π w)
    (theta P (nativeRESChartClass (fibreChart P a ha m w)))

/-- **`h_m` on a bounded chart.** -/
def hmValue {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a) (m : ℕ+) :
    PuiseuxPolynomial EquivariantVariety.ModifiedRing :=
  ∑ w ∈ weights P a ha m, hmTerm P a ha m w

theorem hmTerm_eq_zero {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (w : Γ) (hw : w ∉ weights P a ha m) : hmTerm P a ha m w = 0 := by
  have he : (fibreChart P a ha m w).domain = ∅ := by
    rw [fibreChart_domain]
    exact Set.not_nonempty_iff_eq_empty.mp fun h => hw ((mem_weights P a ha m w).mpr h)
  simp [hmTerm, nativeRESChartClass_empty _ he]

/-- The sum defining `h_m` may be taken over any finite superset of the weights. -/
theorem hmValue_eq_sum {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (S : Finset Γ) (hS : weights P a ha m ⊆ S) :
    hmValue P a ha m = ∑ w ∈ S, hmTerm P a ha m w :=
  Finset.sum_subset hS fun w _ hw => hmTerm_eq_zero P a ha m w hw

/-- `h_m` vanishes on empty charts. -/
theorem hmValue_empty {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (h : a.domain = ∅) : hmValue P a ha m = 0 := by
  rw [hmValue_eq_sum P a ha m ∅ fun w hw => ?_]
  · simp
  · obtain ⟨u, hu, -⟩ := (mem_weights P a ha m w).mp hw
    have : u ∈ a.domain := hu.1
    rw [h] at this
    exact absurd this (Set.notMem_empty u)

end DiamondIntegral.Section8.Hm
