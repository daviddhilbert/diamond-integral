import «section 7».Lemma714PromoteMoves

/-! Lemma 7.14, part 8: the chart schema of a family of RV fibres.

For a `T`-definable mixed set `A ⊆ VFᵐ × RVʳ` with a Γ-form `ω` and head-start
labels `π : Fin k → Fin r`, `famSchema` is the chart schema over `BT T` with
VF parameters whose row at `a` is the fibre `A_a`:

* structural map `u ↦ u ∘ π`;
* volume `u ↦ ω(a, u)`.

This is the chart of `fibreObject T A ω a π` (Section 7, `FibreObjects`). The
family is valid at every point with a doubly bounded fibre, for a fibre bound
chosen by saturation (`famSchema_valid`). The fibre object over `S⟨a⟩` is
identified with the extended row by the identity map (`fibre_iso_famRow`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {m r k : ℕ}

/-- VF parameter sorts. -/
abbrev vfs (m : ℕ) : Fin m → SortTag := fun _ => .vf

/-- The raw domain of the family. -/
def famDomain (A : DefSet (rawMixedSpace (M := M) m r) S) : Set (Fin (m + r) → M) := mixedTuple '' A.carrier

theorem mixedTuple_sorted (x : Mixed M m r) : ∀ i, sortEval (Fin.append (vfs m) (rvs r) i) (mixedTuple x i) := by
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [mixedTuple, Fin.append_left]
    exact (x.1 l).property
  · simp only [mixedTuple, Fin.append_right]
    exact (x.2 l).property

include hc in
theorem famDomain_definable (A : DefSet (rawMixedSpace (M := M) m r) S) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (Fin.append (vfs m) (rvs r)) (famDomain A) :=
  real_base hc ((mixedTuple_image_definable_iff _).mpr A.definable) (by
    rintro _ ⟨x, -, rfl⟩
    exact mixedTuple_sorted x)

/-- The index map `(z, u) ↦ (z, u, u ∘ π)`. -/
def famCoordIdx (m r k : ℕ) (π : Fin k → Fin r) : Fin ((m + r) + k) → Fin (m + r) :=
  Fin.append id (fun i => Fin.natAdd m (π i))

/-- The raw graph of the structural map `u ↦ u ∘ π` of the family. -/
def famCoord (A : DefSet (rawMixedSpace (M := M) m r) S) (π : Fin k → Fin r) : Set (Fin ((m + r) + k) → M) :=
  (fun x => x ∘ famCoordIdx m r k π) '' famDomain A

include hc in
theorem famCoord_definable (A : DefSet (rawMixedSpace (M := M) m r) S) (π : Fin k → Fin r) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (Fin.append (Fin.append (vfs m) (rvs r)) (rvs k)) (famCoord A π) := by
  have h := (famDomain_definable hc A).image_real (famCoordIdx m r k π)
  have e : Fin.append (vfs m) (rvs r) ∘ famCoordIdx m r k π = Fin.append (Fin.append (vfs m) (rvs r)) (rvs k) := by
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [famCoordIdx]
  rw [e] at h
  exact h

/-- The index map from the append layout to the layout of `mixedGammaGraph`. -/
def famVolIdx (m r : ℕ) : Fin (m + r) ⊕ Fin 1 → Fin ((m + r) + 1) :=
  Sum.elim (Fin.castAdd 1) (fun _ => Fin.natAdd (m + r) 0)

/-- The raw graph of the volume of the family. -/
def famVol (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) : Set (Fin ((m + r) + 1) → M) :=
  (fun w => w ∘ famVolIdx m r) ⁻¹' mixedGammaGraph A.carrier (gammaFormExtension ω)

include hc in
theorem famVol_definable (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (Fin.append (Fin.append (vfs m) (rvs r)) (rvs 1)) (famVol A ω) := by
  refine real_base hc ((gammaFormExtension_graph_definable ω).preimage_comp (famVolIdx m r)) ?_
  rintro w ⟨hnz, x, -, hx, -⟩ i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · have := mixedTuple_sorted x l
    rw [hx] at this
    simpa [famVolIdx] using this
  · fin_cases l
    rw [Fin.append_right]
    exact hnz.1

/-- **The chart schema of the family of fibres** `a ↦ (A_a, u ↦ u ∘ π, ω(a, ·))`. -/
def famSchema (A : DefSet (rawMixedSpace (M := M) m r) S) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (π : Fin k → Fin r) (N : ℕ) : ChartSchema (⟨S, ∅⟩ : Base (M := M)) (vfs m) k where
  arity := r
  domain := famDomain A
  domain_definable := famDomain_definable hc A
  coord := famCoord A π
  coord_definable := famCoord_definable hc A π
  volume := famVol A ω
  volume_definable := famVol_definable hc A ω
  bound := N

/-! ### Rows of the family -/

section Rows
variable (A : DefSet (rawMixedSpace (M := M) m r) S) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
  (π : Fin k → Fin r) (N : ℕ)

theorem append_eq_mixedTuple_iff (x : Mixed M m r) (a : Fin m → VF M) (u : Fin r → M) :
    mixedTuple x = Fin.append (vfValues a) u ↔ x.1 = a ∧ rvValues x.2 = u := by
  constructor
  · intro he
    refine ⟨vfValues_injective (funext fun i => ?_), funext fun i => ?_⟩
    · simpa [mixedTuple] using congrFun he (Fin.castAdd r i)
    · simpa [mixedTuple] using congrFun he (Fin.natAdd m i)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mem_famDomain_append (a : Fin m → VF M) (u : Fin r → M) :
    Fin.append (vfValues a) u ∈ famDomain A ↔ ∃ t, (a, t) ∈ A.carrier ∧ rvValues t = u := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨h1, h2⟩ := (append_eq_mixedTuple_iff x a u).mp he
    refine ⟨x.2, ?_, h2⟩
    rw [← h1]
    exact hx
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(a, t), ht, rfl⟩

theorem famSchema_mem_row (a : Fin m → VF M) (u : Fin r → M) :
    u ∈ (famSchema hc A ω π N).row (vfValues a) ↔ ∃ t, (a, t) ∈ A.carrier ∧ rvValues t = u :=
  mem_famDomain_append A a u

theorem famSchema_coordRow (a : Fin m → VF M) (u : Fin r → M) (y : Fin k → M) :
    (famSchema hc A ω π N).coordRow (vfValues a) u y ↔
      u ∈ (famSchema hc A ω π N).row (vfValues a) ∧ y = fun i => u (π i) := by
  change Fin.append (Fin.append (vfValues a) u) y ∈ famCoord A π ↔ Fin.append (vfValues a) u ∈ famDomain A ∧ _
  constructor
  · rintro ⟨x, hx, he⟩
    have h1 : x = Fin.append (vfValues a) u := by
      funext i
      have := congrFun he (Fin.castAdd k i)
      simpa [famCoordIdx] using this
    subst h1
    refine ⟨hx, funext fun i => ?_⟩
    have := congrFun he (Fin.natAdd (m + r) i)
    simp [famCoordIdx] at this
    exact this.symm
  · rintro ⟨hx, rfl⟩
    refine ⟨_, hx, funext fun i => ?_⟩
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [famCoordIdx]

theorem famSchema_volRow (a : Fin m → VF M) (t : Fin r → RVInfinity M) (ht : (a, t) ∈ A.carrier) (c : M) :
    (famSchema hc A ω π N).volRow (vfValues a) (rvValues t) c ↔
      NonzeroRV c ∧ codeValue c = (ω ⟨(a, t), ht⟩).val := by
  change Fin.append (Fin.append (vfValues a) (rvValues t)) (fun _ : Fin 1 => c) ∘ famVolIdx m r ∈
    mixedGammaGraph A.carrier (gammaFormExtension ω) ↔ _
  have h0 : (Fin.append (Fin.append (vfValues a) (rvValues t)) (fun _ : Fin 1 => c) ∘ famVolIdx m r) (.inr 0) = c := by
    simp [famVolIdx]
  have h1 : (Fin.append (Fin.append (vfValues a) (rvValues t)) (fun _ : Fin 1 => c) ∘ famVolIdx m r) ∘ Sum.inl =
      Fin.append (vfValues a) (rvValues t) := by
    funext i; simp [famVolIdx]
  unfold mixedGammaGraph
  simp only [Set.mem_setOf_eq, h0, h1]
  constructor
  · rintro ⟨hc0, x, hx, he, hv⟩
    obtain ⟨rfl, h2⟩ := (append_eq_mixedTuple_iff x a _).mp he
    have hx2 : x.2 = t := rvValues_injective h2
    have hxe : x = (x.1, t) := Prod.ext rfl hx2
    refine ⟨hc0, ?_⟩
    rw [hv]
    exact (congrArg (gammaFormExtension ω) hxe).trans (gammaFormExtension_at ω ⟨(x.1, t), ht⟩)
  · rintro ⟨hc0, hv⟩
    refine ⟨hc0, (a, t), ht, rfl, ?_⟩
    rw [hv, gammaFormExtension_at ω ⟨(a, t), ht⟩]

end Rows

end DiamondIntegral.Section7.Lemma714Schema
