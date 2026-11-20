import «section 7».Lemma714Chains
import «section 7».BaseExtension

/-! Lemma 7.14, part 6: promotion of pointwise data to schemata.

Let `z : Fin p → M` be a parameter tuple of sorts `sp`, and let `C` be a base
whose definable sets are definable over `B ∪ z` (`Promotable`). This holds for
`C = S⟨a⟩` and `z = a`, since the generated substructure lies in the
definable closure.

* `promoteSet`: a set definable over `C` is the row at `z` of a `B`-definable
  set (`gamma_tuple_parameter_promotion` of integration-in-ACVF).
* `promoteChart c N`: a chart `c` over `C` with fibre bound `N` gives a chart
  schema over `B` whose row at `z` is `c`. It is valid at `z`, and its chart at
  `z` is identified with `c` by the identity map (`promoteChart_iso`).
* `exists_coord_bound`: by saturation over the small base `B ∪ z`, the finite
  fibres of the structural map of `c` have a uniform bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

/-- Every set definable over `C` is definable over `B ∪ z`. -/
def Promotable (B C : Base (M := M)) (z : Fin p → M) : Prop :=
  ∀ {n : ℕ} (sn : Fin n → SortTag) (S : Set (Fin n → M)), DefinableOverBase C sn S →
    DefinableOverBase (baseAt B z) sn S

omit hM in
theorem split_append {n : ℕ} (z : Fin p → M) (x : Fin n → M) :
    ((fun i => Fin.append z x (Fin.castAdd n i)), fun j => Fin.append z x (Fin.natAdd p j)) = (z, x) := by
  simp

section PromoteSet
variable {C : Base (M := M)} {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)
include hz hC

/-- A set definable over `C` is the row at `z` of a `B`-definable set. -/
theorem promoteSet {n : ℕ} (sx : Fin n → SortTag) (S : Set (Fin n → M)) (hS : DefinableOverBase C sx S) :
    ∃ P : Set (Fin (p + n) → M), DefinableOverBase B (Fin.append sp sx) P ∧ ∀ x, Fin.append z x ∈ P ↔ x ∈ S := by
  obtain ⟨Q, hQ, hQS⟩ := gamma_tuple_parameter_promotion B sp sx z hz S (hC sx S hS)
  refine ⟨_, hQ, fun x => ?_⟩
  change ((fun i => Fin.append z x (Fin.castAdd n i)), fun j => Fin.append z x (Fin.natAdd p j)) ∈ Q ↔ x ∈ S
  rw [split_append, ← hQS]
  rfl

/-- The same, in two blocks. -/
theorem promoteSet2 {n m : ℕ} (sx : Fin n → SortTag) (sy : Fin m → SortTag) (S : Set (Fin (n + m) → M))
    (hS : DefinableOverBase C (Fin.append sx sy) S) :
    ∃ P : Set (Fin ((p + n) + m) → M), DefinableOverBase B (Fin.append (Fin.append sp sx) sy) P ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ P ↔ Fin.append x y ∈ S := by
  obtain ⟨P, hP, hPS⟩ := promoteSet hz hC (Fin.append sx sy) S hS
  refine ⟨{w | w ∘ Fin.cast (Nat.add_assoc p n m).symm ∈ P ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sp sx) sy)}, hP.preimage_real _ _, fun x y => ?_⟩
  have e : Fin.append (Fin.append z x) y ∘ Fin.cast (Nat.add_assoc p n m).symm = Fin.append z (Fin.append x y) := by
    funext i
    exact append_assoc_apply z x y i
  simp only [Set.mem_setOf_eq, e]
  constructor
  · exact fun h => (hPS _).mp h.1
  · intro h
    refine ⟨(hPS _).mpr h, ?_⟩
    have hs := hS.proper _ h
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) l
      · simpa using hz r
      · simpa using hs (Fin.castAdd m r)
    · simpa using hs (Fin.natAdd n l)

end PromoteSet

/-! ### Promoting a chart -/

section PromoteChart
variable {C : Base (M := M)} {d : ℕ}

/-- The graph of the structural map, in the append layout `(u, y)`. -/
def coordSet (c : Chart C d) : Set (Fin (c.arity + d) → M) :=
  {w | (fun i => w (Fin.castAdd d i)) ∈ c.domain ∧ c.coordinate (fun i => w (Fin.castAdd d i)) =
    fun j => w (Fin.natAdd c.arity j)}

/-- The index map from the graph layout `(y, u)` of Section 4 to the append layout. -/
def graphIndexInv (a d : ℕ) : Fin (d + a) → Fin (a + d) := join d a (Fin.castAdd d) (Fin.natAdd a)

theorem coordSet_definable (c : Chart C d) :
    DefinableOverBase C (Fin.append (rvs c.arity) (rvs d)) (coordSet c) := by
  have h := c.coordinate_definable.preimage_real (Fin.append (rvs c.arity) (rvs d)) (graphIndexInv c.arity d)
  convert h using 1
  ext w
  simp only [coordSet, Set.mem_setOf_eq, graphOn, graphIndexInv, comp_join, join_comp_head, join_comp_tail]
  constructor
  · rintro ⟨hu, he⟩
    refine ⟨⟨hu, he⟩, ?_⟩
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · have := c.domain_definable.proper _ hu l
      simpa using this
    · have := (c.coordinate_proper _ hu l).1
      rw [he] at this
      rw [Fin.append_right]
      exact this
  · rintro ⟨⟨hu, he⟩, -⟩
    exact ⟨hu, he⟩

/-- The volume relation, in the append layout `(u, c)`. -/
def volSet (c : Chart C d) : Set (Fin (c.arity + 1) → M) :=
  {w | (fun i => w (Fin.castAdd 1 i)) ∈ c.domain ∧ NonzeroRV (w (Fin.natAdd c.arity 0)) ∧
    codeValue (w (Fin.natAdd c.arity 0)) = c.volume (fun i => w (Fin.castAdd 1 i))}

theorem volSet_definable (c : Chart C d) :
    DefinableOverBase C (Fin.append (rvs c.arity) (rvs 1)) (volSet c) := by
  have h := c.volume_definable.preimage_real (Fin.append (rvs c.arity) (rvs 1))
    (Fin.cons (Fin.natAdd c.arity 0) (Fin.castAdd 1))
  convert h using 1
  ext w
  simp only [volSet, Set.mem_setOf_eq]
  have ht : Fin.tail (w ∘ Fin.cons (Fin.natAdd c.arity 0) (Fin.castAdd 1)) = fun i => w (Fin.castAdd 1 i) := by
    funext i; simp [Fin.tail]
  have h0 : (w ∘ Fin.cons (Fin.natAdd c.arity 0) (Fin.castAdd 1)) 0 = w (Fin.natAdd c.arity 0) := by simp
  rw [ht, h0]
  constructor
  · rintro ⟨hu, hn, he⟩
    refine ⟨⟨hu, hn, he⟩, ?_⟩
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · have := c.domain_definable.proper _ hu l
      simpa using this
    · fin_cases l
      rw [Fin.append_right]
      exact hn.1
  · rintro ⟨h, -⟩
    exact h

variable {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)

/-- **Promotion of a chart** over `C` to a chart schema over `B` with row `c` at `z`. -/
def promoteChart (c : Chart C d) (N : ℕ) : ChartSchema B sp d where
  arity := c.arity
  domain := (promoteSet hz hC (rvs c.arity) c.domain c.domain_definable).choose
  domain_definable := (promoteSet hz hC (rvs c.arity) c.domain c.domain_definable).choose_spec.1
  coord := (promoteSet2 hz hC (rvs c.arity) (rvs d) (coordSet c) (coordSet_definable c)).choose
  coord_definable := (promoteSet2 hz hC (rvs c.arity) (rvs d) (coordSet c) (coordSet_definable c)).choose_spec.1
  volume := (promoteSet2 hz hC (rvs c.arity) (rvs 1) (volSet c) (volSet_definable c)).choose
  volume_definable := (promoteSet2 hz hC (rvs c.arity) (rvs 1) (volSet c) (volSet_definable c)).choose_spec.1
  bound := N

variable (c : Chart C d) (N : ℕ)

theorem promoteChart_row : (promoteChart hz hC c N).row z = c.domain :=
  Set.ext (fun u => (promoteSet hz hC (rvs c.arity) c.domain c.domain_definable).choose_spec.2 u)

theorem promoteChart_coordRow (u : Fin c.arity → M) (y : Fin d → M) :
    (promoteChart hz hC c N).coordRow z u y ↔ u ∈ c.domain ∧ c.coordinate u = y := by
  have h := (promoteSet2 hz hC (rvs c.arity) (rvs d) (coordSet c) (coordSet_definable c)).choose_spec.2 u y
  change _ ∈ (promoteSet2 hz hC (rvs c.arity) (rvs d) (coordSet c) (coordSet_definable c)).choose ↔ _
  rw [h]
  simp only [coordSet, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]

theorem promoteChart_volRow (u : Fin c.arity → M) (c' : M) :
    (promoteChart hz hC c N).volRow z u c' ↔ u ∈ c.domain ∧ NonzeroRV c' ∧ codeValue c' = c.volume u := by
  have h := (promoteSet2 hz hC (rvs c.arity) (rvs 1) (volSet c) (volSet_definable c)).choose_spec.2 u
    (fun _ => c')
  change _ ∈ (promoteSet2 hz hC (rvs c.arity) (rvs 1) (volSet c) (volSet_definable c)).choose ↔ _
  rw [h]
  simp only [volSet, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]

/-- The promoted chart schema is valid at `z`, given a fibre bound and a domain bound. -/
theorem promoteChart_valid (hN : ∀ t, {u | u ∈ c.domain ∧ c.coordinate u = t}.ncard ≤ N)
    (hb : RVMeasuredBounds.DomainBounded c) : (promoteChart hz hC c N).Valid z := by
  refine ⟨⟨hz, fun u hu => ?_, fun u y hy => ?_, fun y _ => ?_⟩, fun u y hy => ?_, fun u hu => ?_,
    fun u c' hc' => ?_, fun u c₁ c₂ h₁ _ h₂ => ?_, ?_⟩
  · have hu' : u ∈ c.domain := by rw [← promoteChart_row hz hC c N]; exact hu
    exact ⟨c.coordinate u, (promoteChart_coordRow hz hC c N u _).mpr ⟨hu', rfl⟩,
      fun y hy => ((promoteChart_coordRow hz hC c N u y).mp hy).2.symm⟩
  · have := ((promoteChart_coordRow hz hC c N u y).mp hy).1
    rw [← promoteChart_row hz hC c N] at this
    exact this
  · have hsub : {x : Fin c.arity → M | Fin.append (Fin.append z x) y ∈ (promoteChart hz hC c N).coord} ⊆
        {u | u ∈ c.domain ∧ c.coordinate u = y} := fun x hx => (promoteChart_coordRow hz hC c N x y).mp hx
    exact ⟨(c.finite_fibres y).subset hsub, (Set.ncard_le_ncard hsub (c.finite_fibres y)).trans (hN y)⟩
  · obtain ⟨hu, rfl⟩ := (promoteChart_coordRow hz hC c N u y).mp hy
    exact c.coordinate_proper u hu
  · have hu' : u ∈ c.domain := by rw [← promoteChart_row hz hC c N]; exact hu
    refine ⟨GammaParameters.raw (GammaParameters.representative (c.volume u)), ?_⟩
    exact (promoteChart_volRow hz hC c N u _).mpr ⟨hu', ChartSchema.nonzero_raw _,
      ChartSchema.codeValue_raw_representative _⟩
  · obtain ⟨hu, hn, -⟩ := (promoteChart_volRow hz hC c N u c').mp hc'
    rw [promoteChart_row hz hC c N]
    exact ⟨hu, hn⟩
  · obtain ⟨hu, -, he⟩ := (promoteChart_volRow hz hC c N u c₁).mp h₁
    rw [promoteChart_volRow hz hC c N, he]
    exact ⟨fun h => h.2.2, fun h => ⟨hu, h₂, h⟩⟩
  · obtain ⟨β, hβ⟩ := hb
    refine ⟨β⁻¹, β, fun u hu i hi => ?_⟩
    rw [promoteChart_row hz hC c N] at hu
    exact hβ u hu i hi

end PromoteChart

/-! ### Corrected weights of rows -/

namespace ChartSchema
variable {d : ℕ} (W : ChartSchema B sp d)

/-- The corrected weight of the row at `z`. -/
def weightAt (z : Fin p → M) (u : Fin W.arity → M) : Values.Gamma (M := M) :=
  W.volAt z u * ∏ i, codeValue (W.coordAt z u i)

end ChartSchema

/-! ### Isomorphism schemata from row bijections -/

section PromoteIso
variable {C : Base (M := M)} {d : ℕ} {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)
include hz hC

/-- A bijection of valid rows with a `C`-definable graph that preserves the
corrected weights is the row at `z` of a valid isomorphism schema. -/
theorem exists_isoSchema {X Y : ChartSchema B sp d} (hX : X.Valid z) (hY : Y.Valid z)
    (F : (Fin X.arity → M) → (Fin Y.arity → M))
    (hF : DefinableOverBase C (Fin.append (rvs X.arity) (rvs Y.arity))
      {w | (fun i => w (Fin.castAdd Y.arity i)) ∈ X.row z ∧
        F (fun i => w (Fin.castAdd Y.arity i)) = fun j => w (Fin.natAdd X.arity j)})
    (hbij : Set.BijOn F (X.row z) (Y.row z))
    (hw : ∀ u ∈ X.row z, X.weightAt z u = Y.weightAt z (F u)) :
    ∃ Φ : IsoSchema X Y, Φ.Valid z := by
  obtain ⟨P, hP, hPS⟩ := promoteSet2 hz hC (rvs X.arity) (rvs Y.arity) _ hF
  have hrow : ∀ u v, Fin.append (Fin.append z u) v ∈ P ↔ u ∈ X.row z ∧ F u = v := by
    intro u v
    rw [hPS]
    simp only [Set.mem_setOf_eq, Fin.append_left, Fin.append_right]
  refine ⟨⟨P, hP⟩, ⟨⟨⟨hz, fun u hu => ?_, fun u v h => ((hrow u v).mp h).1, fun v hv => ?_⟩, fun v => ?_⟩, ?_⟩⟩
  · exact ⟨F u, (hrow u _).mpr ⟨hu, rfl⟩, fun v h => ((hrow u v).mp h).2.symm⟩
  · have hsub : {x : Fin X.arity → M | Fin.append (Fin.append z x) v ∈ P} ⊆ {x | x ∈ X.row z ∧ F x = v} :=
      fun x hx => (hrow x v).mp hx
    have hss : {x | x ∈ X.row z ∧ F x = v}.Subsingleton := by
      rintro x ⟨hx, rfl⟩ x' ⟨hx', he⟩
      exact hbij.injOn hx hx' he.symm
    exact ⟨hss.finite.subset hsub, (Set.ncard_le_ncard hsub hss.finite).trans ((Set.ncard_le_one hss.finite).mpr (fun a ha b hb => hss ha hb))⟩
  · constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv
      exact ⟨u, (hrow u _).mpr ⟨hu, rfl⟩⟩
    · rintro ⟨u, h⟩
      obtain ⟨hu, rfl⟩ := (hrow u v).mp h
      exact hbij.mapsTo hu
  · intro u v y y' c c' h1 h2 h3 h4 h5 _ _ _ _
    obtain ⟨hu, rfl⟩ := (hrow u v).mp h1
    have hv := hbij.mapsTo hu
    obtain ⟨-, rfl⟩ := (ChartSchema.coordRow_iff hX u y).mp h2
    obtain ⟨-, rfl⟩ := (ChartSchema.coordRow_iff hY (F u) y').mp h3
    obtain ⟨-, -, hc⟩ := (ChartSchema.volRow_iff hX u c).mp h4
    obtain ⟨-, -, hc'⟩ := (ChartSchema.volRow_iff hY (F u) c').mp h5
    rw [hc, hc']
    exact hw u hu

end PromoteIso

end DiamondIntegral.Section7.Lemma714Schema
