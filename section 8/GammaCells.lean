import «section 8».LinearTransfer
import «section 4».GammaCellFormula
import «section 4».GammaMapOrder
import «section 4».GammaQuantifierLogic
import Mathlib.GroupTheory.DivisibleHull

/-! The value group as an ordered `ℚ`-vector space, and cylindrical cells.

The value group `Γ` of the formalization is a multiplicative linearly ordered group with `n`-th
roots. It embeds in the divisible hull `Hull Γ` of `Additive Γ`, an ordered `ℚ`-vector space, by an
injective order-preserving homomorphism `ι` (`ι_mul`, `ι_lt_iff`); `qpow γ q = root (γ ^ num q) (den q)`
is the rational power, with `ι (qpow γ q) = q • ι γ`.

Fix `π > 1` in `Γ`, the value of the uniformizer. A rational affine function `g` on `ℚⁿ` gives the
map `gfun π g : Γⁿ → Γ`, `y ↦ ∏ᵢ qpow (y (rev i)) (coeff i) · qpow π const`; the coordinates are
reversed because the cells of the library add the new coordinate in front (`Fin.cons`), while the
triangulation of `LinearTransfer` adds it at the end (`Fin.snoc`). A set `S ⊆ (Hull Γ)ⁿ` is realized
in `Γⁿ` as `real S = {z | (ι (z (rev i)))ᵢ ∈ S}`.

* `cell_real`: the realization of a `VCell` is a cell of the library of the same dimension,
  definable over any base over which `π` is definable.
* `euler_real`: if `S` is a union of sign classes of finitely many affine functions and its
  rational points are bounded, then the geometric Euler characteristic of `real S` is
  `Triangulation.eulerChar` of a triangulation of those rational points. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.GammaCells

open Prism

/-! ### The divisible hull -/

section hull

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ] [RootableBy Γ ℕ]

/-- The divisible hull of the value group, an ordered `ℚ`-vector space. -/
abbrev Hull (Γ : Type*) [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ] :=
  DivisibleHull (Additive Γ)

/-- The embedding of `Γ` in its divisible hull. -/
def ι (γ : Γ) : Hull Γ := ((Additive.ofMul γ : Additive Γ) : DivisibleHull (Additive Γ))

omit [RootableBy Γ ℕ] in
theorem ι_mul (γ δ : Γ) : ι (γ * δ) = ι γ + ι δ := by
  simp only [ι, ofMul_mul]
  exact DivisibleHull.coe_add

omit [RootableBy Γ ℕ] in
theorem ι_one : ι (1 : Γ) = 0 := by
  simp [ι]

omit [RootableBy Γ ℕ] in
theorem ι_prod {α : Type*} (s : Finset α) (f : α → Γ) : ι (∏ a ∈ s, f a) = ∑ a ∈ s, ι (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ι_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ι_mul, ih]

omit [RootableBy Γ ℕ] in
theorem ι_npow (γ : Γ) (k : ℕ) : ι (γ ^ k) = k • ι γ := by
  induction k with
  | zero => simp [ι_one]
  | succ k ih => rw [pow_succ, ι_mul, ih, succ_nsmul]

omit [RootableBy Γ ℕ] in
theorem ι_inv (γ : Γ) : ι γ⁻¹ = -ι γ := by
  have h : ι γ⁻¹ + ι γ = 0 := by rw [← ι_mul, inv_mul_cancel, ι_one]
  exact eq_neg_of_add_eq_zero_left h

omit [RootableBy Γ ℕ] in
theorem ι_zpow (γ : Γ) (k : ℤ) : ι (γ ^ k) = k • ι γ := by
  cases k with
  | ofNat k => simp [ι_npow]
  | negSucc k => rw [zpow_negSucc, ι_inv, ι_npow, negSucc_zsmul]

omit [RootableBy Γ ℕ] in
theorem ι_injective : Function.Injective (ι : Γ → Hull Γ) := fun _ _ h =>
  Additive.ofMul.injective (DivisibleHull.coe_injective h)

omit [RootableBy Γ ℕ] in
theorem ι_lt_iff {γ δ : Γ} : ι γ < ι δ ↔ γ < δ := by
  change DivisibleHull.mk (Additive.ofMul γ) 1 < DivisibleHull.mk (Additive.ofMul δ) 1 ↔ _
  rw [DivisibleHull.mk_lt_mk]
  simp only [PNat.val_ofNat, one_smul]
  exact Additive.ofMul_lt

omit [RootableBy Γ ℕ] in
theorem ι_strictMono : StrictMono (ι : Γ → Hull Γ) := fun _ _ h => ι_lt_iff.mpr h

omit [RootableBy Γ ℕ] in
theorem ι_le_iff {γ δ : Γ} : ι γ ≤ ι δ ↔ γ ≤ δ := ι_strictMono.le_iff_le

omit [RootableBy Γ ℕ] in
theorem ι_inj {γ δ : Γ} : ι γ = ι δ ↔ γ = δ := ι_injective.eq_iff

/-- The rational power `γ ^ q`. -/
def qpow (γ : Γ) (q : ℚ) : Γ := RootableBy.root (γ ^ q.num) q.den

omit [LinearOrder Γ] [IsOrderedMonoid Γ] in
theorem qpow_pow_den (γ : Γ) (q : ℚ) : qpow γ q ^ q.den = γ ^ q.num :=
  RootableBy.root_cancel _ q.den_ne_zero

theorem ι_qpow (γ : Γ) (q : ℚ) : ι (qpow γ q) = q • ι γ := by
  change DivisibleHull.mk (Additive.ofMul (qpow γ q)) 1 =
    q • DivisibleHull.mk (Additive.ofMul γ) 1
  rw [DivisibleHull.qsmul_mk, DivisibleHull.mk_eq_mk_iff_smul_eq_smul]
  change (q.den * 1) • Additive.ofMul (qpow γ q) = 1 • (q.num • Additive.ofMul γ)
  rw [mul_one, one_smul, ← ofMul_pow, ← ofMul_zpow, qpow_pow_den]

theorem qpow_intCast (γ : Γ) (k : ℤ) : qpow γ (k : ℚ) = γ ^ k := by
  have h := qpow_pow_den γ (k : ℚ)
  simpa only [Rat.den_intCast, Rat.num_intCast, pow_one] using h

theorem ι_zpow_rat (γ : Γ) (k : ℤ) : ι (γ ^ k) = (k : ℚ) • ι γ := by
  rw [← qpow_intCast, ι_qpow]

omit [RootableBy Γ ℕ] in
theorem pos_ι_of_one_lt {π : Γ} (hπ : 1 < π) : 0 < ι π := by
  rw [← ι_one]; exact ι_lt_iff.mpr hπ

/-- The map `Γⁿ → Γ` of a rational affine function, coordinates reversed. -/
def gfun (π : Γ) {n : ℕ} (g : AffFun n) (y : Fin n → Γ) : Γ :=
  (∏ i, qpow (y (Fin.rev i)) (g.coeff i)) * qpow π g.const

theorem ι_gfun (π : Γ) {n : ℕ} (g : AffFun n) (y : Fin n → Γ) :
    ι (gfun π g y) = g.evalV (ι π) (fun i => ι (y (Fin.rev i))) := by
  simp only [gfun, ι_mul, ι_prod, ι_qpow, AffFun.evalV]

/-- The realization in `Γⁿ` of a set in `(Hull Γ)ⁿ`, coordinates reversed. -/
def real {n : ℕ} (S : Set (Fin n → Hull Γ)) : Set (Fin n → Γ) :=
  {z | (fun i => ι (z (Fin.rev i))) ∈ S}

omit [RootableBy Γ ℕ] in
theorem real_univ (n : ℕ) : real (Set.univ : Set (Fin n → Hull Γ)) = Set.univ := rfl

omit [RootableBy Γ ℕ] in
theorem real_iUnion {n : ℕ} {κ : Type*} (S : κ → Set (Fin n → Hull Γ)) :
    real (⋃ k, S k) = ⋃ k, real (S k) := by
  ext z; simp [real]

omit [RootableBy Γ ℕ] in
theorem real_disjoint {n : ℕ} {S S' : Set (Fin n → Hull Γ)} (h : Disjoint S S') :
    Disjoint (real S) (real S') :=
  Set.disjoint_left.mpr fun _ hz hz' => Set.disjoint_left.mp h hz hz'

omit [RootableBy Γ ℕ] in
theorem tail_rev {n : ℕ} (z : Fin (n + 1) → Γ) :
    (fun i : Fin n => (fun j => ι (z (Fin.rev j))) (Fin.castSucc i)) =
      fun i => ι (Fin.tail z (Fin.rev i)) := by
  funext i
  simp [Fin.rev_castSucc, Fin.tail]

omit [RootableBy Γ ℕ] in
theorem last_rev {n : ℕ} (z : Fin (n + 1) → Γ) :
    (fun j => ι (z (Fin.rev j))) (Fin.last n) = ι (z 0) := by
  simp [Fin.rev_last]

end hull

/-! ### Cells of the value group -/

section cells

open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic GammaDefinableMaps GammaCellSections
  GammaCylindricalCells GammaMapOrder

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "Γ" => Values.Gamma (M := M)

theorem one_map_definable (B : Base (M := M)) {n : ℕ} {π : Γ}
    (hπ : GammaDefinableClosureAtBase B π) : MapDefinable B (fun _ : Fin n → Γ => (1 : Γ)) := by
  have h := int_power_definable B _ (constant_definable B π hπ (n := n)) 0
  simpa only [zpow_zero] using h

theorem prod_map_definable (B : Base (M := M)) {n : ℕ} {π : Γ}
    (hπ : GammaDefinableClosureAtBase B π) {α : Type*} (s : Finset α)
    (f : α → (Fin n → Γ) → Γ) (hf : ∀ a ∈ s, MapDefinable B (f a)) :
    MapDefinable B (fun y => ∏ a ∈ s, f a y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using one_map_definable B hπ
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact mul_definable B _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem qpow_map_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Γ) → Γ) (hf : MapDefinable B f) (q : ℚ) :
    MapDefinable B (fun y => qpow (f y) q) :=
  root_definable B _ (int_power_definable B f hf q.num) q.den q.den_ne_zero

theorem gfun_definable (B : Base (M := M)) {n : ℕ} {π : Γ}
    (hπ : GammaDefinableClosureAtBase B π) (g : AffFun n) : MapDefinable B (gfun π g) :=
  mul_definable B _ _
    (prod_map_definable B hπ Finset.univ _ fun i _ =>
      qpow_map_definable B _ (projection_definable B (Fin.rev i)) (g.coeff i))
    (qpow_map_definable B _ (constant_definable B π hπ) g.const)

theorem graphCell_definable (B : Base (M := M)) {n : ℕ} {C : Set (Fin n → Γ)}
    (hC : GammaDefinable B C) {T : (Fin n → Γ) → Γ} (hT : MapDefinable B T) :
    GammaDefinable B (graphCell C T) := by
  have h1 := GammaRelationLogic.preimage_definable_base B C hC Fin.succ
  have h2 := equal_maps_definable B _ _ (projection_definable B (0 : Fin (n + 1)))
    (reindex_definable B T hT Fin.succ)
  exact GammaRelationLogic.inter_definable_base B _ _ h1 h2

theorem bandCell_definable (B : Base (M := M)) {n : ℕ} {C : Set (Fin n → Γ)}
    (hC : GammaDefinable B C) {l u : (Fin n → Γ) → Γ} (hl : MapDefinable B l)
    (hu : MapDefinable B u) : GammaDefinable B (bandCell C l u) := by
  have h1 := GammaRelationLogic.preimage_definable_base B C hC Fin.succ
  have h2 := lt_maps_definable B _ _ (reindex_definable B l hl Fin.succ)
    (projection_definable B (0 : Fin (n + 1)))
  have h3 := lt_maps_definable B _ _ (projection_definable B (0 : Fin (n + 1)))
    (reindex_definable B u hu Fin.succ)
  exact GammaRelationLogic.inter_definable_base B _ _ h1
    (GammaRelationLogic.inter_definable_base B _ _ h2 h3)

/-- **Realized cells.** The realization of a `VCell` is a cell of the library of the same
dimension. -/
theorem cell_real (B : Base (M := M)) {π : Γ} (hπ : GammaDefinableClosureAtBase B π)
    {n d : ℕ} {S : Set (Fin n → Hull Γ)} (hS : VCell (ι π) n d S) : Cell B n (real S) d := by
  induction hS with
  | point => exact Cell.base
  | @graph n d C _ φ ih =>
    have he : real {z : Fin (n + 1) → Hull Γ | (fun i => z (Fin.castSucc i)) ∈ C ∧
        z (Fin.last n) = φ.evalV (ι π) (fun i => z (Fin.castSucc i))} =
        graphCell (real C) (gfun π φ) := by
      ext z
      show (fun i => (fun j => ι (z (Fin.rev j))) (Fin.castSucc i)) ∈ C ∧ _ ↔ _
      rw [tail_rev, last_rev, ← ι_gfun, ι_inj]
      rfl
    rw [he]
    exact Cell.graph ih _ (graphCell_definable B ih.definable (gfun_definable B hπ φ))
  | @band n d C _ φ ψ hlt ih =>
    have he : real {z : Fin (n + 1) → Hull Γ | (fun i => z (Fin.castSucc i)) ∈ C ∧
        φ.evalV (ι π) (fun i => z (Fin.castSucc i)) < z (Fin.last n) ∧
        z (Fin.last n) < ψ.evalV (ι π) (fun i => z (Fin.castSucc i))} =
        bandCell (real C) (gfun π φ) (gfun π ψ) := by
      ext z
      show (fun i => (fun j => ι (z (Fin.rev j))) (Fin.castSucc i)) ∈ C ∧ _ ↔ _
      rw [tail_rev, last_rev, ← ι_gfun, ← ι_gfun, ι_lt_iff, ι_lt_iff]
      rfl
    rw [he]
    refine Cell.band ih _ _ (fun y hy => ?_)
      (bandCell_definable B ih.definable (gfun_definable B hπ φ) (gfun_definable B hπ ψ))
    rw [← ι_lt_iff, ι_gfun, ι_gfun]
    exact hlt _ hy

/-- **Euler characteristic of a realization.** If `S` is a union of sign classes of finitely many
affine functions, its rational points lie in a box, and `real S` is definable, then the geometric
Euler characteristic of `real S` is `Triangulation.eulerChar` of a triangulation of the rational
points of `S`. -/
theorem euler_real (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M)) (hr : Cardinal.mk B.real < κ)
    (hγ : Cardinal.mk B.gamma < κ) {π : Γ} (hπ1 : 1 < π) (hπ : GammaDefinableClosureAtBase B π)
    {n : ℕ} (G : List (AffFun n)) (S : Set (Fin n → Hull Γ)) (hS : SaturatedV (ι π) G S)
    {N : ℚ} (hN : 0 ≤ N) (hbox : ∀ x : Fin n → ℚ, (fun i => x i • ι π) ∈ S → x ∈ box n N)
    (hX : GammaDefinable B (real S)) :
    Constructible G {x | (fun i => x i • ι π) ∈ S} ∧
      ∃ T : Triangulation n {x | (fun i => x i • ι π) ∈ S},
        GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
          (GammaIndicators.indicatorFamily B (real S) hX) = T.eulerChar := by
  have he := pos_ι_of_one_lt hπ1
  obtain ⟨hD, hreal⟩ := realV_of_saturated he hS
  refine ⟨hD, ?_⟩
  obtain ⟨T, C, hcell, hdisj, hcover⟩ :=
    exists_vcell_partition he G hN {x | (fun i => x i • ι π) ∈ S} hbox hD
  refine ⟨T, ?_⟩
  have h := GammaCellFormula.geometric_partition_formula (ι := T.κ) h00 hκ hs B hr hγ n (real S) hX
    (fun k => real (C k)) T.dim (fun k => cell_real B hπ (hcell k))
    (fun k k' hkk' => real_disjoint (hdisj k k' hkk'))
    (by rw [← real_iUnion, hcover, hreal])
  rw [h]
  rfl

end cells

end DiamondIntegral.Section8.GammaCells
