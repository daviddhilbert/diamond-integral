import «section 7».StageSlices

/-! Two-dimensional slices of sets, maps and standard contraction stages (for
Lemma 7.23 with `n > 2`).

This is the analogue of `FibreRestriction` and `StageSlices` with two free
coordinates instead of one. Points of `VF^{m+2}` over `b ∈ VFᵐ` are written in the
snoc convention of `FibreRestriction`: `(b, y) = Fin.snoc (Fin.snoc b y₀) y₁` for
`y ∈ VF²`; `snoc2_eq_append` identifies this with `Fin.append b y`. The last two
coordinates of `w ∈ VF^{m+2}` are `fun i => w (Fin.natAdd m i)`.

* For a definable mixed set `X ⊆ VF^{m+2} × RVʳ` over `S` and `b ∈ VFᵐ`, the slice
  `X_b = {(y, t) ∈ VF² × RVʳ | ((b, y), t) ∈ X}` is definable over every base `S'`
  containing `S` and the coordinates of `b` (`slice2`, `mem_slice2`). It is proper
  invariant, VF-(doubly) bounded and RV bounded when `X` is, with the radii of the last
  two coordinates, and has finite RV fibres when `X` does.
* A definable map `f : X → X'` fixing the first `m` VF coordinates restricts to
  `f_b : X_b → X'_b` (`sliceMap2`). Bijectivity and the proper covariant homeomorphism
  property pass to `f_b`; the inverse of `f_b` is the restriction of the inverse of `f`.
* A chart of `f` at a point of the slice agrees with the coordinate projections in the
  first `m` coordinates, so the first `m` rows of the derivative `L` are unit rows. After
  reindexing by `Fin m ⊕ Fin 2` the matrix of `L` is block lower triangular with the
  identity in the upper left corner (`det_eq_det_submatrix_natAdd`), so `det L` is the
  determinant of the lower right `2 × 2` block, the derivative of `f_b`
  (`sliceMap2_derivative`). Unit derivatives restrict (`sliceMap2_unitDerivative`).
* Good points (`exists_good_polynomial2`): a set `Bad` of VF dimension `< m + 2` lies in
  the zero set of a nonzero polynomial `Q`. View `Q` as a polynomial in the last two
  variables with coefficients in `K[X₁, …, Xₘ]` (`MvPolynomial.sumAlgEquiv`) and let `P`
  be a nonzero coefficient. If `P(b) ≠ 0`, then `Q(b, ·, ·)` is a nonzero polynomial over
  the VF parameter field of `S'` vanishing on `Bad_b`, so no point of `Bad_b` is
  algebraically independent over that field and `Bad_b` has VF dimension `< 2`. This
  needs no enlargement of the base by a coordinate of the point.
* A standard contraction stage `H` of `Y ⊆ VF^{m+2} × RVʳ` changes only the last VF
  coordinate and fixes the first `m + 1`. At a point `b` whose exceptional slice has VF
  dimension `< 2` or is empty (the hypothesis of `stageSlice2`; good points provide it),
  the restriction is a standard contraction stage of `Y_b` over `S'` (`stageSlice2`): the
  target is the slice of the target, with the same arity, old labels and leading label;
  it fixes coordinate `0` of the slice; the bundle field comes from `H.bundle`
  (`slice2_target_bundle`); the exceptional set is the slice of `H.exceptional`. The
  contracted set of the restricted stage is the one-dimensional slice of the contracted
  set of `H` (`stageSlice2_contracted`), and the contraction is the restriction of the
  contraction of `H` (`stageSlice2_contraction_val`, `stageSlice2_contraction_lift`).
  So the second stage of a standard contraction restricts by `StageSlices`.
* The slice of an object of `μVF^◇[m + 2]` with the form `ω((b, ·), ·)` is an object of
  `μVF^◇[2]` over `S'` (`slice2Object`, `slice2VFObject`).

Every field of the stage restricts as stated. The `exceptional_dim` field of a stage
is a strict bound `< 2`; the "or empty" alternative of the hypothesis is converted by
`vfDim_lt_of_carrier_empty`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.TwoDimSlices
open DiamondIntegral.Section6 DiamondIntegral.Section2
open SpecialTransformations.Section9 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.FibreRestriction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S S' : Set M} {m r s : ℕ}

/-! ### Coordinates of `(b, y) ∈ VF^{m+2}` -/

section Coordinates

omit [M ⊨ Axioms.ACVF] in
theorem natAdd_two_zero : Fin.natAdd m (0 : Fin 2) = (Fin.last m).castSucc :=
  Fin.ext (by simp)

omit [M ⊨ Axioms.ACVF] in
theorem natAdd_two_one : Fin.natAdd m (1 : Fin 2) = Fin.last (m + 1) :=
  Fin.ext (by simp)

omit [M ⊨ Axioms.ACVF] in
theorem fin_two_ext {x y : Fin 2 → VF M} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

omit [M ⊨ Axioms.ACVF] in
/-- The coordinates of `(b, y)` after the first `m` are those of `y`. -/
theorem snoc2_natAdd (b : Fin m → VF M) (y : Fin 2 → VF M) (i : Fin 2) :
    (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) (Fin.natAdd m i) = y i := by
  fin_cases i
  · show (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) (Fin.natAdd m (0 : Fin 2)) = y 0
    rw [natAdd_two_zero]
    simp
  · show (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) (Fin.natAdd m (1 : Fin 2)) = y 1
    rw [natAdd_two_one]
    simp

omit [M ⊨ Axioms.ACVF] in
/-- The snoc convention agrees with `Fin.append`. -/
theorem snoc2_eq_append (b : Fin m → VF M) (y : Fin 2 → VF M) :
    (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) = Fin.append b y := by
  funext i
  refine Fin.addCases (m := m) (n := 2) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    show (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) j.castSucc.castSucc = b j
    simp
  · rw [Fin.append_right, snoc2_natAdd]

omit [M ⊨ Axioms.ACVF] in
theorem snoc2_eq_iff {b : Fin m → VF M} {x y : Fin 2 → VF M} :
    (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) =
      Fin.snoc (Fin.snoc b (y 0)) (y 1) ↔ x = y := by
  constructor
  · intro h
    apply fin_two_ext
    · simpa using congrFun h (Fin.last m).castSucc
    · simpa using congrFun h (Fin.last (m + 1))
  · rintro rfl
    rfl

omit [M ⊨ Axioms.ACVF] in
theorem init_init_snoc2 (b : Fin m → VF M) (y : Fin 2 → VF M) :
    Fin.init (Fin.init (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M)) = b := by
  simp only [Fin.init_snoc]

omit [M ⊨ Axioms.ACVF] in
theorem init_snoc2 (b : Fin m → VF M) (y : Fin 2 → VF M) :
    Fin.init (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) = Fin.snoc b (y 0) :=
  Fin.init_snoc _ _

omit [M ⊨ Axioms.ACVF] in
/-- A tuple whose first `m` coordinates are `b` is `(b, y)`. -/
theorem eq_snoc2_of_init {b : Fin m → VF M} {a : Fin (m + 2) → VF M}
    (h : Fin.init (Fin.init a) = b) :
    a = Fin.snoc (Fin.snoc b (a (Fin.natAdd m 0))) (a (Fin.natAdd m 1)) := by
  rw [natAdd_two_zero, natAdd_two_one]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp
    · simp only [Fin.snoc_castSucc]
      rw [← h]
      rfl

end Coordinates

/-! ### The two-dimensional slice of a mixed set -/

section Slice

/-- The real codes of `(y, t) ↦ ((b, y), t)`. -/
def liftCodes2 (b : Fin m → VF M) (z : Fin 2 ⊕ Fin r → M) : Fin (m + 2) ⊕ Fin r → M :=
  Sum.elim (Fin.snoc (α := fun _ => M) (Fin.snoc (α := fun _ => M) (vfValues b) (z (.inl 0)))
    (z (.inl 1))) (z ∘ Sum.inr)

omit [M ⊨ Axioms.ACVF] in
theorem liftCodes2_definable (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    S'.DefinableMap LRV (liftCodes2 (r := r) b) := by
  rintro (i | i)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · have he : (fun z : Fin 2 ⊕ Fin r → M => liftCodes2 b z (.inl (Fin.last (m + 1)))) =
          fun z => z (.inl 1) := by
        funext z
        simp [liftCodes2]
      rw [he]
      exact Set.DefinableFun.proj LRV
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · have he : (fun z : Fin 2 ⊕ Fin r → M => liftCodes2 b z (.inl (Fin.last m).castSucc)) =
            fun z => z (.inl 0) := by
          funext z
          simp [liftCodes2]
        rw [he]
        exact Set.DefinableFun.proj LRV
      · have he : (fun z : Fin 2 ⊕ Fin r → M => liftCodes2 b z (.inl k.castSucc.castSucc)) =
            fun _ => (b k).val := by
          funext z
          simp [liftCodes2, vfValues]
        rw [he]
        exact LRV.definableFun_const _ (hS (Or.inr ⟨k, rfl⟩))
  · exact Set.DefinableFun.proj LRV

omit [M ⊨ Axioms.ACVF] in
theorem liftCodes2_mixedValues (b : Fin m → VF M) (p : Mixed M 2 r) :
    liftCodes2 b (mixedValues p) =
      mixedValues ((Fin.snoc (Fin.snoc b (p.1 0)) (p.1 1), p.2) : Mixed M (m + 2) r) := by
  funext i
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [liftCodes2, mixedValues, vfValues]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [liftCodes2, mixedValues, vfValues]
      · simp [liftCodes2, mixedValues, vfValues]
  · rfl

omit [M ⊨ Axioms.ACVF] in
theorem liftCodes2_decode (b : Fin m → VF M) (c : (rawMixedSpace (M := M) 2 r).domain) :
    liftCodes2 b c.val = mixedValues
      ((Fin.snoc (Fin.snoc b (((rawMixedSpace (M := M) 2 r).decode c).1 0))
          (((rawMixedSpace (M := M) 2 r).decode c).1 1),
        ((rawMixedSpace (M := M) 2 r).decode c).2) : Mixed M (m + 2) r) := by
  rw [← liftCodes2_mixedValues, mixedValues_decode]

/-- The definable map `(y, t) ↦ ((b, y), t)` over `S'`. -/
def liftMap2 (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    Map (DefSet.univ (rawMixedSpace (M := M) 2 r) S')
      (DefSet.univ (rawMixedSpace (M := M) (m + 2) r) S') :=
  Map.ofCodes _ (fun p : Mixed M 2 r =>
      ((Fin.snoc (Fin.snoc b (p.1 0)) (p.1 1), p.2) : Mixed M (m + 2) r))
    (liftCodes2 b) (liftCodes2_definable b hS)
    (fun c => (liftCodes2_decode b c) ▸ mixedValues_mem_domain _)
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (liftCodes2_decode b c)))

/-- The two-dimensional slice `X_b = {(y, t) ∈ VF² × RVʳ | ((b, y), t) ∈ X}`, over a
base `S'` containing `S` and the coordinates of `b`. -/
def slice2 (X : DefSet (rawMixedSpace (M := M) (m + 2) r) S) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') : DefSet (rawMixedSpace (M := M) 2 r) S' where
  carrier := {p | ((Fin.snoc (Fin.snoc b (p.1 0)) (p.1 1), p.2) : Mixed M (m + 2) r) ∈ X.carrier}
  definable := by
    have h := (liftMap2 (r := r) b hS).definable_preimage
      (X.definable.mono _ (Set.subset_union_left.trans hS))
    convert h using 1
    ext p
    constructor
    · intro hp
      exact ⟨⟨p, Set.mem_univ _⟩, rfl, hp⟩
    · rintro ⟨a, rfl, ha⟩
      exact ha

variable {X : DefSet (rawMixedSpace (M := M) (m + 2) r) S} {b : Fin m → VF M}
  {hS : S ∪ Set.range (vfValues b) ⊆ S'}

omit [M ⊨ Axioms.ACVF] in
theorem mem_slice2 (p : Mixed M 2 r) :
    p ∈ (slice2 X b hS).carrier ↔
      ((Fin.snoc (Fin.snoc b (p.1 0)) (p.1 1), p.2) : Mixed M (m + 2) r) ∈ X.carrier :=
  Iff.rfl

omit [M ⊨ Axioms.ACVF] in
/-- Membership in the slice, in the `Fin.append` convention. -/
theorem mem_slice2_append (p : Mixed M 2 r) :
    p ∈ (slice2 X b hS).carrier ↔ ((Fin.append b p.1, p.2) : Mixed M (m + 2) r) ∈ X.carrier := by
  rw [mem_slice2, snoc2_eq_append]

omit [M ⊨ Axioms.ACVF] in
theorem slice2_mono {Y : DefSet (rawMixedSpace (M := M) (m + 2) r) S}
    (h : Y.carrier ⊆ X.carrier) :
    (slice2 Y b hS).carrier ⊆ (slice2 X b hS).carrier :=
  fun _ hp => h hp

omit [M ⊨ Axioms.ACVF] in
theorem slice2_carrier_eq_empty (h : X.carrier = ∅) :
    (slice2 X b hS).carrier = ∅ := by
  ext p
  constructor
  · intro hp
    have h' : ((Fin.snoc (Fin.snoc b (p.1 0)) (p.1 1), p.2) : Mixed M (m + 2) r) ∈ X.carrier := hp
    rw [h] at h'
    exact h'.elim
  · intro hp
    exact hp.elim

/-- The point of `X` over a point of the slice. -/
def liftElem2 (q : slice2 X b hS) : X :=
  ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2), q.property⟩

omit [M ⊨ Axioms.ACVF] in
@[simp] theorem liftElem2_val (q : slice2 X b hS) :
    (liftElem2 q).val = ((Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2) :
      Mixed M (m + 2) r) := rfl

/-- The definable map `X_b → X`, `(y, t) ↦ ((b, y), t)`, over `S'`. -/
def liftElem2Map (X : DefSet (rawMixedSpace (M := M) (m + 2) r) S) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    Map (slice2 X b hS) (extendDefSetBase (Set.subset_union_left.trans hS) X) :=
  ((liftMap2 (r := r) b hS).comp (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict
    (fun q => q.property)

omit [M ⊨ Axioms.ACVF] in
@[simp] theorem liftElem2Map_val (q : slice2 X b hS) :
    (liftElem2Map X b hS q).val =
      ((Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2) : Mixed M (m + 2) r) := rfl

theorem congruent_snoc2 {α : Fin (m + 2) → Gamma M} {x y : Fin 2 → VF M}
    (h : Congruent (fun i => α (Fin.natAdd m i)) x y) :
    Congruent α (Fin.snoc (Fin.snoc b (x 0)) (x 1)) (Fin.snoc (Fin.snoc b (y 0)) (y 1)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h1 := h 1
    simp only [natAdd_two_one] at h1
    simpa using h1
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · have h0 := h 0
      simp only [natAdd_two_zero] at h0
      simpa using h0
    · simpa using DiamondIntegral.Section6.Congruent.refl α
        (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) k.castSucc.castSucc

theorem slice2_vfBounded (hX : VFBounded X.carrier) : VFBounded (slice2 X b hS).carrier := by
  obtain ⟨γ, hγ⟩ := hX
  refine ⟨γ, fun p hp i => ?_⟩
  simpa only [snoc2_natAdd] using hγ _ ((mem_slice2 p).mp hp) (Fin.natAdd m i)

theorem slice2_vfDoublyBounded (hX : VFDoublyBounded X.carrier) :
    VFDoublyBounded (slice2 X b hS).carrier := by
  obtain ⟨γ, hγ⟩ := hX
  refine ⟨γ, fun p hp i => ?_⟩
  simpa only [snoc2_natAdd] using hγ _ ((mem_slice2 p).mp hp) (Fin.natAdd m i)

theorem slice2_rvBounded (hX : RVSupportDoublyBounded X.carrier) :
    RVSupportDoublyBounded (slice2 X b hS).carrier := by
  obtain ⟨γ, hγ⟩ := hX
  exact ⟨γ, fun p hp i => hγ _ hp i⟩

/-- The slice of a proper invariant set is proper invariant over `S'`: the radii of
`X` in the last two coordinates serve for the slice. -/
theorem slice2_properInvariant (hX : ProperInvariant S X.carrier) :
    ProperInvariant S' (slice2 X b hS).carrier := by
  refine ⟨(slice2 X b hS).definable, slice2_vfBounded hX.vfBounded,
    slice2_rvBounded hX.rvBounded, fun t => ?_⟩
  obtain ⟨α, hα, hInv⟩ := hX.radii t
  refine ⟨fun i => α (Fin.natAdd m i), fun i => (hα (Fin.natAdd m i)).mono
    (Set.union_subset_union_left _ (Set.subset_union_left.trans hS)), fun x y hxy => ?_⟩
  exact hInv _ _ (congruent_snoc2 hxy)

omit [M ⊨ Axioms.ACVF] in
/-- Finite RV fibres pass to the slice. -/
theorem slice2_finiteRV (hfin : ∀ x : Fin (m + 2) → VF M, {u | (x, u) ∈ X.carrier}.Finite)
    (x : Fin 2 → VF M) : {u | (x, u) ∈ (slice2 X b hS).carrier}.Finite :=
  hfin (Fin.snoc (Fin.snoc b (x 0)) (x 1))

theorem continuous_snoc2_const (b : Fin m → VF M) {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VF M) G] :
    Continuous (fun x : Fin 2 → VF M => (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M)) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact continuous_apply 1
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact continuous_apply 0
    · simp only [Fin.snoc_castSucc]
      exact continuous_const

end Slice

/-! ### Restricting a map that fixes the first `m` coordinates -/

section SliceMap

/-- The real codes of `(y, v) ↦ ((y_{m+1}, y_{m+2}), v)`. -/
def lastTwoCodes (z : Fin (m + 2) ⊕ Fin s → M) : Fin 2 ⊕ Fin s → M :=
  Sum.elim (fun i => z (.inl (Fin.natAdd m i))) (z ∘ Sum.inr)

omit [M ⊨ Axioms.ACVF] in
theorem lastTwoCodes_mixedValues (p : Mixed M (m + 2) s) :
    lastTwoCodes (mixedValues p) =
      mixedValues ((fun i => p.1 (Fin.natAdd m i), p.2) : Mixed M 2 s) := by
  funext i
  rcases i with i | i <;> rfl

omit [M ⊨ Axioms.ACVF] in
theorem lastTwoCodes_decode (c : (rawMixedSpace (M := M) (m + 2) s).domain) :
    lastTwoCodes c.val = mixedValues
      ((fun i => ((rawMixedSpace (M := M) (m + 2) s).decode c).1 (Fin.natAdd m i),
        ((rawMixedSpace (M := M) (m + 2) s).decode c).2) : Mixed M 2 s) := by
  rw [← lastTwoCodes_mixedValues, mixedValues_decode]

/-- The definable map `(y, v) ↦ ((y_{m+1}, y_{m+2}), v)`. -/
def lastTwoMap {T : Set M} (A : DefSet (rawMixedSpace (M := M) (m + 2) s) T) :
    Map A (DefSet.univ (rawMixedSpace (M := M) 2 s) T) :=
  Map.ofCodes A (fun p : Mixed M (m + 2) s => ((fun i => p.1 (Fin.natAdd m i), p.2) : Mixed M 2 s))
    lastTwoCodes (by rintro (i | i) <;> exact Set.DefinableFun.proj LRV)
    (fun c => (lastTwoCodes_decode c) ▸ mixedValues_mem_domain _)
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (lastTwoCodes_decode c)))

variable {X : DefSet (rawMixedSpace (M := M) (m + 2) r) S}
  {X' : DefSet (rawMixedSpace (M := M) (m + 2) s) S} {b : Fin m → VF M}
  {hS : S ∪ Set.range (vfValues b) ⊆ S'}

omit [M ⊨ Axioms.ACVF] in
theorem fix2_init {f : Map X X'}
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
    (q : slice2 X b hS) : Fin.init (Fin.init (f (liftElem2 q)).val.1) = b := by
  rw [hfix]
  exact init_init_snoc2 b q.val.1

omit [M ⊨ Axioms.ACVF] in
theorem fix2_snoc {f : Map X X'}
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
    (q : slice2 X b hS) :
    (Fin.snoc (Fin.snoc b ((f (liftElem2 q)).val.1 (Fin.natAdd m 0)))
        ((f (liftElem2 q)).val.1 (Fin.natAdd m 1)) : Fin (m + 2) → VF M) =
      (f (liftElem2 q)).val.1 :=
  (eq_snoc2_of_init (fix2_init hfix q)).symm

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_mem {f : Map X X'}
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
    (q : slice2 X b hS) :
    ((fun i => (f (liftElem2 q)).val.1 (Fin.natAdd m i), (f (liftElem2 q)).val.2) : Mixed M 2 s) ∈
      (slice2 X' b hS).carrier := by
  show ((Fin.snoc (Fin.snoc b ((f (liftElem2 q)).val.1 (Fin.natAdd m 0)))
      ((f (liftElem2 q)).val.1 (Fin.natAdd m 1)), (f (liftElem2 q)).val.2) :
    Mixed M (m + 2) s) ∈ X'.carrier
  rw [fix2_snoc hfix q]
  exact (f (liftElem2 q)).property

/-- The restriction `f_b : X_b → X'_b` of a map fixing the first `m` VF
coordinates, `(y, t) ↦ ((z_{m+1}, z_{m+2}), v)` where
`f((b, y), t) = ((b, z_{m+1}, z_{m+2}), v)`. -/
def sliceMap2 (f : Map X X')
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1)) :
    Map (slice2 X b hS) (slice2 X' b hS) :=
  ((lastTwoMap _).comp ((extendMapBase (Set.subset_union_left.trans hS) f).comp
    (liftElem2Map X b hS))).corestrict (fun q => sliceMap2_mem hfix q)

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_val (f : Map X X')
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
    (q : slice2 X b hS) :
    (sliceMap2 f hfix q).val =
      ((fun i => (f ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2), q.property⟩).val.1
          (Fin.natAdd m i),
        (f ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2), q.property⟩).val.2) :
        Mixed M 2 s) := rfl

variable {f : Map X X'}
  (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
include hfix

omit [M ⊨ Axioms.ACVF] in
theorem liftElem2_sliceMap2 (q : slice2 X b hS) :
    liftElem2 (sliceMap2 f hfix q) = f (liftElem2 q) :=
  Subtype.ext (Prod.ext (fix2_snoc hfix q) rfl)

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_injective (hf : Function.Injective f) :
    Function.Injective (sliceMap2 (b := b) (hS := hS) f hfix) := by
  intro q q' h
  have h1 : f (liftElem2 q) = f (liftElem2 q') := by
    rw [← liftElem2_sliceMap2 hfix q, ← liftElem2_sliceMap2 hfix q', h]
  have h2 : ((Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2) : Mixed M (m + 2) r) =
      (Fin.snoc (Fin.snoc b (q'.val.1 0)) (q'.val.1 1), q'.val.2) := congrArg Subtype.val (hf h1)
  have h3 := congrArg Prod.snd h2
  apply Subtype.ext
  exact Prod.ext (snoc2_eq_iff.mp (congrArg Prod.fst h2)) h3

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_surjective (hf : Function.Surjective f) :
    Function.Surjective (sliceMap2 (b := b) (hS := hS) f hfix) := by
  intro q'
  obtain ⟨p, hp⟩ := hf (liftElem2 q')
  have hinit : Fin.init (Fin.init p.val.1) = b := by
    rw [← hfix p, hp]
    exact init_init_snoc2 b q'.val.1
  have hpX : ((Fin.snoc (Fin.snoc b (p.val.1 (Fin.natAdd m 0))) (p.val.1 (Fin.natAdd m 1)),
      p.val.2) : Mixed M (m + 2) r) ∈ X.carrier := by
    rw [← eq_snoc2_of_init hinit]
    exact p.property
  refine ⟨⟨(fun i => p.val.1 (Fin.natAdd m i), p.val.2), hpX⟩, ?_⟩
  have hl : liftElem2 (⟨(fun i => p.val.1 (Fin.natAdd m i), p.val.2), hpX⟩ : slice2 X b hS) = p :=
    Subtype.ext (Prod.ext (eq_snoc2_of_init hinit).symm rfl)
  apply Subtype.ext
  change ((fun i => (f (liftElem2 (⟨(fun i => p.val.1 (Fin.natAdd m i), p.val.2), hpX⟩ :
    slice2 X b hS))).val.1 (Fin.natAdd m i), (f (liftElem2 (⟨(fun i => p.val.1 (Fin.natAdd m i),
      p.val.2), hpX⟩ : slice2 X b hS))).val.2) : Mixed M 2 s) = q'.val
  rw [hl, hp]
  exact Prod.ext (funext fun i => snoc2_natAdd b q'.val.1 i) rfl

omit [M ⊨ Axioms.ACVF] in
/-- The restriction of a bijection is a bijection. -/
theorem sliceMap2_bijective (hf : Function.Bijective f) :
    Function.Bijective (sliceMap2 (b := b) (hS := hS) f hfix) :=
  ⟨sliceMap2_injective hfix hf.1, sliceMap2_surjective hfix hf.2⟩

omit [M ⊨ Axioms.ACVF] in
theorem graphFibre_init2 {u : Fin r → RVInfinity M} {v : Fin s → RVInfinity M}
    {a c : Fin (m + 2) → VF M} (h : graphFibre f u v a c) :
    Fin.init (Fin.init c) = Fin.init (Fin.init a) := by
  obtain ⟨p, hp, hfp⟩ := h
  simpa [hfp, hp] using hfix p

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_graphFibre_iff (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (x y : Fin 2 → VF M) :
    graphFibre (sliceMap2 (b := b) (hS := hS) f hfix) u v x y ↔
      graphFibre f u v (Fin.snoc (Fin.snoc b (x 0)) (x 1)) (Fin.snoc (Fin.snoc b (y 0)) (y 1)) := by
  constructor
  · rintro ⟨q, hq, hgq⟩
    refine ⟨liftElem2 q, ?_, ?_⟩
    · rw [liftElem2_val, hq]
    · rw [← liftElem2_sliceMap2 hfix q, liftElem2_val, hgq]
  · rintro ⟨p, hp, hfp⟩
    have hq : ((Fin.snoc (Fin.snoc b (x 0)) (x 1), u) : Mixed M (m + 2) r) ∈ X.carrier :=
      hp ▸ p.property
    refine ⟨⟨(x, u), hq⟩, rfl, ?_⟩
    have hl : liftElem2 (⟨(x, u), hq⟩ : slice2 X b hS) = p := Subtype.ext hp.symm
    change ((fun i => (f (liftElem2 (⟨(x, u), hq⟩ : slice2 X b hS))).val.1 (Fin.natAdd m i),
      (f (liftElem2 (⟨(x, u), hq⟩ : slice2 X b hS))).val.2) : Mixed M 2 s) = (y, v)
    rw [hl, hfp]
    exact Prod.ext (funext fun i => snoc2_natAdd b y i) rfl

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_graphFibreSource (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (sliceMap2 (b := b) (hS := hS) f hfix) u v =
      {x | (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) ∈ graphFibreSource f u v} := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, (sliceMap2_graphFibre_iff hfix u v x y).mp hy⟩
  · rintro ⟨c, hc⟩
    have hinit : Fin.init (Fin.init c) = b := by
      rw [graphFibre_init2 hfix hc]
      exact init_init_snoc2 b x
    refine ⟨fun i => c (Fin.natAdd m i), (sliceMap2_graphFibre_iff hfix u v x _).mpr ?_⟩
    show graphFibre f u v (Fin.snoc (Fin.snoc b (x 0)) (x 1))
      (Fin.snoc (Fin.snoc b (c (Fin.natAdd m 0))) (c (Fin.natAdd m 1)))
    rw [← eq_snoc2_of_init hinit]
    exact hc

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap2_graphFibreRange (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange (sliceMap2 (b := b) (hS := hS) f hfix) u v =
      {y | (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) ∈ graphFibreRange f u v} := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (sliceMap2_graphFibre_iff hfix u v x y).mp hx⟩
  · rintro ⟨a, ha⟩
    have hinit : Fin.init (Fin.init a) = b := by
      rw [← graphFibre_init2 hfix ha]
      exact init_init_snoc2 b y
    refine ⟨fun i => a (Fin.natAdd m i), (sliceMap2_graphFibre_iff hfix u v _ y).mpr ?_⟩
    show graphFibre f u v (Fin.snoc (Fin.snoc b (a (Fin.natAdd m 0))) (a (Fin.natAdd m 1)))
      (Fin.snoc (Fin.snoc b (y 0)) (y 1))
    rw [← eq_snoc2_of_init hinit]
    exact ha

theorem sliceMap2_graphFibreMap (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    {x : Fin 2 → VF M} (hx : x ∈ graphFibreSource (sliceMap2 (b := b) (hS := hS) f hfix) u v) :
    graphFibreMap (sliceMap2 (b := b) (hS := hS) f hfix) u v x =
      fun i => graphFibreMap f u v (Fin.snoc (Fin.snoc b (x 0)) (x 1)) (Fin.natAdd m i) := by
  have h1 := (sliceMap2_graphFibre_iff hfix u v x _).mp (graphFibreMap_graph _ u v hx)
  have hx' : (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) ∈ graphFibreSource f u v :=
    ⟨_, h1⟩
  have h2 := graphFibre_functional f u v h1 (graphFibreMap_graph f u v hx')
  funext i
  rw [← h2, snoc2_natAdd]

/-- The restriction of a proper covariant map is proper covariant: the radii
of `f` in the last two coordinates serve for `f_b`. -/
theorem sliceMap2_properCovariant (hf : ProperCovariant f) :
    ProperCovariant (sliceMap2 (b := b) (hS := hS) f hfix) := by
  refine ⟨slice2_vfBounded hf.sourceVFBounded, ?_, slice2_rvBounded hf.sourceRVBounded, ?_,
    fun u v => ?_⟩
  · obtain ⟨γ, hγ⟩ := hf.imageVFBounded
    refine ⟨γ, ?_⟩
    rintro _ ⟨q, rfl⟩ i
    exact hγ _ ⟨liftElem2 q, rfl⟩ (Fin.natAdd m i)
  · obtain ⟨γ, hγ⟩ := hf.imageRVBounded
    refine ⟨γ, ?_⟩
    rintro _ ⟨q, rfl⟩ i
    exact hγ _ ⟨liftElem2 q, rfl⟩ i
  · obtain ⟨α, β, hα, hβ, hInvα, hInvβ, hcov⟩ := hf.radii u v
    have hbase : graphFibreBase S u v ⊆ graphFibreBase S' u v :=
      Set.union_subset_union_left _ (Set.union_subset_union_left _ (Set.subset_union_left.trans hS))
    refine ⟨fun i => α (Fin.natAdd m i), fun i => β (Fin.natAdd m i),
      fun _ => (hα _).mono hbase, fun _ => (hβ _).mono hbase, ?_, ?_, ?_⟩
    · rw [sliceMap2_graphFibreSource hfix]
      intro x y hxy
      exact hInvα _ _ (congruent_snoc2 hxy)
    · rw [sliceMap2_graphFibreRange hfix]
      intro x y hxy
      exact hInvβ _ _ (congruent_snoc2 hxy)
    · intro x hx y hy hxy
      have hx' : (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) ∈
          graphFibreSource f u v := by
        have h := hx
        rwa [sliceMap2_graphFibreSource hfix] at h
      have hy' : (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) ∈
          graphFibreSource f u v := by
        have h := hy
        rwa [sliceMap2_graphFibreSource hfix] at h
      have h := hcov _ hx' _ hy' (congruent_snoc2 hxy)
      rw [sliceMap2_graphFibreMap hfix u v hx, sliceMap2_graphFibreMap hfix u v hy]
      exact fun i => h (Fin.natAdd m i)

/-- The restriction of a map continuous on its graph fibres is continuous on
its graph fibres. -/
theorem sliceMap2_continuous {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (hf : ContinuousOnGraphFibres (G := G) f) :
    ContinuousOnGraphFibres (G := G) (sliceMap2 (b := b) (hS := hS) f hfix) := by
  intro u v
  have hπ : Continuous (fun w : Fin (m + 2) → VF M => (fun i : Fin 2 => w (Fin.natAdd m i))) :=
    continuous_pi fun _ => continuous_apply _
  have hmaps : Set.MapsTo
      (fun x : Fin 2 → VF M => (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M))
      (graphFibreSource (sliceMap2 (b := b) (hS := hS) f hfix) u v) (graphFibreSource f u v) := by
    intro x hx
    rw [sliceMap2_graphFibreSource hfix] at hx
    exact hx
  refine (hπ.comp_continuousOn ((hf u v).comp (continuous_snoc2_const b (G := G)).continuousOn
    hmaps)).congr ?_
  intro x hx
  exact sliceMap2_graphFibreMap hfix u v hx

omit [M ⊨ Axioms.ACVF] in
theorem fix2_inverse (hf : Function.Bijective f) :
    ∀ p : X', Fin.init (Fin.init ((f.inverse hf) p).val.1) = Fin.init (Fin.init p.val.1) := by
  intro p
  have h := hfix (f.inverse hf p)
  rw [Map.apply_inverse] at h
  exact h.symm

omit [M ⊨ Axioms.ACVF] in
/-- The inverse of the restriction is the restriction of the inverse. -/
theorem sliceMap2_inverse (hf : Function.Bijective f)
    (hbij : Function.Bijective (sliceMap2 (b := b) (hS := hS) f hfix)) :
    (sliceMap2 (b := b) (hS := hS) f hfix).inverse hbij =
      sliceMap2 (b := b) (hS := hS) (f.inverse hf) (fix2_inverse hfix hf) := by
  apply Map.ext
  intro q'
  apply hbij.1
  rw [Map.apply_inverse]
  apply Subtype.ext
  change q'.val = ((fun i => (f (liftElem2 (sliceMap2 (f.inverse hf) (fix2_inverse hfix hf) q'))).val.1
    (Fin.natAdd m i), (f (liftElem2 (sliceMap2 (f.inverse hf) (fix2_inverse hfix hf) q'))).val.2) :
      Mixed M 2 s)
  rw [liftElem2_sliceMap2 (fix2_inverse hfix hf) q', Map.apply_inverse]
  exact Prod.ext (funext fun i => (snoc2_natAdd b q'.val.1 i).symm) rfl

/-- The restriction of a proper covariant homeomorphism fixing the first `m`
VF coordinates is a proper covariant homeomorphism over `S'`. -/
theorem sliceMap2_homeomorphism {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (hf : ProperCovariantHomeomorphism (G := G) f) :
    ProperCovariantHomeomorphism (G := G) (sliceMap2 (b := b) (hS := hS) f hfix) := by
  have hbij := sliceMap2_bijective (b := b) (hS := hS) hfix hf.bijective
  refine ⟨hbij, sliceMap2_properCovariant hfix hf.covariant, sliceMap2_continuous hfix hf.continuous,
    ?_, ?_⟩
  · rw [sliceMap2_inverse hfix hf.bijective hbij]
    exact sliceMap2_properCovariant _ hf.inverseCovariant
  · rw [sliceMap2_inverse hfix hf.bijective hbij]
    exact sliceMap2_continuous _ hf.inverseContinuous

end SliceMap

/-! ### The derivative of the restriction -/

section Derivative

theorem castAdd_ne_natAdd {k : ℕ} (j : Fin m) (i : Fin k) : Fin.castAdd k j ≠ Fin.natAdd m i := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := j.isLt
  omega

/-- A square matrix whose first `m` rows are unit rows has the determinant of its
lower right block: after reindexing by `Fin m ⊕ Fin k` it is block lower
triangular with the identity in the upper left corner. -/
theorem det_eq_det_submatrix_natAdd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin (m + k)) (Fin (m + k)) R)
    (hA : ∀ (j : Fin m) (i : Fin (m + k)),
      A (Fin.castAdd k j) i = if Fin.castAdd k j = i then 1 else 0) :
    A.det = (A.submatrix (Fin.natAdd m) (Fin.natAdd m)).det := by
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm A]
  have h : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A =
      Matrix.fromBlocks 1 0 (A.submatrix (Fin.natAdd m) (Fin.castAdd k))
        (A.submatrix (Fin.natAdd m) (Fin.natAdd m)) := by
    ext (i | i) (j | j)
    · simp [hA, Matrix.one_apply, Fin.ext_iff]
    · simp [hA, castAdd_ne_natAdd]
    · simp
    · simp
  rw [h, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

variable {X : DefSet (rawMixedSpace (M := M) (m + 2) r) S}
  {X' : DefSet (rawMixedSpace (M := M) (m + 2) s) S} {b : Fin m → VF M}
  {hS : S ∪ Set.range (vfValues b) ⊆ S'}

/-- The linear map `x ↦ (0, …, 0, x₀, x₁)`. -/
def lastTwoEmbedding : (Fin 2 → VF M) →ₗ[VF M] (Fin (m + 2) → VF M) where
  toFun x := Fin.append (0 : Fin m → VF M) x
  map_add' x y := by
    funext i
    refine Fin.addCases (m := m) (n := 2) (fun j => ?_) (fun j => ?_) i <;>
      simp [Fin.append_left, Fin.append_right]
  map_smul' c x := by
    funext i
    refine Fin.addCases (m := m) (n := 2) (fun j => ?_) (fun j => ?_) i <;>
      simp [Fin.append_left, Fin.append_right]

/-- The last two coordinates, as a linear map to `VF²`. -/
def lastTwoProj : (Fin (m + 2) → VF M) →ₗ[VF M] (Fin 2 → VF M) :=
  LinearMap.funLeft (VF M) (VF M) (Fin.natAdd m)

theorem lastTwoEmbedding_apply (x : Fin 2 → VF M) :
    lastTwoEmbedding (m := m) x = Fin.append 0 x := rfl

theorem lastTwoProj_apply (w : Fin (m + 2) → VF M) :
    lastTwoProj w = fun i => w (Fin.natAdd m i) := rfl

theorem lastTwoEmbedding_single (j : Fin 2) :
    lastTwoEmbedding (M := M) (m := m) (Pi.single j 1) = Pi.single (Fin.natAdd m j) 1 := by
  funext k
  refine Fin.addCases (m := m) (n := 2) (fun a => ?_) (fun a => ?_) k
  · rw [lastTwoEmbedding_apply, Fin.append_left]
    simp [castAdd_ne_natAdd]
  · rw [lastTwoEmbedding_apply, Fin.append_right]
    simp [Pi.single_apply]

theorem snoc2_eq_affine (b : Fin m → VF M) (x : Fin 2 → VF M) :
    (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) =
      lastTwoEmbedding x + Fin.append b 0 := by
  rw [snoc2_eq_append]
  funext i
  refine Fin.addCases (m := m) (n := 2) (fun j => ?_) (fun j => ?_) i <;>
    simp [lastTwoEmbedding_apply, Fin.append_left, Fin.append_right]

theorem hasVFDerivativeAt_lastTwoProj (a : Fin (m + 2) → VF M) :
    HasVFDerivativeAt (lastTwoProj (m := m)) a lastTwoProj := by
  have h := hasVFDerivativeAt_affine (lastTwoProj (M := M) (m := m)) 0 a
  have he : (fun x => lastTwoProj (M := M) (m := m) x + 0) = lastTwoProj :=
    funext fun x => add_zero _
  rwa [he] at h

theorem hasVFDerivativeAt_snoc2 (b : Fin m → VF M) (x : Fin 2 → VF M) :
    HasVFDerivativeAt
      (fun x : Fin 2 → VF M => (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M)) x
      lastTwoEmbedding := by
  have h := hasVFDerivativeAt_affine (lastTwoEmbedding (M := M) (m := m)) (Fin.append b 0) x
  have he : (fun x => lastTwoEmbedding x + Fin.append b 0) =
      fun x : Fin 2 → VF M => (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) :=
    funext fun x => (snoc2_eq_affine b x).symm
  rwa [he] at h

theorem snoc2_mem_vfBall {x y : Fin 2 → VF M} {ρ : Gamma M} (h : x ∈ vfBall y ρ) :
    (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M) ∈
      vfBall (Fin.snoc (Fin.snoc b (y 0)) (y 1)) ρ := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h 1
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using h 0
    · simpa using mem_vfBall_self (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) ρ
        k.castSucc.castSucc

/-- The derivative of the restriction. A chart of `f` agrees with the coordinate
projections in the first `m` coordinates on a ball, so the first `m` rows of `L`
are unit rows. The matrix of `L` is block lower triangular with the identity in
the upper left corner, and its determinant is that of the lower right `2 × 2`
block, the derivative of `f_b`. -/
theorem sliceMap2_derivative (f : Map X X')
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
    (q : slice2 X b hS) {L : (Fin (m + 2) → VF M) →ₗ[VF M] (Fin (m + 2) → VF M)}
    (hL : HasMixedVFDerivativeAt f
      ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2), q.property⟩ L) :
    ∃ L₂ : (Fin 2 → VF M) →ₗ[VF M] (Fin 2 → VF M),
      HasMixedVFDerivativeAt (sliceMap2 f hfix) q L₂ ∧
        (LinearMap.toMatrix' L₂).det = (LinearMap.toMatrix' L).det := by
  obtain ⟨F, ⟨ρ, hρ⟩, hFL⟩ := hL
  have hFL' : HasVFDerivativeAt F (Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1)) L := hFL
  -- The first `m` rows of `L` are unit rows.
  have hrow : ∀ (j : Fin m) (w : Fin (m + 2) → VF M),
      L w (Fin.castAdd 2 j) = w (Fin.castAdd 2 j) := by
    intro j w
    have hcomp : HasVFDerivativeAt (coordProj (Fin.castAdd 2 j) ∘ F)
        (Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1)) ((coordProj (Fin.castAdd 2 j)).comp L) :=
      HasVFDerivativeAt.comp (hasVFDerivativeAt_coordProj (Fin.castAdd 2 j) _) hFL'
    have heq : Set.EqOn (coordProj (Fin.castAdd 2 j) ∘ F) (coordProj (Fin.castAdd 2 j))
        (vfBall (Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1)) ρ) := by
      intro y hy
      obtain ⟨hyX, hfy⟩ := hρ y hy
      have h1 : (f ⟨(y, q.val.2), hyX⟩).val.1 = F y := congrArg Prod.fst hfy
      have h2 : (f ⟨(y, q.val.2), hyX⟩).val.1 (Fin.castAdd 2 j) = y (Fin.castAdd 2 j) :=
        congrFun (hfix ⟨(y, q.val.2), hyX⟩) j
      rw [h1] at h2
      funext k
      simp [coordProj_apply, h2]
    have hD := (hcomp.congr_on_vfBall heq).unique
      (hasVFDerivativeAt_coordProj (Fin.castAdd 2 j) _)
    have h := congrFun (LinearMap.congr_fun hD w) 0
    simpa [coordProj_apply] using h
  refine ⟨lastTwoProj.comp (L.comp lastTwoEmbedding),
    ⟨fun x => lastTwoProj (F (Fin.snoc (Fin.snoc b (x 0)) (x 1))), ⟨ρ, fun x hx => ?_⟩, ?_⟩, ?_⟩
  · -- the chart
    obtain ⟨hxX, hfx⟩ := hρ _ (snoc2_mem_vfBall (b := b) hx)
    refine ⟨hxX, ?_⟩
    have e1 : (f ⟨(Fin.snoc (Fin.snoc b (x 0)) (x 1), q.val.2), hxX⟩).val.1 =
        F (Fin.snoc (Fin.snoc b (x 0)) (x 1)) := congrArg Prod.fst hfx
    have e2 : (f ⟨(Fin.snoc (Fin.snoc b (x 0)) (x 1), q.val.2), hxX⟩).val.2 =
        (f ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2), q.property⟩).val.2 := by
      have h := congrArg Prod.snd hfx
      exact h
    have e3 : (fun i : Fin 2 => (f ⟨(Fin.snoc (Fin.snoc b (x 0)) (x 1), q.val.2), hxX⟩).val.1
        (Fin.natAdd m i)) = lastTwoProj (F (Fin.snoc (Fin.snoc b (x 0)) (x 1))) := by
      rw [e1]
      rfl
    exact Prod.ext e3 e2
  · -- the derivative of the chart
    have h1 : HasVFDerivativeAt
        (F ∘ fun x : Fin 2 → VF M => (Fin.snoc (Fin.snoc b (x 0)) (x 1) : Fin (m + 2) → VF M))
        q.val.1 (L.comp lastTwoEmbedding) :=
      HasVFDerivativeAt.comp hFL' (hasVFDerivativeAt_snoc2 b q.val.1)
    exact HasVFDerivativeAt.comp (hasVFDerivativeAt_lastTwoProj _) h1
  · -- the determinant
    have hsub : LinearMap.toMatrix' (lastTwoProj.comp (L.comp lastTwoEmbedding)) =
        (LinearMap.toMatrix' L).submatrix (Fin.natAdd m) (Fin.natAdd m) := by
      ext i j
      rw [LinearMap.toMatrix'_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, lastTwoEmbedding_single, lastTwoProj_apply]
    have hA : ∀ (j : Fin m) (i : Fin (m + 2)), LinearMap.toMatrix' L (Fin.castAdd 2 j) i =
        if Fin.castAdd 2 j = i then 1 else 0 := by
      intro j i
      rw [LinearMap.toMatrix'_apply, hrow j, Pi.single_apply]
    rw [hsub]
    exact (det_eq_det_submatrix_natAdd (LinearMap.toMatrix' L) hA).symm

/-- The restriction of a map with unit derivative at the lifted point has unit
derivative. -/
theorem sliceMap2_unitDerivative (f : Map X X')
    (hfix : ∀ p : X, Fin.init (Fin.init (f p).val.1) = Fin.init (Fin.init p.val.1))
    (q : slice2 X b hS) (h : HasMixedUnitDerivativeAt f (liftElem2 q)) :
    HasMixedUnitDerivativeAt (sliceMap2 f hfix) q := by
  obtain ⟨L, hL, hdet⟩ := h
  obtain ⟨L₂, hL₂, hdet₂⟩ := sliceMap2_derivative f hfix q hL
  exact ⟨L₂, hL₂, hdet₂.trans hdet⟩

end Derivative

/-! ### Good points for two-dimensional slices -/

section GoodPoints

omit [M ⊨ Axioms.ACVF] in
/-- An empty definable set has VF dimension `0`. -/
theorem vfDim_lt_of_carrier_empty {n k j : ℕ} {T : Set M}
    (E : DefSet (rawMixedSpace (M := M) n k) T) (h : E.carrier = ∅) (hj : 0 < j) :
    vfDim (rawRVSpace (M := M) 1) E < j := by
  have he : E = DefSet.empty (rawMixedSpace (M := M) n k) T := by
    cases E
    cases h
    rfl
  have hz : vfDim (rawRVSpace (M := M) 1) (DefSet.empty (rawMixedSpace (M := M) n k) T) = 0 :=
    Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv k)
  rw [he, hz]
  exact hj

set_option backward.isDefEq.respectTransparency true in
/-- Evaluation at `(y, b)` through `sumAlgEquiv`: first evaluate the coefficients at
`b`, then the polynomial in two variables at `y`. -/
theorem eval₂_sumElim_eq_eval₂_sumAlgEquiv {K F : Type*} [CommRing K] [CommRing F] (φ : K →+* F)
    (y : Fin 2 → F) (b : Fin m → F) (Q : MvPolynomial (Fin 2 ⊕ Fin m) K) :
    MvPolynomial.eval₂ φ (Sum.elim y b) Q =
      MvPolynomial.eval₂ (MvPolynomial.eval₂Hom φ b) y
        (MvPolynomial.sumAlgEquiv K (Fin 2) (Fin m) Q) := by
  have h : MvPolynomial.eval₂Hom φ (Sum.elim y b) =
      (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom φ b) y).comp
        (MvPolynomial.sumAlgEquiv K (Fin 2) (Fin m)).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change φ a = MvPolynomial.eval₂ _ y
        (MvPolynomial.sumAlgEquiv K (Fin 2) (Fin m) (MvPolynomial.C a))
      rw [MvPolynomial.sumAlgEquiv_C_inl, MvPolynomial.eval₂_C, MvPolynomial.eval₂Hom_C]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change Sum.elim y b i = MvPolynomial.eval₂ _ y
        (MvPolynomial.sumAlgEquiv K (Fin 2) (Fin m) (MvPolynomial.X i))
      rcases i with i | i
      · rw [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.eval₂_X]
        rfl
      · rw [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.eval₂_C, MvPolynomial.eval₂Hom_X']
        rfl
  exact RingHom.congr_fun h Q

/-- The reindexing `VF^{m+2} = VF² × VFᵐ` (last two coordinates first). -/
def splitTwo : Fin (m + 2) ≃ Fin 2 ⊕ Fin m :=
  finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m) (Fin 2))

omit [M ⊨ Axioms.ACVF] in
theorem sumElim_comp_splitTwo (b : Fin m → VF M) (y : Fin 2 → VF M) :
    Sum.elim y b ∘ splitTwo = (Fin.snoc (Fin.snoc b (y 0)) (y 1) : Fin (m + 2) → VF M) := by
  rw [snoc2_eq_append]
  funext i
  refine Fin.addCases (m := m) (n := 2) (fun j => ?_) (fun j => ?_) i <;>
    simp [splitTwo, Fin.append_left, Fin.append_right]

/-- Let `K ≤ L` be subfields of `F`, `b ∈ Lᵐ`, and `R` a polynomial in two variables over
`K[X₁, …, Xₘ]` with a coefficient that does not vanish at `b`. Then no zero of `R(b, ·, ·)`
is algebraically independent over `L`: `R(b, ·, ·)` is a nonzero polynomial over `L`. -/
theorem not_algebraicIndependent_of_sumAlgEquiv_root {F : Type*} [Field F] {K L : Subfield F}
    (hKL : K ≤ L) (b : Fin m → F) (hb : ∀ j, b j ∈ L)
    (R : MvPolynomial (Fin 2) (MvPolynomial (Fin m) K)) (d : Fin 2 →₀ ℕ)
    (hd : MvPolynomial.eval₂ K.subtype b (R.coeff d) ≠ 0) (y : Fin 2 → F)
    (hy : MvPolynomial.eval₂ (MvPolynomial.eval₂Hom K.subtype b) y R = 0) :
    ¬ AlgebraicIndependent L y := by
  intro hInd
  let bL : Fin m → L := fun j => ⟨b j, hb j⟩
  let φ : MvPolynomial (Fin m) K →+* L := MvPolynomial.eval₂Hom (Subfield.inclusion hKL) bL
  have hφR : L.subtype.comp φ = MvPolynomial.eval₂Hom K.subtype b := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, φ, MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply, φ, MvPolynomial.eval₂Hom_X']
      rfl
  have hT0 : MvPolynomial.map φ R ≠ 0 := by
    intro h0
    apply hd
    have h1 : φ (R.coeff d) = 0 := by
      have h := MvPolynomial.coeff_map φ R d
      rw [h0] at h
      simpa using h.symm
    have h2 := RingHom.congr_fun hφR (R.coeff d)
    rw [RingHom.comp_apply, h1, map_zero] at h2
    exact h2.symm
  have hT : MvPolynomial.aeval y (MvPolynomial.map φ R) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, Subfield.algebraMap_ofSubfield, hφR]
    exact hy
  exact hT0 (hInd (hT.trans (map_zero _).symm))

/-- **Good points for two-dimensional slices.** For a set `Bad ⊆ VF^{m+2} × RVʳ` of VF
dimension `< m + 2` there is a nonzero polynomial `P` in `m` variables over the VF
parameter field of `S` such that, at every point `b` with `P(b) ≠ 0`, the slice `Bad_b`
has VF dimension `< 2` over every small base `S'` containing `S` and `b`.

`Bad` lies in the zero set of a nonzero polynomial `Q`. View `Q` as a polynomial in the
last two variables with coefficients in `K[X₁, …, Xₘ]` and let `P` be a nonzero
coefficient. If `P(b) ≠ 0`, then `Q(b, ·, ·)` is a nonzero polynomial over the VF
parameter field of `S'` vanishing on `Bad_b`, so no point of `Bad_b` is algebraically
independent over that field. -/
theorem exists_good_polynomial2 (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Bad : DefSet (rawMixedSpace (M := M) (m + 2) r) S)
    (hBad : vfDim (rawRVSpace (M := M) 1) Bad < m + 2) :
    ∃ P : MvPolynomial (Fin m) (vfParameterField S), P ≠ 0 ∧
      ∀ (b : Fin m → VF M) {S' : Set M} (hS : S ∪ Set.range (vfValues b) ⊆ S'),
        Cardinal.mk S' < κ → P.eval₂ (vfParameterField S).subtype b ≠ 0 →
          vfDim (rawRVSpace (M := M) 1) (slice2 Bad b hS) < 2 := by
  obtain ⟨Q, hQ0, hQ⟩ := GoodPoints.exists_polynomial_vanishing_of_dim_lt hc hs hsmall Bad hBad
  obtain ⟨R, hR⟩ : ∃ R, MvPolynomial.sumAlgEquiv (vfParameterField S) (Fin 2) (Fin m)
      (MvPolynomial.rename (splitTwo (m := m)) Q) = R := ⟨_, rfl⟩
  have hR0 : R ≠ 0 := by
    rintro rfl
    apply hQ0
    apply MvPolynomial.rename_injective _ (splitTwo (m := m)).injective
    rw [map_zero]
    exact (MvPolynomial.sumAlgEquiv _ _ _).injective (hR.trans (map_zero _).symm)
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hR0
  refine ⟨R.coeff d, hd, ?_⟩
  intro b S' hS hsmall' hPb
  have hKL : vfParameterField (M := M) S ≤ vfParameterField S' :=
    Subfield.closure_mono (fun x hx => hS (Or.inl hx))
  have hbL : ∀ j, b j ∈ vfParameterField (M := M) S' :=
    fun j => Subfield.subset_closure (hS (Or.inr ⟨j, rfl⟩))
  apply mixed_vfDim_lt_of_no_independent hc hs hsmall' _ (rawRVSpace_rvCoded 1) Nat.zero_lt_two
  intro p hInd
  refine not_algebraicIndependent_of_sumAlgEquiv_root hKL b hbL R d hPb p.val.1 ?_ hInd
  have hx : MvPolynomial.eval₂ (vfParameterField S).subtype
      (Fin.snoc (Fin.snoc b (p.val.1 0)) (p.val.1 1) : Fin (m + 2) → VF M) Q = 0 :=
    hQ ⟨_, p.property⟩
  rw [← hR, ← eval₂_sumElim_eq_eval₂_sumAlgEquiv, MvPolynomial.eval₂_rename,
    sumElim_comp_splitTwo]
  exact hx

/-- `exists_good_polynomial2` in the hypothesis shape of `stageSlice2`: a set that has
VF dimension `< m + 2` or is empty has good points whose two-dimensional slices have VF
dimension `< 2` or are empty. -/
theorem exists_good_polynomial2_or_empty (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Bad : DefSet (rawMixedSpace (M := M) (m + 2) r) S)
    (hBad : vfDim (rawRVSpace (M := M) 1) Bad < m + 2 ∨ Bad.carrier = ∅) :
    ∃ P : MvPolynomial (Fin m) (vfParameterField S), P ≠ 0 ∧
      ∀ (b : Fin m → VF M) {S' : Set M} (hS : S ∪ Set.range (vfValues b) ⊆ S'),
        Cardinal.mk S' < κ → P.eval₂ (vfParameterField S).subtype b ≠ 0 →
          vfDim (rawRVSpace (M := M) 1) (slice2 Bad b hS) < 2 ∨
            (slice2 Bad b hS).carrier = ∅ := by
  rcases hBad with hBad | hBad
  · obtain ⟨P, hP0, hP⟩ := exists_good_polynomial2 hc hs hsmall Bad hBad
    exact ⟨P, hP0, fun b S' hS h1 h2 => Or.inl (hP b hS h1 h2)⟩
  · exact ⟨1, one_ne_zero, fun b S' hS _ _ => Or.inr (slice2_carrier_eq_empty hBad)⟩

end GoodPoints

/-! ### Restricting a standard contraction stage -/

section Stage

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {Y : DefSet (rawMixedSpace (M := M) (m + 2) r) S}
variable (H : StandardContractionStage (G := G) Y) (b : Fin m → VF M)
  (hS : S ∪ Set.range (vfValues b) ⊆ S')

/-- A stage fixes the first `m` VF coordinates (it fixes the first `m + 1`). -/
theorem stage_fix2 :
    ∀ p : Y, Fin.init (Fin.init (H.lift p).val.1) = Fin.init (Fin.init p.val.1) :=
  fun p => funext fun j => H.relative p j.castSucc

/-- Membership in the slice of the target: `((b, y₀), u)` lies in the contracted set and
`rv(y₁) = u(leading)`. -/
theorem mem_slice2_target (p : Mixed M 2 H.arity) :
    p ∈ (slice2 H.target b hS).carrier ↔
      ((Fin.snoc b (p.1 0), p.2) : Mixed M (m + 1) H.arity) ∈ H.contracted.carrier ∧
        rv M (p.1 1) = p.2 H.leading := by
  rw [mem_slice2, H.recover_target]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa only [Fin.init_snoc] using h1, ?_⟩
    simpa only [Fin.snoc_last] using h2
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa only [Fin.init_snoc] using h1, ?_⟩
    simpa only [Fin.snoc_last] using h2

/-- Dropping the last coordinate of the two-dimensional slice of the target gives the
one-dimensional slice of the contracted set. -/
theorem contracted_slice2 :
    (vfDropLast (slice2 H.target b hS)).image.carrier = (sliceSet H.contracted b hS).carrier := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    have hq := (mem_slice2_target H b hS q.val).mp q.property
    have h0 : Fin.init q.val.1 0 = q.val.1 0 := by
      show q.val.1 (Fin.castSucc 0) = q.val.1 0
      rw [Fin.castSucc_zero]
    show ((Fin.snoc b (Fin.init q.val.1 0), q.val.2) : Mixed M (m + 1) H.arity) ∈
      H.contracted.carrier
    rw [h0]
    exact hq.1
  · intro hp
    obtain ⟨t, ht⟩ := hp
    have ht1 : Fin.init t.val.1 = Fin.snoc b (p.1 0) := congrArg Prod.fst ht
    have ht2 : t.val.2 = p.2 := congrArg Prod.snd ht
    have hrv := ((H.recover_target t.val).mp t.property).2
    have e0 : (Fin.snoc p.1 (t.val.1 (Fin.last (m + 1))) : Fin 2 → VF M) 0 = p.1 0 := by
      rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
    have e1 : (Fin.snoc p.1 (t.val.1 (Fin.last (m + 1))) : Fin 2 → VF M) 1 =
        t.val.1 (Fin.last (m + 1)) := by
      rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
    have hq : ((Fin.snoc p.1 (t.val.1 (Fin.last (m + 1))), p.2) : Mixed M 2 H.arity) ∈
        (slice2 H.target b hS).carrier := by
      refine (mem_slice2_target H b hS _).mpr ⟨?_, ?_⟩
      · show ((Fin.snoc b ((Fin.snoc p.1 (t.val.1 (Fin.last (m + 1))) : Fin 2 → VF M) 0), p.2) :
          Mixed M (m + 1) H.arity) ∈ H.contracted.carrier
        rw [e0, ← ht1, ← ht2]
        exact ⟨t, rfl⟩
      · show rv M ((Fin.snoc p.1 (t.val.1 (Fin.last (m + 1))) : Fin 2 → VF M) 1) = p.2 H.leading
        rw [e1, ← ht2]
        exact hrv
    refine ⟨⟨_, hq⟩, ?_⟩
    show ((Fin.init (Fin.snoc p.1 (t.val.1 (Fin.last (m + 1))) : Fin 2 → VF M), p.2) :
      Mixed M 1 H.arity) = p
    rw [Fin.init_snoc]
    rfl

/-- The target slice is the RV-disc bundle over its contracted set. -/
theorem slice2_target_bundle :
    (slice2 H.target b hS).carrier =
      (rvCoordinateBundle (vfDropLast (slice2 H.target b hS)).image H.leading).carrier := by
  ext p
  show p ∈ (slice2 H.target b hS).carrier ↔
    (Fin.init p.1, p.2) ∈ (vfDropLast (slice2 H.target b hS)).image.carrier ∧
      rv M (p.1 (Fin.last 1)) = p.2 H.leading
  rw [mem_slice2_target, contracted_slice2]
  have h0 : Fin.init p.1 0 = p.1 0 := by
    show p.1 (Fin.castSucc 0) = p.1 0
    rw [Fin.castSucc_zero]
  show _ ↔ ((Fin.snoc b (Fin.init p.1 0), p.2) : Mixed M (m + 1) H.arity) ∈
    H.contracted.carrier ∧ rv M (p.1 (Fin.last 1)) = p.2 H.leading
  rw [h0]
  rfl

/-- The restricted stage fixes coordinate `0` of the slice. -/
theorem stageSlice2_relative (p : slice2 Y b hS) (i : Fin 1) :
    (sliceMap2 H.lift (stage_fix2 H) p).val.1 i.castSucc = p.val.1 i.castSucc := by
  rw [Subsingleton.elim i 0]
  have h := H.relative (liftElem2 p) (Fin.last m)
  show (H.lift (liftElem2 p)).val.1 (Fin.natAdd m (Fin.castSucc 0)) = p.val.1 (Fin.castSucc 0)
  rw [show Fin.natAdd m (Fin.castSucc (0 : Fin 1)) = (Fin.last m).castSucc from Fin.ext (by simp),
    h, Fin.castSucc_zero]
  simp

/-- Good points for a stage: there is a nonzero polynomial `P` such that at every point `b`
with `P(b) ≠ 0` the hypothesis of `stageSlice2` holds over every small base. -/
theorem stage_exists_good_polynomial2 (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    ∃ P : MvPolynomial (Fin m) (vfParameterField S), P ≠ 0 ∧
      ∀ (b : Fin m → VF M) {S' : Set M} (hS : S ∪ Set.range (vfValues b) ⊆ S'),
        Cardinal.mk S' < κ → P.eval₂ (vfParameterField S).subtype b ≠ 0 →
          vfDim (rawRVSpace (M := M) 1) (slice2 H.exceptional b hS) < 2 ∨
            (slice2 H.exceptional b hS).carrier = ∅ :=
  exists_good_polynomial2_or_empty hc hs hsmall H.exceptional (Or.inl H.exceptional_dim)

variable (hgood : vfDim (rawRVSpace (M := M) 1) (slice2 H.exceptional b hS) < 2 ∨
  (slice2 H.exceptional b hS).carrier = ∅)

/-- **The restriction of a stage to the two-dimensional slices.** A standard
contraction stage `H` of `Y ⊆ VF^{m+2} × RVʳ` fixes the first `m + 1` VF
coordinates. At a point `b ∈ VFᵐ` whose exceptional slice has VF dimension `< 2`
(or is empty), its restriction is a standard contraction stage of the slice `Y_b`
over `S'`, with target the slice of the target, the same arity, old labels and
leading label, and exceptional set the slice of the exceptional set. -/
def stageSlice2 : StandardContractionStage (G := G) (slice2 Y b hS) where
  arity := H.arity
  target := slice2 H.target b hS
  lift := sliceMap2 H.lift (stage_fix2 H)
  home := sliceMap2_homeomorphism (stage_fix2 H) H.home
  proper := slice2_properInvariant H.proper
  doublyBounded := slice2_vfDoublyBounded H.doublyBounded
  relative p i := stageSlice2_relative H b hS p i
  oldLabels := H.oldLabels
  oldLabels_injective := H.oldLabels_injective
  retained p i := H.retained (liftElem2 p) i
  leading := H.leading
  bundle := slice2_target_bundle H b hS
  exceptional := slice2 H.exceptional b hS
  exceptional_subset := slice2_mono H.exceptional_subset
  exceptional_dim := hgood.elim id (fun h => vfDim_lt_of_carrier_empty _ h two_pos)
  unitDerivative p hp :=
    sliceMap2_unitDerivative H.lift (stage_fix2 H) p (H.unitDerivative (liftElem2 p) hp)

theorem stageSlice2_lift : (stageSlice2 H b hS hgood).lift = sliceMap2 H.lift (stage_fix2 H) := rfl

theorem stageSlice2_target : (stageSlice2 H b hS hgood).target = slice2 H.target b hS := rfl

theorem stageSlice2_exceptional :
    (stageSlice2 H b hS hgood).exceptional = slice2 H.exceptional b hS := rfl

/-- The contracted set of the restricted stage is the one-dimensional slice of the
contracted set of `H`. -/
theorem stageSlice2_contracted :
    (stageSlice2 H b hS hgood).contracted.carrier = (sliceSet H.contracted b hS).carrier :=
  contracted_slice2 H b hS

/-- The contraction of the restricted stage: `(y, t) ↦ (y₀, v)` where `v` are the labels of
`H((b, y), t)`. -/
theorem stageSlice2_contraction_val (q : slice2 Y b hS) :
    ((stageSlice2 H b hS hgood).contraction q).val =
      ((fun _ => q.val.1 0, (H.lift (liftElem2 q)).val.2) : Mixed M 1 H.arity) := by
  rw [StandardContractionStage.contraction_value]
  refine Prod.ext (fin_one_ext ?_) rfl
  show (sliceMap2 H.lift (stage_fix2 H) q).val.1 (Fin.castSucc 0) = q.val.1 0
  rw [stageSlice2_relative, Fin.castSucc_zero]

/-- The contraction of the restricted stage is the restriction of the contraction of `H`:
`((b, x), v) = H.contraction((b, y), t)` where `(x, v)` is its value at `(y, t)`. -/
theorem stageSlice2_contraction_lift (q : slice2 Y b hS) :
    ((Fin.snoc b (((stageSlice2 H b hS hgood).contraction q).val.1 0),
        ((stageSlice2 H b hS hgood).contraction q).val.2) : Mixed M (m + 1) H.arity) =
      (H.contraction (liftElem2 q)).val := by
  rw [stageSlice2_contraction_val, StandardContractionStage.contraction_value]
  refine Prod.ext ?_ rfl
  show Fin.snoc b (q.val.1 0) = Fin.init (H.lift (liftElem2 q)).val.1
  rw [show Fin.init (H.lift (liftElem2 q)).val.1 = Fin.init (liftElem2 q).val.1 from
    funext fun i => H.relative _ i, liftElem2_val, init_snoc2]

/-- The contraction of the restricted stage lands in the one-dimensional slice of the
contracted set. -/
theorem stageSlice2_contraction_mem (q : slice2 Y b hS) :
    ((stageSlice2 H b hS hgood).contraction q).val ∈ (sliceSet H.contracted b hS).carrier := by
  rw [← stageSlice2_contracted H b hS hgood]
  exact ((stageSlice2 H b hS hgood).contraction q).property

end Stage

/-! ### Two-dimensional slice objects -/

section Objects

variable {X : DefSet (rawMixedSpace (M := M) (m + 2) r) S}

/-- The form `(y, t) ↦ ω((b, y), t)` on the slice, over `S'`. -/
def slice2Form (X : DefSet (rawMixedSpace (M := M) (m + 2) r) S)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    Map (slice2 X b hS) (DefSet.univ (rawGammaPresentation (M := M)) S') :=
  (extendMapBase (Set.subset_union_left.trans hS) ω).comp (liftElem2Map X b hS)

theorem slice2Form_apply (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S))
    {b : Fin m → VF M} {hS : S ∪ Set.range (vfValues b) ⊆ S'} (q : slice2 X b hS) :
    gammaMapValue (slice2Form X ω b hS) q =
      gammaMapValue ω ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2), q.property⟩ := rfl

/-- Form covariance of `X` (as in `VFObject.formCovariant`) gives form covariance of the
slice, with the radii of the last two coordinates. -/
theorem slice2FormCovariant_of (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hcov : ∀ t : Fin r → RVInfinity M, ∃ α : Fin (m + 2) → Gamma M, NamedRadii S t α ∧
      ∀ x y (hx : (x, t) ∈ X.carrier) (hy : (y, t) ∈ X.carrier), Congruent α x y →
        gammaMapValue ω ⟨(x, t), hx⟩ = gammaMapValue ω ⟨(y, t), hy⟩)
    (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    ∀ t : Fin r → RVInfinity M, ∃ α : Fin 2 → Gamma M, NamedRadii S' t α ∧
      ∀ x y (hx : ((Fin.snoc (Fin.snoc b (x 0)) (x 1), t) : Mixed M (m + 2) r) ∈ X.carrier)
        (hy : ((Fin.snoc (Fin.snoc b (y 0)) (y 1), t) : Mixed M (m + 2) r) ∈ X.carrier),
        Congruent α x y → gammaMapValue ω ⟨_, hx⟩ = gammaMapValue ω ⟨_, hy⟩ := by
  intro t
  obtain ⟨α, hα, h⟩ := hcov t
  exact ⟨fun i => α (Fin.natAdd m i), fun i => (hα (Fin.natAdd m i)).mono
    (Set.union_subset_union_left _ (Set.subset_union_left.trans hS)),
    fun x y hx hy hxy => h _ _ hx hy (congruent_snoc2 hxy)⟩

/-- The two-dimensional slice `(X_b, ω((b, ·), ·))` of a proper invariant measured VF
set, as an object of `μVF^◇[2]` over `S'`. It needs finite RV fibres of `X` and form
covariance on the slice (`slice2FormCovariant_of` derives the latter from form
covariance of `X`). -/
def slice2Object (X : DefSet (rawMixedSpace (M := M) (m + 2) r) S)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hX : ProperInvariant S X.carrier)
    (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S')
    (hcov : ∀ t : Fin r → RVInfinity M, ∃ α : Fin 2 → Gamma M, NamedRadii S' t α ∧
      ∀ x y (hx : ((Fin.snoc (Fin.snoc b (x 0)) (x 1), t) : Mixed M (m + 2) r) ∈ X.carrier)
        (hy : ((Fin.snoc (Fin.snoc b (y 0)) (y 1), t) : Mixed M (m + 2) r) ∈ X.carrier),
        Congruent α x y → gammaMapValue ω ⟨_, hx⟩ = gammaMapValue ω ⟨_, hy⟩)
    (hfin : ∀ x : Fin (m + 2) → VF M, {u | (x, u) ∈ X.carrier}.Finite) :
    VFObject (M := M) S' 2 where
  labels := r
  carrier := slice2 X b hS
  form := slice2Form X ω b hS
  proper := slice2_properInvariant hX
  formCovariant t := hcov t
  finiteRV x := hfin (Fin.snoc (Fin.snoc b (x 0)) (x 1))

/-- The two-dimensional slice of an object of `μVF^◇[m + 2]` over `S`, as an object of
`μVF^◇[2]` over `S'`. -/
def slice2VFObject (A : VFObject (M := M) S (m + 2)) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') : VFObject (M := M) S' 2 :=
  slice2Object A.carrier A.form A.proper b hS (slice2FormCovariant_of A.form A.formCovariant b hS)
    A.finiteRV

theorem slice2VFObject_carrier (A : VFObject (M := M) S (m + 2)) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    (slice2VFObject A b hS).carrier = slice2 A.carrier b hS := rfl

theorem slice2VFObject_form_apply (A : VFObject (M := M) S (m + 2)) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') (q : slice2 A.carrier b hS) :
    gammaMapValue (slice2VFObject A b hS).form q =
      gammaMapValue A.form ⟨(Fin.snoc (Fin.snoc b (q.val.1 0)) (q.val.1 1), q.val.2),
        q.property⟩ := rfl

theorem slice2VFObject_doublyBounded (A : VFObject (M := M) S (m + 2))
    (hA : VFDoublyBounded A.carrier.carrier) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    VFDoublyBounded (slice2VFObject A b hS).carrier.carrier :=
  slice2_vfDoublyBounded (hS := hS) hA

end Objects

end DiamondIntegral.Section7.TwoDimSlices
