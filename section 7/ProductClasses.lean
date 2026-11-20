import «section 7».BoundedClasses

/-! Products of isomorphism classes of `μRV^db[*]` (for the multiplicative part
of Lemma 7.10, `isp:congruence:vol`).

The product of bounded objects is Section 4's `RVBoundedCharts.product`: for
`a` of degree `k` and `b` of degree `l` it is `a × b`, with the coordinates of
`a` first, in degree `l + k` (Section 4's block convention for `Fin (l + k)`).
This module provides:

* degree casts along equalities `m = m'` that keep the arity, the domain and
  the volume and only reindex the structural coordinates (`castChart`,
  `castObj`, `castCls`); the class cast is additive;
* the product of classes `x * y : Cls B (l + k)` for `x : Cls B k`,
  `y : Cls B l` (`mul`, well defined by Section 4's product isomorphisms);
* distributivity over the tagged coproduct on both sides, with the zero laws
  (`cls_add_mul`, `cls_mul_add`, `cls_zero_mul`, `cls_mul_zero`, and the sums `cls_sum_mul`,
  `cls_mul_sum`);
* the unit `one = [RVBoundedRing.unit B] : Cls B 0`, with `one * x = x` (the
  degree `k + 0` is definitionally `k`) and `castCls (Nat.zero_add k) (x * one) = x`;
* commutativity up to the degree cast: `castCls (Nat.add_comm l k) (x * y) = y * x`.

Route: distributivity restricts a product to the product pieces over a definable
partition of one factor (`cls_prod_head_split`, `cls_prod_tail_split`): the
restriction of `X × c` to the points whose `X`-part lies in `I` has literally
the domain, coordinates and volume of `(X ∩ I) × c`. The tagged coproduct is
then split along its left tag. The unit and commutativity isomorphisms are
coordinate maps (`RVCoordinateMaps.coordinateIso`); the weight is multiplicative
(`RVMeasuredProductProperties.product_weight_join`). No cancellation is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.ProductClasses
open DiamondIntegral.Section4
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions FiniteTupleBlocks FiniteTupleGraphProduct
open RVRealProducts RVMeasuredProduct
open DiamondIntegral.Section7.BoundedClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}

/-! ### Degree casts -/

/-- A chart read in an equal degree: same arity, domain and volume, structural
coordinates reindexed along `Fin.cast`. -/
def castChart {m m' : ℕ} (h : m = m') (r : Chart B m) : Chart B m' where
  arity := r.arity
  domain := r.domain
  domain_definable := r.domain_definable
  coordinate := fun u => r.coordinate u ∘ Fin.cast h.symm
  coordinate_definable := by subst h; exact r.coordinate_definable
  coordinate_proper := by subst h; exact r.coordinate_proper
  finite_fibres := by subst h; exact r.finite_fibres
  volume := r.volume
  volume_definable := r.volume_definable

theorem castChart_rfl {m : ℕ} (r : Chart B m) : castChart rfl r = r := rfl

theorem castChart_weight {m m' : ℕ} (h : m = m') (r : Chart B m) (u : Fin r.arity → M) :
    (castChart h r).correctedWeight u = r.correctedWeight u := by
  subst h
  rfl

/-- A bounded object read in an equal degree. -/
def castObj {m m' : ℕ} (h : m = m') (a : Obj B m) : Obj B m' :=
  ⟨castChart h a.toChart, a.domain_bounded⟩

theorem castObj_weight {m m' : ℕ} (h : m = m') (a : Obj B m) (u : Fin a.arity → M) :
    (castObj h a).correctedWeight u = a.correctedWeight u :=
  castChart_weight h a.toChart u

/-- Classes along an equality of degrees (the same definition as
`FiberwiseInput.castCls`). -/
def castCls {m m' : ℕ} (h : m = m') (x : Cls B m) : Cls B m' := h ▸ x

theorem castCls_rfl {m : ℕ} (x : Cls B m) : castCls rfl x = x := rfl

theorem castCls_cls {m m' : ℕ} (h : m = m') (a : Obj B m) : castCls h (cls a) = cls (castObj h a) := by
  subst h
  rfl

theorem castCls_castCls {m m' m'' : ℕ} (h : m = m') (h' : m' = m'') (x : Cls B m) :
    castCls h' (castCls h x) = castCls (h.trans h') x := by
  subst h
  subst h'
  rfl

theorem castCls_symm {m m' : ℕ} (h : m = m') (x : Cls B m) : castCls h.symm (castCls h x) = x := by
  subst h
  rfl

theorem castCls_injective {m m' : ℕ} (h : m = m') : Function.Injective (castCls (B := B) h) := by
  subst h
  exact fun _ _ e => e

/-- The class cast as an additive map. -/
def castHom {m m' : ℕ} (h : m = m') : Cls B m →+ Cls B m' where
  toFun := castCls h
  map_zero' := by subst h; rfl
  map_add' x y := by subst h; rfl

theorem castHom_apply {m m' : ℕ} (h : m = m') (x : Cls B m) : castHom h x = castCls h x := rfl

theorem castCls_add {m m' : ℕ} (h : m = m') (x y : Cls B m) :
    castCls h (x + y) = castCls h x + castCls h y := (castHom h).map_add x y

theorem castCls_zero {m m' : ℕ} (h : m = m') : castCls h (0 : Cls B m) = 0 := (castHom h).map_zero

theorem castCls_sum {m m' n : ℕ} (h : m = m') (x : Fin n → Cls B m) :
    castCls h (∑ i, x i) = ∑ i, castCls h (x i) := map_sum (castHom h) x Finset.univ

/-! ### Products of objects and of classes -/

variable {k l : ℕ}

/-- The product `a × b` of bounded objects, in degree `l + k`. -/
abbrev prodObj (a : Obj B k) (b : Obj B l) : Obj B (l + k) := RVBoundedCharts.product a b

/-- The product of classes, induced by `RVBoundedCharts.product`. -/
def mul : Cls B k → Cls B l → Cls B (l + k) :=
  Quotient.map₂ prodObj (fun _ _ hF _ _ hG => by
    obtain ⟨F⟩ := hF
    obtain ⟨G⟩ := hG
    exact ⟨RVMeasuredIsomorphisms.productIso F G⟩)

instance : HMul (Cls B k) (Cls B l) (Cls B (l + k)) := ⟨mul⟩

theorem cls_mul (a : Obj B k) (b : Obj B l) : cls a * cls b = cls (prodObj a b) := rfl

theorem prod_weight_join (a : Chart B k) (b : Chart B l) (x : Fin a.arity → M) (y : Fin b.arity → M) :
    (product a b).correctedWeight (join b.arity a.arity x y) = a.correctedWeight x * b.correctedWeight y :=
  RVMeasuredProductProperties.product_weight_join a b x y

/-! ### Zero laws -/

theorem cls_mul_zero (x : Cls B k) : x * (0 : Cls B l) = 0 := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  rw [← cls_zero, cls_mul]
  apply cls_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact hu.2

theorem cls_zero_mul (y : Cls B l) : (0 : Cls B k) * y = 0 := by
  obtain ⟨b, rfl⟩ := cls_surjective y
  rw [← cls_zero, cls_mul]
  apply cls_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact hu.1

/-! ### Restricting a product to the product pieces of one factor -/

/-- The points of `X × c` whose `X`-part lies in `I`. -/
def headCut (a b : ℕ) (I : Set (Fin a → M)) : Set (Fin (b + a) → M) :=
  {w | w ∘ headIndex b a ∈ I ∧ w ∈ sortedUniverse (fun _ : Fin (b + a) => .rv)}

theorem headCut_definable (a b : ℕ) (I : Set (Fin a → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I) :
    DefinableOverBase B (fun _ : Fin (b + a) => .rv) (headCut a b I) :=
  hI.preimage_real (fun _ : Fin (b + a) => .rv) (headIndex b a)

/-- The points of `c × X` whose `X`-part lies in `I`. -/
def tailCut (a b : ℕ) (I : Set (Fin b → M)) : Set (Fin (b + a) → M) :=
  {w | w ∘ tailIndex b a ∈ I ∧ w ∈ sortedUniverse (fun _ : Fin (b + a) => .rv)}

theorem tailCut_definable (a b : ℕ) (I : Set (Fin b → M))
    (hI : DefinableOverBase B (fun _ : Fin b => .rv) I) :
    DefinableOverBase B (fun _ : Fin (b + a) => .rv) (tailCut a b I) :=
  hI.preimage_real (fun _ : Fin (b + a) => .rv) (tailIndex b a)

section Split
variable (X : Obj B k) (c : Obj B l) (I : Set (Fin X.arity → M))
  (hI : DefinableOverBase B (fun _ : Fin X.arity => .rv) I)

theorem prod_sorted {w : Fin (c.arity + X.arity) → M} (hw : w ∈ (prodObj X c).domain) :
    w ∈ sortedUniverse (fun _ : Fin (c.arity + X.arity) => .rv) :=
  (prodObj X c).domain_definable.proper w hw

theorem prod_sorted_left {w : Fin (X.arity + c.arity) → M} (hw : w ∈ (prodObj c X).domain) :
    w ∈ sortedUniverse (fun _ : Fin (X.arity + c.arity) => .rv) :=
  (prodObj c X).domain_definable.proper w hw

theorem cls_piece_headCut :
    cls (piece (prodObj X c) (headCut X.arity c.arity I) (headCut_definable X.arity c.arity I hI)) =
      cls (prodObj (piece X I hI) c) := by
  apply cls_eq_of_iso
  refine sameIso (inside (ofChart (prodObj X c).toChart) _ _) (ofChart (prodObj (piece X I hI) c).toChart)
    ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, hi, _⟩
    exact ⟨⟨hx, hi⟩, hy⟩
  · rintro ⟨⟨hx, hi⟩, hy⟩
    exact ⟨⟨hx, hy⟩, hi, prod_sorted X c ⟨hx, hy⟩⟩

theorem cls_cpiece_headCut :
    cls (cpiece (prodObj X c) (headCut X.arity c.arity I) (headCut_definable X.arity c.arity I hI)) =
      cls (prodObj (cpiece X I hI) c) := by
  apply cls_eq_of_iso
  refine sameIso (outside (ofChart (prodObj X c).toChart) _ _) (ofChart (prodObj (cpiece X I hI) c).toChart)
    ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, hn⟩
    exact ⟨⟨hx, fun hi => hn ⟨hi, prod_sorted X c ⟨hx, hy⟩⟩⟩, hy⟩
  · rintro ⟨⟨hx, hn⟩, hy⟩
    exact ⟨⟨hx, hy⟩, fun hi => hn hi.1⟩

theorem cls_piece_tailCut :
    cls (piece (prodObj c X) (tailCut c.arity X.arity I) (tailCut_definable c.arity X.arity I hI)) =
      cls (prodObj c (piece X I hI)) := by
  apply cls_eq_of_iso
  refine sameIso (inside (ofChart (prodObj c X).toChart) _ _) (ofChart (prodObj c (piece X I hI)).toChart)
    ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, hi, _⟩
    exact ⟨hx, hy, hi⟩
  · rintro ⟨hx, hy, hi⟩
    exact ⟨⟨hx, hy⟩, hi, prod_sorted_left X c ⟨hx, hy⟩⟩

theorem cls_cpiece_tailCut :
    cls (cpiece (prodObj c X) (tailCut c.arity X.arity I) (tailCut_definable c.arity X.arity I hI)) =
      cls (prodObj c (cpiece X I hI)) := by
  apply cls_eq_of_iso
  refine sameIso (outside (ofChart (prodObj c X).toChart) _ _) (ofChart (prodObj c (cpiece X I hI)).toChart)
    ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, hn⟩
    exact ⟨hx, hy, fun hi => hn ⟨hi, prod_sorted_left X c ⟨hx, hy⟩⟩⟩
  · rintro ⟨hx, hy, hn⟩
    exact ⟨⟨hx, hy⟩, fun hi => hn hi.1⟩

/-- A definable partition of the left factor splits the product. -/
theorem cls_prod_head_split :
    cls (prodObj X c) = cls (prodObj (piece X I hI) c) + cls (prodObj (cpiece X I hI) c) := by
  rw [cls_partition (prodObj X c) (headCut X.arity c.arity I) (headCut_definable X.arity c.arity I hI),
    cls_piece_headCut, cls_cpiece_headCut]

/-- A definable partition of the right factor splits the product. -/
theorem cls_prod_tail_split :
    cls (prodObj c X) = cls (prodObj c (piece X I hI)) + cls (prodObj c (cpiece X I hI)) := by
  rw [cls_partition (prodObj c X) (tailCut c.arity X.arity I) (tailCut_definable c.arity X.arity I hI),
    cls_piece_tailCut, cls_cpiece_tailCut]

end Split

/-! ### Distributivity -/

theorem cls_piece_coprod_left (a b : Obj B k) :
    cls (piece (coprod a b) (BoundedClasses.L a.toChart b.toChart).domain
      (BoundedClasses.L a.toChart b.toChart).domain_definable) = cls a :=
  cls_eq_of_iso (coprodInsideLeft a.toChart b.toChart)

theorem cls_cpiece_coprod_left (a b : Obj B k) :
    cls (cpiece (coprod a b) (BoundedClasses.L a.toChart b.toChart).domain
      (BoundedClasses.L a.toChart b.toChart).domain_definable) = cls b :=
  cls_eq_of_iso (coprodOutsideLeft a.toChart b.toChart)

/-- Products distribute over sums on the left factor. -/
theorem cls_add_mul (x y : Cls B k) (z : Cls B l) : (x + y) * z = x * z + y * z := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  obtain ⟨b, rfl⟩ := cls_surjective y
  obtain ⟨c, rfl⟩ := cls_surjective z
  rw [← cls_coprod, cls_mul, cls_mul, cls_mul,
    cls_prod_head_split (coprod a b) c _ (BoundedClasses.L a.toChart b.toChart).domain_definable]
  congr 1
  · rw [← cls_mul, cls_piece_coprod_left, cls_mul]
  · rw [← cls_mul, cls_cpiece_coprod_left, cls_mul]

/-- Products distribute over sums on the right factor. -/
theorem cls_mul_add (x : Cls B k) (y z : Cls B l) : x * (y + z) = x * y + x * z := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  obtain ⟨b, rfl⟩ := cls_surjective y
  obtain ⟨c, rfl⟩ := cls_surjective z
  rw [← cls_coprod, cls_mul, cls_mul, cls_mul,
    cls_prod_tail_split (coprod b c) a _ (BoundedClasses.L b.toChart c.toChart).domain_definable]
  congr 1
  · rw [← cls_mul, cls_piece_coprod_left, cls_mul]
  · rw [← cls_mul, cls_cpiece_coprod_left, cls_mul]

/-- Right multiplication by a class, as an additive map. -/
def mulRight (z : Cls B l) : Cls B k →+ Cls B (l + k) where
  toFun x := x * z
  map_zero' := cls_zero_mul z
  map_add' x y := cls_add_mul x y z

/-- Left multiplication by a class, as an additive map. -/
def mulLeft (x : Cls B k) : Cls B l →+ Cls B (l + k) where
  toFun y := x * y
  map_zero' := cls_mul_zero x
  map_add' y z := cls_mul_add x y z

theorem cls_sum_mul {n : ℕ} (x : Fin n → Cls B k) (z : Cls B l) : (∑ i, x i) * z = ∑ i, x i * z :=
  map_sum (mulRight z) x Finset.univ

theorem cls_mul_sum {n : ℕ} (x : Cls B k) (y : Fin n → Cls B l) : x * (∑ i, y i) = ∑ i, x * y i :=
  map_sum (mulLeft x) y Finset.univ

/-! ### The unit -/

variable (B) in
/-- The unit class `[RVBoundedRing.unit B]` of degree `0`. -/
def one : Cls B 0 := cls (RVBoundedRing.unit B)

theorem unit_correctedWeight (u : Fin (RVBoundedRing.unit B).arity → M) :
    (RVBoundedRing.unit B).correctedWeight u = 1 :=
  RVMeasuredCharts.weightedUnit_correctedWeight B 1 (GammaGroupNames.one_definable_base B) u

/-- `unit × a ≅ a`, by the identity on raw tuples (the arity `a.arity + 0` is
definitionally `a.arity`). -/
def unitProdIso (a : Chart B k) : Iso (product (RVBoundedRing.unit B).toChart a) a := by
  refine RVCoordinateMaps.coordinateIso _ _ id
    ⟨fun _ hw => hw.2, fun _ _ _ _ he => he, fun x hx => ⟨x, ⟨Set.mem_univ _, hx⟩, rfl⟩⟩ ?_
  change ∀ u : Fin a.arity → M, u ∈ productSet (Set.univ : Set (Fin 0 → M)) a.domain →
    (product (RVBoundedRing.unit B).toChart a).correctedWeight u = a.correctedWeight u
  intro w _
  have h := prod_weight_join (RVBoundedRing.unit B).toChart a Fin.elim0 w
  have hu : (RVBoundedRing.unit B).correctedWeight (Fin.elim0 : Fin (RVBoundedRing.unit B).arity → M) = 1 :=
    unit_correctedWeight _
  refine h.trans ?_
  rw [hu, one_mul]

/-- `a × unit ≅ a`, read in degree `k` along `0 + k = k`. -/
def prodUnitIso (a : Chart B k) :
    Iso (castChart (Nat.zero_add k) (product a (RVBoundedRing.unit B).toChart)) a := by
  refine RVCoordinateMaps.coordinateIso _ _ (headIndex 0 a.arity) ?_ ?_
  · change Set.BijOn (fun u : Fin (0 + a.arity) → M => u ∘ headIndex 0 a.arity)
      (productSet a.domain (Set.univ : Set (Fin 0 → M))) a.domain
    refine ⟨fun _ hw => hw.1, ?_, ?_⟩
    · intro w _ w' _ he
      exact block_ext 0 a.arity he (funext fun i => i.elim0)
    · intro x hx
      exact ⟨join 0 a.arity x Fin.elim0, (productSet_join _ _ x Fin.elim0).mpr ⟨hx, Set.mem_univ _⟩,
        funext (join_head 0 a.arity x Fin.elim0)⟩
  · change ∀ u : Fin (0 + a.arity) → M, u ∈ productSet a.domain (Set.univ : Set (Fin 0 → M)) →
      (castChart (Nat.zero_add k) (product a (RVBoundedRing.unit B).toChart)).correctedWeight u =
        a.correctedWeight (u ∘ headIndex 0 a.arity)
    intro w _
    refine (castChart_weight (Nat.zero_add k) (product a (RVBoundedRing.unit B).toChart) w).trans ?_
    have h := prod_weight_join a (RVBoundedRing.unit B).toChart (w ∘ headIndex 0 a.arity)
      (w ∘ tailIndex 0 a.arity)
    have hu : (RVBoundedRing.unit B).correctedWeight
        (w ∘ tailIndex 0 a.arity : Fin (RVBoundedRing.unit B).arity → M) = 1 := unit_correctedWeight _
    have hr : join (RVBoundedRing.unit B).arity a.arity (w ∘ headIndex 0 a.arity) (w ∘ tailIndex 0 a.arity) = w :=
      join_reconstruct 0 a.arity w
    rw [hr, hu, mul_one] at h
    exact h

/-- The unit on the left: the degree `k + 0` is definitionally `k`. -/
theorem cls_one_mul (x : Cls B k) : one B * x = x := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  exact cls_eq_of_iso (unitProdIso a.toChart)

/-- The unit on the right, up to the degree cast `0 + k = k`. -/
theorem cls_mul_one (x : Cls B k) : castCls (Nat.zero_add k) (x * one B) = x := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  rw [one, cls_mul, castCls_cls]
  exact cls_eq_of_iso (prodUnitIso a.toChart)

/-! ### Commutativity -/

omit [LRV.Structure M] hM in
theorem comp_blockSwap (n m : ℕ) (w : Fin (m + n) → M) :
    w ∘ blockSwap n m = join n m (w ∘ tailIndex m n) (w ∘ headIndex m n) := by
  conv_lhs => rw [← join_reconstruct m n w]
  exact join_blockSwap n m _ _

/-- `a × b ≅ b × a` by the block swap, read in degree `k + l`. -/
def prodCommIso (a : Chart B k) (b : Chart B l) :
    Iso (castChart (Nat.add_comm l k) (product a b)) (product b a) := by
  refine RVCoordinateMaps.coordinateIso _ _ (blockSwap a.arity b.arity) ?_ ?_
  · change Set.BijOn (fun u : Fin (b.arity + a.arity) → M => u ∘ blockSwap a.arity b.arity)
      (productSet a.domain b.domain) (productSet b.domain a.domain)
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      show w ∘ blockSwap a.arity b.arity ∈ productSet b.domain a.domain
      rw [comp_blockSwap, productSet_join]
      exact ⟨hw.2, hw.1⟩
    · intro w _ w' _ he
      exact (blockSwap a.arity b.arity).surjective.injective_comp_right he
    · intro v hv
      obtain ⟨y, hy, x, hx, rfl⟩ := (productSet_exists _ _ v).mp hv
      exact ⟨join b.arity a.arity x y, (productSet_join _ _ x y).mpr ⟨hx, hy⟩, join_blockSwap a.arity b.arity y x⟩
  · change ∀ u : Fin (b.arity + a.arity) → M, u ∈ productSet a.domain b.domain →
      (castChart (Nat.add_comm l k) (product a b)).correctedWeight u =
        (product b a).correctedWeight (u ∘ blockSwap a.arity b.arity : Fin (a.arity + b.arity) → M)
    intro w hw
    obtain ⟨x, _, y, _, rfl⟩ := (productSet_exists _ _ w).mp hw
    refine (castChart_weight (Nat.add_comm l k) (product a b) (join b.arity a.arity x y)).trans ?_
    rw [join_blockSwap, prod_weight_join, prod_weight_join, mul_comm]

/-- Commutativity of the product, up to the degree cast `l + k = k + l`. -/
theorem cls_mul_comm (x : Cls B k) (y : Cls B l) : castCls (Nat.add_comm l k) (x * y) = y * x := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  obtain ⟨b, rfl⟩ := cls_surjective y
  rw [cls_mul, cls_mul, castCls_cls]
  exact cls_eq_of_iso (prodCommIso a.toChart b.toChart)

/-- Commutativity along any degree equality. -/
theorem cls_mul_comm_cast {n : ℕ} (h : l + k = n) (h' : k + l = n) (x : Cls B k) (y : Cls B l) :
    castCls h (x * y) = castCls h' (y * x) := by
  rw [← cls_mul_comm, castCls_castCls]

end DiamondIntegral.Section7.ProductClasses
