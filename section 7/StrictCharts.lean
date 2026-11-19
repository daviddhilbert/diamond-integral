import «section 7».RVMaps
import «section 7».ElementaryBlowups
import «section 6».NonzeroBranchTags

/-! The `∞`-free form of a bounded measured RV object.

Section 4's bounded charts allow `∞` in label coordinates (it is used as a tag)
whereas the paper's doubly bounded objects (Definition 4.9) and Section 6's
lifts require nonzero RV values. Here every bounded chart `a` is replaced by an
isomorphic chart `strictChart a` without `∞`: each coordinate `u_i` becomes the
pair `(y_i, t_i)` with `y_i = u_i` and `t_i = 1` when `u_i ≠ ∞`, and `y_i = 1`,
`t_i = rv(-1)` when `u_i = ∞`. The tags are Section 6's `branchTag` values;
residue characteristic zero separates them. Both are definable over the empty
base, so no new name is introduced, and the coordinates and volumes are
transported by the inverse decoding. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.StrictCharts
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### The second tag `rv(-1)` -/

/-- The raw RV element `rv(-1)`. -/
def minusOne : M := iRv (iVFNeg (iVFOne (M := M)))

theorem minusOne_rv : iRV (minusOne (M := M)) :=
  rv_mem hM (vf_neg_mem hM (vf_one_mem hM))

theorem minusOne_ne_zero : minusOne (M := M) ≠ iRVZero := fun h =>
  RVCalc.vf_neg_one_ne_zero hM (RVCalc.vf_eq_zero_of_rv_eq_zero hM (vf_neg_mem hM (vf_one_mem hM)) h)

theorem minusOne_nonzero : NonzeroRV (minusOne (M := M)) := ⟨minusOne_rv, minusOne_ne_zero⟩

theorem one_nonzero : NonzeroRV (iRVOne : M) := ⟨rv_one_mem hM, RVCalc.rv_one_ne_zero hM⟩

theorem minusOne_ne_one (h00 : M ⊨ Axioms.ACVF00) : minusOne (M := M) ≠ iRVOne := by
  intro h
  have hb := DiamondIntegral.Section6.branchTag_injective (M := M) h00
  have he : DiamondIntegral.Section6.branchTag (M := M) true = DiamondIntegral.Section6.branchTag false := by
    apply Subtype.ext
    change minusOne (M := M) = iRv (iVFOne (M := M))
    rw [h, RVCalc.rv_one hM]
  exact Bool.true_eq_false_eq_False (hb he)

theorem minusOne_definable : DefinableClosureAtBase B .rv (minusOne (M := M)) := by
  have h1 : DefinableClosureAtBase B .vf (iVFOne (M := M)) :=
    definableClosureAtBase_function_symbol B Fn.vfOne Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  have h2 : DefinableClosureAtBase B .vf (iVFNeg (iVFOne (M := M))) :=
    definableClosureAtBase_function_symbol B Fn.vfNeg ![iVFOne (M := M)]
      (fun i => by fin_cases i; exact vf_one_mem hM) (fun i => by fin_cases i; exact h1)
  exact definableClosureAtBase_function_symbol B Fn.rvMap ![iVFNeg (iVFOne (M := M))]
    (fun i => by fin_cases i; exact vf_neg_mem hM (vf_one_mem hM)) (fun i => by fin_cases i; exact h2)

/-! ### Piecewise and constant scalar maps -/

omit [LRV.Structure M] hM in
theorem join_mem_range_blocks {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) (i : Fin (n + m)) :
    join n m u y i ∈ Set.range u ∪ Set.range y := by
  induction m with
  | zero => exact Or.inr ⟨i, rfl⟩
  | succ m ih =>
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact Or.inl ⟨0, rfl⟩
    · rcases ih (Fin.tail u) i' with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Or.inl ⟨a.succ, ha⟩
      · exact Or.inr ⟨a, ha⟩

omit [LRV.Structure M] hM in
theorem block_cases (n m : ℕ) (i : Fin (n + m)) :
    (∃ i', i = headIndex n m i') ∨ (∃ i', i = tailIndex n m i') := by
  have h := join_mem_range_blocks n m (headIndex n m) (tailIndex n m) i
  have hi : join n m (headIndex n m) (tailIndex n m) i = i :=
    congrFun (join_reconstruct n m (id : Fin (n + m) → Fin (n + m))) i
  rw [hi] at h
  rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact Or.inl ⟨a, ha.symm⟩
  · exact Or.inr ⟨a, ha.symm⟩

theorem scalarDef_const {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {c : M} (hc : DefinableClosureAtBase B .rv c) :
    ScalarDef B I (fun _ => c) := by
  have hs := tuple_singleton_definable_base B (fun _ : Fin 1 => .rv) ![c] (fun i => by fin_cases i; exact hc)
  have h := (hI.preimage_real (fun _ : Fin (1 + n) => .rv) (headIndex 1 n)).inter
    (hs.preimage_real (fun _ : Fin (1 + n) => .rv) (tailIndex 1 n))
  unfold ScalarDef
  convert h using 1
  apply Set.ext
  intro w
  constructor
  · rintro ⟨hw, he⟩
    have hsort : w ∈ sortedUniverse (fun _ : Fin (1 + n) => .rv) := by
      intro i
      rcases block_cases 1 n i with ⟨i', rfl⟩ | ⟨i', rfl⟩
      · exact hI.proper _ hw i'
      · have hwc : w (tailIndex 1 n i') = c := by
          have := congrFun he i'
          fin_cases i'
          exact this.symm
        change iRV (w (tailIndex 1 n i'))
        rw [hwc]
        exact hs.proper ![c] rfl 0
    exact ⟨⟨hw, hsort⟩, he.symm, hsort⟩
  · rintro ⟨⟨hw, _⟩, he, _⟩
    exact ⟨hw, he.symm⟩

theorem scalarDef_ite {n : ℕ} {I : Set (Fin n → M)} (P : Set (Fin n → M))
    (hP : DefinableOverBase B (fun _ : Fin n => .rv) P) {g h : (Fin n → M) → M}
    (hg : ScalarDef B I g) (hh : ScalarDef B I h) :
    ScalarDef B I (fun u => if u ∈ P then g u else h u) := by
  have h1 := BoundedClasses.graph_inter_definable I P (fun u => ![g u]) hg hP
  have h2 := DiamondIntegral.Section7.ElementaryBlowups.graph_diff_definable I P (fun u => ![h u]) hh hP
  unfold ScalarDef
  convert h1.union h2 using 1
  apply Set.ext
  intro w
  by_cases hw : w ∘ headIndex 1 n ∈ P
  · constructor
    · rintro ⟨hi, he⟩
      exact Or.inl ⟨⟨hi, hw⟩, by simpa only [if_pos hw] using he⟩
    · rintro (⟨⟨hi, _⟩, he⟩ | ⟨⟨_, hn⟩, _⟩)
      · exact ⟨hi, by simpa only [if_pos hw] using he⟩
      · exact absurd hw hn
  · constructor
    · rintro ⟨hi, he⟩
      exact Or.inr ⟨⟨hi, hw⟩, by simpa only [if_neg hw] using he⟩
    · rintro (⟨⟨_, hp⟩, _⟩ | ⟨⟨hi, _⟩, he⟩)
      · exact absurd hp hw
      · exact ⟨hi, by simpa only [if_neg hw] using he⟩

/-- The definable set where coordinate `i` equals a given definable constant. -/
def coordEq {n : ℕ} (i : Fin n) (c : M) : Set (Fin n → M) :=
  {u | u ∘ ![i] ∈ ({![c]} : Set (Fin 1 → M)) ∧ u ∈ sortedUniverse (fun _ : Fin n => .rv)}

theorem coordEq_definable {n : ℕ} (i : Fin n) {c : M} (hc : DefinableClosureAtBase B .rv c) :
    DefinableOverBase B (fun _ : Fin n => .rv) (coordEq i c) :=
  (tuple_singleton_definable_base B (fun _ : Fin 1 => .rv) ![c]
    (fun j => by fin_cases j; exact hc)).preimage_real (fun _ : Fin n => .rv) ![i]

theorem mem_coordEq {n : ℕ} {i : Fin n} {c : M} {u : Fin n → M}
    (hu : u ∈ sortedUniverse (fun _ : Fin n => .rv)) : u ∈ coordEq i c ↔ u i = c := by
  constructor
  · rintro ⟨he, _⟩
    exact congrFun he 0
  · intro he
    refine ⟨?_, hu⟩
    funext j
    fin_cases j
    exact he

theorem codeValue_rvOne_strict : codeValue (iRVOne : M) = 1 := by
  have h := GammaGroupNames.codeValue_mul (iRVOne : M) iRVOne one_nonzero one_nonzero
  rw [rv_mul_one_any hM one_nonzero.1] at h
  have h' : codeValue (iRVOne : M) * 1 = codeValue (iRVOne : M) * codeValue (iRVOne : M) := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel h').symm

omit [LRV.Structure M] hM in
theorem eq_one_of_mul_self {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a : G}
    (h : a * a = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with hl | he | hg
  · exact absurd h (ne_of_lt (mul_lt_one' hl hl))
  · exact he
  · exact absurd h (ne_of_gt (one_lt_mul' hg hg))

theorem codeValue_minusOne : codeValue (minusOne (M := M)) = 1 := by
  have hsq : iRVMul (minusOne (M := M)) minusOne = iRVOne := by
    unfold minusOne
    rw [← rv_mul_hom_of_model hM (vf_neg_mem hM (vf_one_mem hM)) (vf_neg_mem hM (vf_one_mem hM)),
      RVCalc.vf_neg_one_mul_neg_one hM, RVCalc.rv_one hM]
  have h := GammaGroupNames.codeValue_mul _ _ (minusOne_nonzero (M := M)) minusOne_nonzero
  rw [hsq, codeValue_rvOne_strict] at h
  exact eq_one_of_mul_self h.symm

/-! ### Encoding and decoding -/

/-- The value part: `x`, or `1` at `∞`. -/
def yv (x : M) : M := if x = iRVZero then iRVOne else x

/-- The tag part: `1`, or `rv(-1)` at `∞`. -/
def tv (x : M) : M := if x = iRVZero then minusOne else iRVOne

/-- Decoding a value and a tag. -/
def dec (y t : M) : M := if t = minusOne then iRVZero else y

theorem dec_enc (h00 : M ⊨ Axioms.ACVF00) (x : M) : dec (yv x) (tv x) = x := by
  by_cases hx : x = iRVZero
  · simp [dec, tv, hx]
  · have ht : tv x = iRVOne := by simp [tv, hx]
    have hy : yv x = x := by simp [yv, hx]
    rw [dec, ht, hy, if_neg (Ne.symm (minusOne_ne_one h00))]

theorem yv_nonzero {x : M} (hx : iRV x) : NonzeroRV (yv x) := by
  by_cases h : x = iRVZero
  · simp only [yv, if_pos h]
    exact one_nonzero
  · simp only [yv, if_neg h]
    exact ⟨hx, h⟩

theorem tv_nonzero (x : M) : NonzeroRV (tv x) := by
  by_cases h : x = iRVZero
  · simp only [tv, if_pos h]
    exact minusOne_nonzero
  · simp only [tv, if_neg h]
    exact one_nonzero

/-- The encoding `u ↦ (y(u), t(u))`. -/
def encode {n : ℕ} (u : Fin n → M) : Fin (n + n) → M :=
  join n n (fun i => yv (u i)) (fun i => tv (u i))

/-- The decoding. -/
def decode {n : ℕ} (z : Fin (n + n) → M) : Fin n → M :=
  fun i => dec (z (headIndex n n i)) (z (tailIndex n n i))

theorem decode_encode (h00 : M ⊨ Axioms.ACVF00) {n : ℕ} (u : Fin n → M) : decode (encode u) = u := by
  funext i
  simp only [decode, encode, join_head, join_tail]
  exact dec_enc h00 (u i)

theorem encode_injective (h00 : M ⊨ Axioms.ACVF00) {n : ℕ} : Function.Injective (encode (M := M) (n := n)) :=
  fun u v h => by rw [← decode_encode h00 u, h, decode_encode h00 v]

theorem encode_nonzero {n : ℕ} {u : Fin n → M} (hu : u ∈ sortedUniverse (fun _ : Fin n => .rv))
    (i : Fin (n + n)) : NonzeroRV (encode u i) := by
  rcases block_cases n n i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · rw [encode, join_head]
    exact yv_nonzero (hu i')
  · rw [encode, join_tail]
    exact tv_nonzero _

omit hM in
theorem graphOn_congr {m n : ℕ} {I : Set (Fin m → M)} {F G : (Fin m → M) → (Fin n → M)}
    (h : ∀ u ∈ I, F u = G u) : graphOn I F = graphOn I G := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨hw, he⟩
    exact ⟨hw, (h _ hw).symm.trans he⟩
  · rintro ⟨hw, he⟩
    exact ⟨hw, (h _ hw).trans he⟩

theorem scalarDef_congr {n : ℕ} {I : Set (Fin n → M)} {g g' : (Fin n → M) → M}
    (hg : ScalarDef B I g) (h : ∀ u ∈ I, g u = g' u) : ScalarDef B I g' := by
  unfold ScalarDef at *
  rwa [graphOn_congr (G := fun u => ![g' u]) (fun u hu => by rw [h u hu])] at hg

theorem scalarDef_yv {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (i : Fin n) :
    ScalarDef B I (fun u => yv (u i)) := by
  refine scalarDef_congr (scalarDef_ite (coordEq i iRVZero) (coordEq_definable i (RVNamedTuples.zero_definable B))
    (scalarDef_const hI (RVNamedTuples.one_definable B)) (scalarDef_coord hI i)) (fun u hu => ?_)
  simp only [yv, mem_coordEq (hI.proper u hu)]

theorem scalarDef_tv {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (i : Fin n) :
    ScalarDef B I (fun u => tv (u i)) := by
  refine scalarDef_congr (scalarDef_ite (coordEq i iRVZero) (coordEq_definable i (RVNamedTuples.zero_definable B))
    (scalarDef_const hI minusOne_definable) (scalarDef_const hI (RVNamedTuples.one_definable B))) (fun u hu => ?_)
  simp only [tv, mem_coordEq (hI.proper u hu)]

theorem encode_tupleDef {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) : TupleDef B I (encode (n := n)) := by
  apply tupleDef_of_scalar hI
  intro i
  rcases block_cases n n i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · simpa only [encode, join_head] using scalarDef_yv hI i'
  · simpa only [encode, join_tail] using scalarDef_tv hI i'

theorem decode_tupleDef {n : ℕ} {J : Set (Fin (n + n) → M)}
    (hJ : DefinableOverBase B (fun _ : Fin (n + n) => .rv) J) : TupleDef B J (decode (n := n)) := by
  apply tupleDef_of_scalar hJ
  intro i
  refine scalarDef_congr (scalarDef_ite (coordEq (tailIndex n n i) minusOne)
    (coordEq_definable _ minusOne_definable) (scalarDef_const hJ (RVNamedTuples.zero_definable B))
    (scalarDef_coord hJ (headIndex n n i))) (fun z hz => ?_)
  simp only [decode, dec, mem_coordEq (hJ.proper z hz)]

/-! ### The strict chart -/

theorem scalarDef_comp_component {n m : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {G : (Fin n → M) → (Fin m → M)}
    (hG : TupleDef B I G) (i : Fin m) : ScalarDef B I (fun u => G u i) := by
  have hJ : DefinableOverBase B (fun _ : Fin m => .rv) (G '' I) :=
    BoundedClasses.graph_image_definable I G hG
  exact scalarDef_comp (g := fun v => v i) hG (scalarDef_coord hJ i) (fun u hu => ⟨u, hu, rfl⟩)

section Strict
variable (h00 : M ⊨ Axioms.ACVF00)

theorem encode_image_definable (a : Chart B k) :
    DefinableOverBase B (fun _ : Fin (a.arity + a.arity) => .rv) (encode '' a.domain) :=
  BoundedClasses.graph_image_definable a.domain encode (encode_tupleDef a.domain_definable)

include h00 in
theorem decode_mem {a : Chart B k} {z : Fin (a.arity + a.arity) → M} (hz : z ∈ encode '' a.domain) :
    decode z ∈ a.domain := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [decode_encode h00]
  exact hu

include h00 in
/-- The `∞`-free chart isomorphic to `a`. -/
def strictChart (a : Chart B k) : Chart B k where
  arity := a.arity + a.arity
  domain := encode '' a.domain
  domain_definable := encode_image_definable a
  coordinate := fun z => a.coordinate (decode z)
  coordinate_definable := tupleDef_comp (G := a.coordinate)
    (decode_tupleDef (encode_image_definable a)) a.coordinate_definable (fun _ hz => decode_mem h00 hz)
  coordinate_proper := fun z hz => a.coordinate_proper _ (decode_mem h00 hz)
  finite_fibres := fun t => by
    apply ((a.finite_fibres t).image encode).subset
    rintro z ⟨⟨u, hu, rfl⟩, he⟩
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    rwa [decode_encode h00] at he
  volume := fun z => a.volume (decode z)
  volume_definable := by
    let W0 : Set (Fin (a.arity + a.arity + 1) → M) :=
      {w | w ∘ Fin.succ ∈ encode '' a.domain ∧ w ∈ sortedUniverse (fun _ => .rv)}
    have hW0 : DefinableOverBase B (fun _ : Fin (a.arity + a.arity + 1) => .rv) W0 :=
      (encode_image_definable a).preimage_real _ Fin.succ
    let Ψ : (Fin (a.arity + a.arity + 1) → M) → (Fin (a.arity + 1) → M) :=
      fun w => Fin.cons (w 0) (decode (Fin.tail w))
    have hΨ : TupleDef B W0 Ψ := by
      apply tupleDef_of_scalar hW0
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa only [Ψ, Fin.cons_zero] using scalarDef_coord hW0 0
      · have hd := scalarDef_comp_component hW0 (tupleDef_comp (G := decode)
          (tupleDef_coord hW0 Fin.succ) (decode_tupleDef (encode_image_definable a)) (fun w hw => hw.1)) i
        simp only [Ψ, Fin.cons_succ]
        exact hd
    have h := RVStrictBoundedComparison.preimage_definable B W0 Ψ hΨ _ a.volume_definable
    convert h using 1
    apply Set.ext
    intro w
    constructor
    · rintro ⟨hw, h0, he⟩
      have hsort : w ∈ sortedUniverse (fun _ : Fin (a.arity + a.arity + 1) => .rv) := by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · exact h0.1
        · exact (encode_image_definable a).proper _ hw i
      refine ⟨⟨hw, hsort⟩, ?_, ?_, ?_⟩
      · change Fin.tail (Ψ w) ∈ a.domain
        simpa only [Ψ, Fin.tail_cons] using decode_mem h00 hw
      · simpa only [Ψ, Fin.cons_zero] using h0
      · simpa only [Ψ, Fin.cons_zero, Fin.tail_cons] using he
    · rintro ⟨⟨hw, _⟩, _, h0, he⟩
      refine ⟨hw, ?_, ?_⟩
      · simpa only [Ψ, Fin.cons_zero] using h0
      · simpa only [Ψ, Fin.cons_zero, Fin.tail_cons] using he

theorem strictChart_infinityFree (a : Chart B k) :
    ∀ z ∈ (strictChart h00 a).domain, ∀ i, NonzeroRV (z i) := by
  rintro z ⟨u, hu, rfl⟩ i
  exact encode_nonzero (a.domain_definable.proper u hu) i

theorem strictChart_bounded (a : Chart B k) (ha : RVMeasuredBounds.DomainBounded a) :
    RVMeasuredBounds.DomainBounded (strictChart h00 a) := by
  obtain ⟨β, hβ⟩ := ha
  have hβ1 : (1 : Values.Gamma (M := M)) ≤ max β 1 := le_max_right _ _
  refine ⟨max β 1, ?_⟩
  rintro z ⟨u, hu, rfl⟩ i _
  have hone : (max β 1)⁻¹ ≤ 1 := inv_le_one'.mpr hβ1
  rcases block_cases a.arity a.arity i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · rw [encode, join_head]
    by_cases h : u i' = iRVZero
    · simp only [yv, if_pos h, codeValue_rvOne_strict]
      exact ⟨hone, hβ1⟩
    · simp only [yv, if_neg h]
      have hb := hβ u hu i' ⟨a.domain_definable.proper u hu i', h⟩
      exact ⟨(inv_le_inv_iff.mpr (le_max_left _ _)).trans hb.1, hb.2.trans (le_max_left _ _)⟩
  · rw [encode, join_tail]
    have hc : codeValue (tv (u i')) = 1 := by
      by_cases h : u i' = iRVZero
      · simp only [tv, if_pos h, codeValue_minusOne]
      · simp only [tv, if_neg h, codeValue_rvOne_strict]
    rw [hc]
    exact ⟨hone, hβ1⟩

/-- Every chart is isomorphic to its strict form. -/
def strictIso (a : Chart B k) : Iso a (strictChart h00 a) :=
  isoOfMap a (strictChart h00 a) encode (encode_tupleDef a.domain_definable)
    ⟨fun u hu => ⟨u, hu, rfl⟩, (encode_injective h00).injOn, fun _ hz => hz⟩
    (fun u _ => by
      change a.volume u * ∏ i, codeValue (a.coordinate u i) =
        a.volume (decode (encode u)) * ∏ i, codeValue (a.coordinate (decode (encode u)) i)
      rw [decode_encode h00])

/-- The strict form of a bounded object. -/
def strictObj (a : Obj B k) : Obj B k :=
  ⟨strictChart h00 a.toChart, strictChart_bounded h00 a.toChart a.domain_bounded⟩

theorem cls_strictObj (a : Obj B k) : cls (strictObj h00 a) = cls a :=
  (cls_eq_of_iso (strictIso h00 a.toChart)).symm

end Strict

end DiamondIntegral.Section7.StrictCharts
