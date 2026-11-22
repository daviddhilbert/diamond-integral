import «section 8».MilnorFiber
import Section3.MixedPolynomialSupport
import Section3.PolynomialRVMonomial
import Section3.SortedTuples
import Section3.QuantifierFree

/-! The type argument of Remark 8.15 (`rem-comp-milnor-fib-bis`).

Let `E` be a subfield of the field sort all of whose nonzero elements have value `0` (the image of
`ℂ`), and let `t, t'` be elements of positive value with `rv(t) = rv(t')`. Then `t` and `t'` have the
same type over `E ∪ RV`: for every set `U` definable with parameters whose field-sort members lie in
`E`, and every tuple `u` of the RV sort, `(t, u) ∈ U ↔ (t', u) ∈ U` (`same_type`, `same_type_sum`).

Proof, as in the manuscript: by quantifier elimination (`DefinableOver.quantifier_free`) and the
support lemma `MixedPolynomialSupport.formula_iff_of_support`, membership depends only on `u` and on
`rv(Q(t))` for finitely many `Q ∈ E[x]`; and `rv(Q(t)) = rv(Q(t'))` (`rv_poly_eq`): write
`Q = x^j Q₀` with `Q₀(0) ≠ 0`; then `rv(Q₀(t)) = rv(Q₀(0))` and `rv(t^j) = rv(t'^j)`.

Also here: moving one parameter out of the parameter set (`definable_extract_param`), the
definability of the set of parameters over which a definable family of relations is the graph of a
bijection between two definable families (`bijGraph_definable`), and the definability of a set
definable over a base without `Γ`-names (`gammaGround_empty_definable`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2 DiamondIntegral.Section6

namespace DiamondIntegral.Section8.SameType

/-! ### Moving a parameter into a variable -/

section Params

variable {L : Language} {M : Type*} [L.Structure M]

/-- A set definable over `A ⊆ B ∪ {t}` is the fibre at `t` of a set definable over `B`. -/
theorem definable_extract_param {α : Type*} {A B : Set M} {t : M} (hA : A ⊆ insert t B)
    {s : Set (α → M)} (hs : A.Definable L s) :
    ∃ S : Set ((Unit ⊕ α) → M), B.Definable L S ∧
      ∀ v : α → M, v ∈ s ↔ Sum.elim (fun _ => t) v ∈ S := by
  classical
  rw [Set.definable_iff_exists_formula_sum] at hs
  obtain ⟨φ, rfl⟩ := hs
  let g : A ⊕ α → B ⊕ (Unit ⊕ α) := Sum.elim
    (fun a => if h : (a : M) ∈ B then Sum.inl ⟨a, h⟩ else Sum.inr (Sum.inl ()))
    (fun i => Sum.inr (Sum.inr i))
  refine ⟨{w | (φ.relabel g).Realize (Sum.elim ((↑) : B → M) w)},
    Set.definable_iff_exists_formula_sum.2 ⟨_, rfl⟩, fun v => ?_⟩
  simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
  apply iff_of_eq
  congr 1
  funext x
  rcases x with ⟨a, ha⟩ | i
  · simp only [Function.comp_apply, g, Sum.elim_inl]
    split_ifs with h
    · rfl
    · rcases hA ha with h' | h'
      · simp [h']
      · exact absurd h' h
  · rfl

/-- Equality of two coordinates is definable. -/
theorem definable_coord_eq (A : Set M) {α : Type*} (i j : α) :
    A.Definable L {w : α → M | w i = w j} :=
  ⟨(Term.var i).equal (Term.var j), by ext w; simp⟩

theorem definable_imp {A : Set M} {α : Type*} {s t : Set (α → M)} (hs : A.Definable L s)
    (ht : A.Definable L t) : A.Definable L {w | w ∈ s → w ∈ t} := by
  convert hs.compl.union ht using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
  tauto

end Params

/-! ### Families of bijections -/

section Graph

variable {L : Language} {M : Type*} [L.Structure M] {A : Set M}

/-- `G` is the graph of a bijection from `X` onto `Y`. -/
def BijGraph {α β : Type*} (X : Set (α → M)) (Y : Set (β → M)) (G : Set (α ⊕ β → M)) : Prop :=
  (∀ u : α ⊕ β → M, u ∈ G → u ∘ Sum.inl ∈ X ∧ u ∘ Sum.inr ∈ Y) ∧
  (∀ x ∈ X, ∃ z : β → M, Sum.elim x z ∈ G) ∧
  (∀ u : α ⊕ (β ⊕ β) → M, Sum.elim (u ∘ Sum.inl) ((u ∘ Sum.inr) ∘ Sum.inl) ∈ G →
    Sum.elim (u ∘ Sum.inl) ((u ∘ Sum.inr) ∘ Sum.inr) ∈ G →
      (u ∘ Sum.inr) ∘ Sum.inl = (u ∘ Sum.inr) ∘ Sum.inr) ∧
  (∀ z ∈ Y, ∃ x : α → M, Sum.elim x z ∈ G) ∧
  (∀ u : (α ⊕ α) ⊕ β → M, Sum.elim ((u ∘ Sum.inl) ∘ Sum.inl) (u ∘ Sum.inr) ∈ G →
    Sum.elim ((u ∘ Sum.inl) ∘ Sum.inr) (u ∘ Sum.inr) ∈ G →
      (u ∘ Sum.inl) ∘ Sum.inl = (u ∘ Sum.inl) ∘ Sum.inr)

/-- The fibre of a set at `y`. -/
def fibre {γ δ : Type*} (S : Set (γ ⊕ δ → M)) (y : γ → M) : Set (δ → M) := {x | Sum.elim y x ∈ S}

theorem bijGraph_iff {α β : Type*} {X : Set (α → M)} {Y : Set (β → M)} {G : Set (α ⊕ β → M)} :
    BijGraph X Y G ↔ (∀ x z, Sum.elim x z ∈ G → x ∈ X ∧ z ∈ Y) ∧ (∀ x ∈ X, ∃ z, Sum.elim x z ∈ G) ∧
      (∀ x z z', Sum.elim x z ∈ G → Sum.elim x z' ∈ G → z = z') ∧
      (∀ z ∈ Y, ∃ x, Sum.elim x z ∈ G) ∧
      (∀ x x' z, Sum.elim x z ∈ G → Sum.elim x' z ∈ G → x = x') := by
  unfold BijGraph
  refine and_congr ⟨fun h x z hG => by simpa using h (Sum.elim x z) hG, fun h u hG => ?_⟩
    (and_congr Iff.rfl (and_congr ⟨fun h x z z' h1 h2 => ?_, fun h u h1 h2 => h _ _ _ h1 h2⟩
      (and_congr Iff.rfl ⟨fun h x x' z h1 h2 => ?_, fun h u h1 h2 => h _ _ _ h1 h2⟩)))
  · rw [← Sum.elim_comp_inl_inr u] at hG
    exact h _ _ hG
  · simpa using h (Sum.elim x (Sum.elim z z')) (by simpa using h1) (by simpa using h2)
  · simpa using h (Sum.elim (Sum.elim x x') z) (by simpa using h1) (by simpa using h2)

/-- The parameters over which a definable family of relations is the graph of a bijection between
two definable families form a definable set. -/
theorem bijGraph_definable {γ α β : Type*} [Finite α] [Finite β] {SX : Set (γ ⊕ α → M)}
    {SY : Set (γ ⊕ β → M)} {SG : Set (γ ⊕ (α ⊕ β) → M)} (hX : A.Definable L SX)
    (hY : A.Definable L SY) (hG : A.Definable L SG) :
    A.Definable L {y : γ → M | BijGraph (fibre SX y) (fibre SY y) (fibre SG y)} := by
  -- (1) `G ⊆ X × Y`
  have h1 : A.Definable L {y : γ → M | ∀ u : α ⊕ β → M, Sum.elim y u ∈ SG →
      Sum.elim y (u ∘ Sum.inl) ∈ SX ∧ Sum.elim y (u ∘ Sum.inr) ∈ SY} := by
    have hX' := hX.preimage_comp (Sum.map id Sum.inl : γ ⊕ α → γ ⊕ (α ⊕ β))
    have hY' := hY.preimage_comp (Sum.map id Sum.inr : γ ⊕ β → γ ⊕ (α ⊕ β))
    convert (definable_imp hG (hX'.inter hY')).forall_of_finite using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Sum.elim_comp_map,
      Function.comp_id]
  -- (2) totality
  have h2 : A.Definable L {y : γ → M | ∀ x : α → M, Sum.elim y x ∈ SX →
      ∃ z : β → M, Sum.elim y (Sum.elim x z) ∈ SG} := by
    have hG' := hG.preimage_comp (Equiv.sumAssoc γ α β).symm
    convert (definable_imp hX hG'.exists_of_finite).forall_of_finite using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    refine forall_congr' fun x => imp_congr Iff.rfl (exists_congr fun z => ?_)
    apply iff_of_eq
    congr 1
    funext k
    rcases k with c | a | b <;> rfl
  -- (3) functionality
  have h3 : A.Definable L {y : γ → M | ∀ u : α ⊕ (β ⊕ β) → M,
      Sum.elim y (Sum.elim (u ∘ Sum.inl) ((u ∘ Sum.inr) ∘ Sum.inl)) ∈ SG →
      Sum.elim y (Sum.elim (u ∘ Sum.inl) ((u ∘ Sum.inr) ∘ Sum.inr)) ∈ SG →
        (u ∘ Sum.inr) ∘ Sum.inl = (u ∘ Sum.inr) ∘ Sum.inr} := by
    have hA1 := hG.preimage_comp (Sum.map id (Sum.map id Sum.inl) : γ ⊕ (α ⊕ β) → γ ⊕ (α ⊕ (β ⊕ β)))
    have hA2 := hG.preimage_comp (Sum.map id (Sum.map id Sum.inr) : γ ⊕ (α ⊕ β) → γ ⊕ (α ⊕ (β ⊕ β)))
    have hE : A.Definable L {w : γ ⊕ (α ⊕ (β ⊕ β)) → M |
        ∀ b : β, w (Sum.inr (Sum.inr (Sum.inl b))) = w (Sum.inr (Sum.inr (Sum.inr b)))} := by
      convert Set.definable_iInter_of_finite (fun b : β => definable_coord_eq A
        (L := L) (M := M) (Sum.inr (Sum.inr (Sum.inl b)) : γ ⊕ (α ⊕ (β ⊕ β)))
        (Sum.inr (Sum.inr (Sum.inr b)))) using 1
      ext w
      simp
    convert (definable_imp hA1 (definable_imp hA2 hE)).forall_of_finite using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    refine forall_congr' fun u => ?_
    have e1 : Sum.elim y u ∘ Sum.map id (Sum.map id Sum.inl) =
        Sum.elim y (Sum.elim (u ∘ Sum.inl) ((u ∘ Sum.inr) ∘ Sum.inl)) := by
      funext k; rcases k with c | a | b <;> rfl
    have e2 : Sum.elim y u ∘ Sum.map id (Sum.map id Sum.inr) =
        Sum.elim y (Sum.elim (u ∘ Sum.inl) ((u ∘ Sum.inr) ∘ Sum.inr)) := by
      funext k; rcases k with c | a | b <;> rfl
    rw [e1, e2, funext_iff]
    rfl
  -- (4) surjectivity
  have h4 : A.Definable L {y : γ → M | ∀ z : β → M, Sum.elim y z ∈ SY →
      ∃ x : α → M, Sum.elim y (Sum.elim x z) ∈ SG} := by
    let f : γ ⊕ (α ⊕ β) → (γ ⊕ β) ⊕ α :=
      Sum.elim (fun c => Sum.inl (Sum.inl c)) (Sum.elim Sum.inr (fun b => Sum.inl (Sum.inr b)))
    have hG' := hG.preimage_comp f
    convert (definable_imp hY hG'.exists_of_finite).forall_of_finite using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    refine forall_congr' fun z => imp_congr Iff.rfl (exists_congr fun x => ?_)
    apply iff_of_eq
    congr 1
    funext k
    rcases k with c | a | b <;> rfl
  -- (5) injectivity
  have h5 : A.Definable L {y : γ → M | ∀ u : (α ⊕ α) ⊕ β → M,
      Sum.elim y (Sum.elim ((u ∘ Sum.inl) ∘ Sum.inl) (u ∘ Sum.inr)) ∈ SG →
      Sum.elim y (Sum.elim ((u ∘ Sum.inl) ∘ Sum.inr) (u ∘ Sum.inr)) ∈ SG →
        (u ∘ Sum.inl) ∘ Sum.inl = (u ∘ Sum.inl) ∘ Sum.inr} := by
    have hA1 := hG.preimage_comp (Sum.map id (Sum.map Sum.inl id) :
      γ ⊕ (α ⊕ β) → γ ⊕ ((α ⊕ α) ⊕ β))
    have hA2 := hG.preimage_comp (Sum.map id (Sum.map Sum.inr id) :
      γ ⊕ (α ⊕ β) → γ ⊕ ((α ⊕ α) ⊕ β))
    have hE : A.Definable L {w : γ ⊕ ((α ⊕ α) ⊕ β) → M |
        ∀ a : α, w (Sum.inr (Sum.inl (Sum.inl a))) = w (Sum.inr (Sum.inl (Sum.inr a)))} := by
      convert Set.definable_iInter_of_finite (fun a : α => definable_coord_eq A
        (L := L) (M := M) (Sum.inr (Sum.inl (Sum.inl a)) : γ ⊕ ((α ⊕ α) ⊕ β))
        (Sum.inr (Sum.inl (Sum.inr a)))) using 1
      ext w
      simp
    convert (definable_imp hA1 (definable_imp hA2 hE)).forall_of_finite using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    refine forall_congr' fun u => ?_
    have e1 : Sum.elim y u ∘ Sum.map id (Sum.map Sum.inl id) =
        Sum.elim y (Sum.elim ((u ∘ Sum.inl) ∘ Sum.inl) (u ∘ Sum.inr)) := by
      funext k; rcases k with c | a | b <;> rfl
    have e2 : Sum.elim y u ∘ Sum.map id (Sum.map Sum.inr id) =
        Sum.elim y (Sum.elim ((u ∘ Sum.inl) ∘ Sum.inr) (u ∘ Sum.inr)) := by
      funext k; rcases k with c | a | b <;> rfl
    rw [e1, e2, funext_iff]
    rfl
  convert h1.inter (h2.inter (h3.inter (h4.inter h5))) using 1
  ext y
  simp only [BijGraph, fibre, Set.mem_ofPred_eq, Set.mem_inter_iff]

end Graph

/-! ### `rv` of a polynomial with constant coefficients -/

section Poly

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (E : Subfield (VFType (M := M)))
  (hE : ∀ e ∈ E, e ≠ 0 → Values.vfValueHom e = 1)

theorem value_add_ge' {γ : Values.GammaTop (M := M)} {a b : VFType (M := M)}
    (ha : γ ≤ Values.vfValueHom a) (hb : γ ≤ Values.vfValueHom b) : γ ≤ Values.vfValueHom (a + b) := by
  have h := SpecialTransformations.Section9.vfValue_min_le_sub a (-b)
  rw [sub_neg_eq_add, SpecialTransformations.Section9.vfValue_neg] at h
  exact (le_min ha hb).trans h

include hE in
/-- A polynomial over `E` maps `𝒪` to `𝒪`. -/
theorem integral_eval (r : Polynomial E) {x : VFType (M := M)} (hx : 1 ≤ Values.vfValueHom x) :
    1 ≤ Values.vfValueHom (r.eval₂ E.subtype x) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add]
    exact value_add_ge' hp hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, map_mul, map_pow]
    refine one_le_mul ?_ (one_le_pow_of_one_le' hx n)
    by_cases ha : a = 0
    · subst ha
      rw [map_zero, map_zero, ← Values.infinity_eq_zero]
      exact Values.le_infinity _
    · exact (hE _ a.property (fun h => ha (Subtype.ext h))).symm.le

include hE in
theorem rv_const_add {c x : VFType (M := M)} (hc : c ∈ E) (hc0 : c ≠ 0) (r : Polynomial E)
    (hx : 1 < Values.vfValueHom x) : rv M (c + x * r.eval₂ E.subtype x) = rv M c := by
  apply rv_eq_of_value_close hc0
  change Values.vfValueHom c < Values.vfValueHom _
  rw [hE c hc hc0, add_sub_cancel_left, map_mul]
  exact hx.trans_le (le_mul_of_one_le_right' (integral_eval E hE r hx.le))

include hE in
/-- **`rv(Q(t)) = rv(Q(t'))`** for `Q ∈ E[x]`, `v(t) > 0` and `rv(t) = rv(t')`. -/
theorem rv_poly_eq (q : Polynomial E) {t t' : VFType (M := M)} (ht : 1 < Values.vfValueHom t)
    (h : rv M t = rv M t') : rv M (q.eval₂ E.subtype t) = rv M (q.eval₂ E.subtype t') := by
  by_cases hq : q = 0
  · subst hq
    simp
  obtain ⟨j, q₀, rfl, hq0⟩ := factor_X_nonzero_constant q hq
  set c : E := q₀.coeff 0 with hcdef
  have hc0 : (c : VFType (M := M)) ≠ 0 := by
    intro h0
    apply hq0
    rw [← Polynomial.coeff_zero_eq_eval_zero, ← hcdef]
    exact Subtype.ext h0
  obtain ⟨r, hr⟩ : Polynomial.X ∣ q₀ - Polynomial.C c := by
    rw [Polynomial.X_dvd_iff]
    simp [hcdef]
  have hq₀ : ∀ x : VFType (M := M), q₀.eval₂ E.subtype x = (c : VFType (M := M)) + x * r.eval₂ E.subtype x := by
    intro x
    have he : q₀ = Polynomial.C c + Polynomial.X * r := by rw [← hr]; ring
    rw [he, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X]
    rfl
  have ht' : 1 < Values.vfValueHom t' := by
    have hv : Values.vfValueHom t = Values.vfValueHom t' := congrArg Values.vrv h
    rwa [← hv]
  have key : rv M (q₀.eval₂ E.subtype t) = rv M (q₀.eval₂ E.subtype t') := by
    rw [hq₀, hq₀, rv_const_add E hE c.property hc0 r ht, rv_const_add E hE c.property hc0 r ht']
  have hpow : ∀ n : ℕ, rv M (t ^ n) = rv M (t' ^ n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, pow_succ, rv_multiply_same_leading_term _ _ _ h, mul_comm (t ^ n),
        mul_comm (t' ^ n), rv_multiply_same_leading_term _ _ _ ih]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_X_pow,
    rv_multiply_same_leading_term _ _ _ key, mul_comm (t ^ j), mul_comm (t' ^ j),
    rv_multiply_same_leading_term _ _ _ (hpow j)]

end Poly

/-! ### Same type over `E ∪ RV` -/

section Types

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (E : Subfield (VFType (M := M)))
  (hE : ∀ e ∈ E, e ≠ 0 → Values.vfValueHom e = 1)
variable (hc : CanonicalStructure.IsCanonical (M := M))

omit hM in
theorem sorted_definable (A : Set M) {n : ℕ} (sn : Fin n → SortTag) :
    A.Definable LRV {z : Fin n → M | ∀ i, sortEval (sn i) (z i)} := by
  have h : ∀ i, A.Definable LRV {z : Fin n → M | sortEval (sn i) (z i)} := by
    intro i
    refine Set.Definable.mono ?_ (Set.empty_subset A)
    rw [Set.empty_definable_iff]
    cases hs : sn i with
    | vf => exact ⟨Relations.formula₁ Rel.memVF (Term.var i), by ext z; simp [sortEval]⟩
    | rv => exact ⟨Relations.formula₁ Rel.memRV (Term.var i), by ext z; simp [sortEval]⟩
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp

include hE hc in
/-- **Same type over `E ∪ RV`.** If `v(t) > 0` and `rv(t) = rv(t')`, then for every set `U`
definable over parameters whose field-sort members lie in `E`, and every RV tuple `ys`,
`(t, ys) ∈ U ↔ (t', ys) ∈ U`. -/
theorem same_type {C : Set M} (hC : ∀ c ∈ C, ∀ h : iVF c, (⟨c, h⟩ : VFType (M := M)) ∈ E)
    {m : ℕ} (U : Set (Fin (m + 1) → M)) (hU : C.Definable LRV U)
    {t t' : VFType (M := M)} (ht : 1 < Values.vfValueHom t) (h : rv M t = rv M t')
    (ys : Fin m → M) (hys : ∀ j, iRV (ys j)) :
    (Fin.cons t.val ys : Fin (m + 1) → M) ∈ U ↔ (Fin.cons t'.val ys : Fin (m + 1) → M) ∈ U := by
  set U' := U ∩ {z | ∀ i, sortEval (MixedPolynomialSyntax.contextSort i) (z i)}
  have hU' : DefinableOver C MixedPolynomialSyntax.contextSort U' :=
    raw_definableOver_sorted hc C _ U' (hU.inter (sorted_definable C _)) (fun z hz => hz.2)
  obtain ⟨p, ψ, hqf, hws, heq⟩ := DefinableOver.quantifier_free hM hU'
  have hsort : ∀ x : VFType (M := M), ∀ i,
      sortEval (MixedPolynomialSyntax.contextSort (m := m) i) ((Fin.cons x.val ys : Fin (m + 1) → M) i) := by
    intro x i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact x.property
    · exact hys j
  have hmem : ∀ x : VFType (M := M),
      (Fin.cons x.val ys : Fin (m + 1) → M) ∈ U ↔ ψ.Realize p.values (Fin.cons x.val ys) := by
    intro x
    have h1 : (Fin.cons x.val ys : Fin (m + 1) → M) ∈ U ↔ (Fin.cons x.val ys : Fin (m + 1) → M) ∈ U' :=
      ⟨fun hx => ⟨hx, hsort x⟩, fun hx => hx.1⟩
    rw [h1, heq]
    exact ⟨fun hx => hx.2, fun hx => ⟨hsort x, hx⟩⟩
  rw [hmem, hmem]
  exact MixedPolynomialSupport.formula_iff_of_support p E (fun i hi => hC _ (p.mem_base i) hi) ψ hqf
    hws t t' ys hys (fun q _ => congrArg Subtype.val (rv_poly_eq E hE q ht h))

include hE hc in
/-- `same_type` with the RV tuple indexed by any finite type. -/
theorem same_type_sum {C : Set M} (hC : ∀ c ∈ C, ∀ h : iVF c, (⟨c, h⟩ : VFType (M := M)) ∈ E)
    {β : Type} [Finite β] (U : Set (Unit ⊕ β → M)) (hU : C.Definable LRV U)
    {t t' : VFType (M := M)} (ht : 1 < Values.vfValueHom t) (h : rv M t = rv M t')
    (ys : β → M) (hys : ∀ j, iRV (ys j)) :
    Sum.elim (fun _ => t.val) ys ∈ U ↔ Sum.elim (fun _ => t'.val) ys ∈ U := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin β
  let g : Unit ⊕ β → Fin (m + 1) := Sum.elim (fun _ => 0) (fun j => (e j).succ)
  have hU' : C.Definable LRV ((fun z : Fin (m + 1) → M => z ∘ g) ⁻¹' U) := hU.preimage_comp g
  have hcomp : ∀ x : VFType (M := M),
      (Fin.cons x.val (ys ∘ e.symm) : Fin (m + 1) → M) ∘ g = Sum.elim (fun _ => x.val) ys := by
    intro x
    funext k
    rcases k with _ | j
    · rfl
    · simp [g]
  have := same_type E hE hc hC _ hU' ht h (ys ∘ e.symm) (fun j => hys _)
  simpa only [Set.mem_preimage, hcomp] using this

end Types

/-! ### Definability over a base without `Γ`-names -/

section Ground

open DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}

/-- A set definable over the base `⟨S, ∅⟩` is definable over `S`. -/
theorem gammaGround_empty_definable {Q : Space LRV M} {S : Set M} {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc ⟨S, ∅⟩ Q A) : Q.Definable S A := by
  obtain ⟨k, γ, hγ, R, hR, hAR⟩ := hA
  cases k with
  | succ k => exact absurd (hγ 0) (Set.notMem_empty _)
  | zero =>
    let P := (volumeGammaSpace hc).power (Fin 0)
    let g : P.Index ⊕ Q.Index → Q.Index := Sum.elim (fun i => i.1.elim0) id
    have h := hR.preimage_comp g
    change S.Definable LRV (Q.preimage A)
    convert h using 1
    ext z
    simp only [Set.mem_preimage]
    have hP : (z ∘ g) ∘ Sum.inl ∈ P.domain := fun i => i.elim0
    constructor
    · rintro ⟨hz, hzA⟩
      refine ⟨⟨hP, hz⟩, ?_⟩
      have hγ' : P.decode ⟨(z ∘ g) ∘ Sum.inl, hP⟩ = γ := funext fun i => i.elim0
      have h2 := (hAR _).mp hzA
      show (P.decode ⟨(z ∘ g) ∘ Sum.inl, hP⟩, Q.decode ⟨(z ∘ g) ∘ Sum.inr, hz⟩) ∈ R
      rw [hγ']
      exact h2
    · rintro ⟨hw, hzR⟩
      refine ⟨hw.2, (hAR _).mpr ?_⟩
      have hγ' : P.decode ⟨(z ∘ g) ∘ Sum.inl, hw.1⟩ = γ := funext fun i => i.elim0
      have h2 : (P.decode ⟨(z ∘ g) ∘ Sum.inl, hw.1⟩, Q.decode ⟨(z ∘ g) ∘ Sum.inr, hw.2⟩) ∈ R := hzR
      rw [hγ'] at h2
      exact h2

end Ground

end DiamondIntegral.Section8.SameType
