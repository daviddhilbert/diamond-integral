import Section3.QuantifierFree
import Mathlib.Algebra.MvPolynomial.Eval

/-! A definable set depends only on the `rv` of finitely many polynomials.

Let `M ⊨ ACVF`, let `X` be definable over a parameter set `A` at a tuple of sorts `sn`, and let `R` be
a subring of the field sort containing the field-sort elements of `A`. Then there is a finite set
`F` of polynomials over `R`, in the variables of the tuple, such that membership of a sorted tuple
`xs` in `X` depends only on its RV-coordinates and on `rv(P(xs))`, `P ∈ F` (`definable_agree`).

This is the usual consequence of quantifier elimination: a quantifier-free formula is a Boolean
combination of equalities of field terms, which are polynomial identities (`vf_term`), and of RV
relations between RV terms, whose values depend only on the `rv` of the field terms under `rv`
(`rv_term`). Field-sort coordinates are read through `vfPoint`; RV slots get the dummy value `0`,
and no polynomial of `F` needs them. -/

set_option autoImplicit false

noncomputable section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace DiamondIntegral.Section8.NormalForm

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {α : Type} {N : ℕ} (sα : α → SortTag) (sn : Fin N → SortTag)
variable (v : α → M) (R : Subring (VFType (M := M)))

/-- The field-sort point of a raw tuple, with `0` at the slots that are not in the field sort. -/
def vfPoint (xs : Fin N → M) : Fin N → VFType (M := M) :=
  fun i => if h : sortEval .vf (xs i) then ⟨xs i, h⟩ else 0

/-- The value of a polynomial over `R` at a raw tuple. -/
def polyValue (P : MvPolynomial (Fin N) R) (xs : Fin N → M) : VFType (M := M) :=
  MvPolynomial.eval₂ R.subtype (vfPoint xs) P

/-- Two raw tuples agree on the RV slots and on the `rv` of the polynomials of `F`. -/
def Agree (F : Finset (MvPolynomial (Fin N) R)) (xs xs' : Fin N → M) : Prop :=
  (∀ i, sn i = .rv → xs i = xs' i) ∧ ∀ P ∈ F, iRv (polyValue R P xs).val = iRv (polyValue R P xs').val

variable {sn R} in
theorem Agree.mono {F G : Finset (MvPolynomial (Fin N) R)} (h : F ⊆ G) {xs xs' : Fin N → M}
    (hA : Agree sn R G xs xs') : Agree sn R F xs xs' :=
  ⟨hA.1, fun P hP => hA.2 P (h hP)⟩

theorem eta0 {X : Type} (f : Fin 0 → X) : f = ![] := funext fun i => i.elim0
theorem eta1 {X : Type} (f : Fin 1 → X) : f = ![f 0] := by funext i; fin_cases i; rfl
theorem eta2 {X : Type} (f : Fin 2 → X) : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl

/-- A field-sort term is a polynomial over `R` in the field-sort variables. -/
theorem vf_term (hv : ∀ a, sortEval (sα a) (v a))
    (hR : ∀ a, sα a = .vf → ∀ h : sortEval .vf (v a), (⟨v a, h⟩ : VFType (M := M)) ∈ R)
    (t : LRV.Term (α ⊕ Fin N)) (ht : TmSort sα sn t = some .vf) :
    ∃ P : MvPolynomial (Fin N) R, ∀ xs : Fin N → M, (∀ i, sortEval (sn i) (xs i)) →
      t.realize (Sum.elim v xs) = (polyValue R P xs).val := by
  induction t with
  | var a =>
    cases a with
    | inl a =>
      have ha : sα a = .vf := Option.some.inj ht
      have hva : sortEval .vf (v a) := ha ▸ hv a
      refine ⟨MvPolynomial.C ⟨⟨v a, hva⟩, hR a ha hva⟩, fun xs _ => ?_⟩
      rw [polyValue, MvPolynomial.eval₂_C]
      rfl
    | inr i =>
      have hi : sn i = .vf := Option.some.inj ht
      refine ⟨MvPolynomial.X i, fun xs hx => ?_⟩
      have hxi : sortEval .vf (xs i) := hi ▸ hx i
      rw [polyValue, MvPolynomial.eval₂_X, vfPoint]
      simp only [hxi, ↓reduceDIte]
      rfl
  | func f ts ih =>
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sα sn f ts).mp ht
    cases f with
    | vfZero =>
      refine ⟨0, fun xs _ => ?_⟩
      rw [polyValue, MvPolynomial.eval₂_zero]
      change Structure.funMap (L := LRV) Fn.vfZero (fun i => (ts i).realize (Sum.elim v xs)) = _
      rw [eta0 (fun i => (ts i).realize (Sum.elim v xs))]
      rfl
    | vfOne =>
      refine ⟨1, fun xs _ => ?_⟩
      rw [polyValue, MvPolynomial.eval₂_one]
      change Structure.funMap (L := LRV) Fn.vfOne (fun i => (ts i).realize (Sum.elim v xs)) = _
      rw [eta0 (fun i => (ts i).realize (Sum.elim v xs))]
      rfl
    | vfAdd =>
      obtain ⟨P0, h0⟩ := ih 0 (hargs 0)
      obtain ⟨P1, h1⟩ := ih 1 (hargs 1)
      refine ⟨P0 + P1, fun xs hx => ?_⟩
      rw [polyValue, MvPolynomial.eval₂_add]
      change Structure.funMap (L := LRV) Fn.vfAdd (fun i => (ts i).realize (Sum.elim v xs)) = _
      rw [eta2 (fun i => (ts i).realize (Sum.elim v xs)), h0 xs hx, h1 xs hx]
      rfl
    | vfNeg =>
      obtain ⟨P0, h0⟩ := ih 0 (hargs 0)
      refine ⟨-P0, fun xs hx => ?_⟩
      rw [polyValue, MvPolynomial.eval₂_neg]
      change Structure.funMap (L := LRV) Fn.vfNeg (fun i => (ts i).realize (Sum.elim v xs)) = _
      rw [eta1 (fun i => (ts i).realize (Sum.elim v xs)), h0 xs hx]
      rfl
    | vfMul =>
      obtain ⟨P0, h0⟩ := ih 0 (hargs 0)
      obtain ⟨P1, h1⟩ := ih 1 (hargs 1)
      refine ⟨P0 * P1, fun xs hx => ?_⟩
      rw [polyValue, MvPolynomial.eval₂_mul]
      change Structure.funMap (L := LRV) Fn.vfMul (fun i => (ts i).realize (Sum.elim v xs)) = _
      rw [eta2 (fun i => (ts i).realize (Sum.elim v xs)), h0 xs hx, h1 xs hx]
      rfl
    | rvOne => exact absurd hres (by decide)
    | rvZero => exact absurd hres (by decide)
    | rvMul => exact absurd hres (by decide)
    | rvInv => exact absurd hres (by decide)
    | kAdd => exact absurd hres (by decide)
    | kNeg => exact absurd hres (by decide)
    | rvMap => exact absurd hres (by decide)

/-- The value of an RV term depends only on the RV slots and on the `rv` of finitely many
polynomials. -/
theorem rv_term (hv : ∀ a, sortEval (sα a) (v a))
    (hR : ∀ a, sα a = .vf → ∀ h : sortEval .vf (v a), (⟨v a, h⟩ : VFType (M := M)) ∈ R)
    (t : LRV.Term (α ⊕ Fin N)) (ht : TmSort sα sn t = some .rv) :
    ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
      (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
        t.realize (Sum.elim v xs) = t.realize (Sum.elim v xs') := by
  induction t with
  | var a =>
    cases a with
    | inl a => exact ⟨∅, fun _ _ _ _ _ => rfl⟩
    | inr i =>
      have hi : sn i = .rv := Option.some.inj ht
      exact ⟨∅, fun xs xs' _ _ h => h.1 i hi⟩
  | func f ts ih =>
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sα sn f ts).mp ht
    have key : (∀ i, Fn.argSort f i = .rv) →
        ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
          (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
            (Term.func f ts).realize (Sum.elim v xs) = (Term.func f ts).realize (Sum.elim v xs') := by
      intro hrv
      have ih' : ∀ i, ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
          (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
            (ts i).realize (Sum.elim v xs) = (ts i).realize (Sum.elim v xs') :=
        fun i => ih i (by rw [hargs i, hrv i])
      choose G hG using ih'
      refine ⟨Finset.univ.biUnion G, fun xs xs' hx hx' hA => ?_⟩
      change Structure.funMap (L := LRV) f (fun i => (ts i).realize (Sum.elim v xs)) =
        Structure.funMap (L := LRV) f (fun i => (ts i).realize (Sum.elim v xs'))
      congr 1
      funext i
      exact hG i xs xs' hx hx' (hA.mono (Finset.subset_biUnion_of_mem G (Finset.mem_univ i)))
    cases f with
    | vfZero => exact absurd hres (by decide)
    | vfOne => exact absurd hres (by decide)
    | vfAdd => exact absurd hres (by decide)
    | vfNeg => exact absurd hres (by decide)
    | vfMul => exact absurd hres (by decide)
    | rvOne => exact key (fun i => i.elim0)
    | rvZero => exact key (fun i => i.elim0)
    | rvMul => exact key (fun _ => rfl)
    | rvInv => exact key (fun _ => rfl)
    | kAdd => exact key (fun _ => rfl)
    | kNeg => exact key (fun _ => rfl)
    | rvMap =>
      obtain ⟨P, hP⟩ := vf_term sα sn v R hv hR (ts 0) (hargs 0)
      refine ⟨{P}, fun xs xs' hx hx' hA => ?_⟩
      change Structure.funMap (L := LRV) Fn.rvMap (fun i => (ts i).realize (Sum.elim v xs)) =
        Structure.funMap (L := LRV) Fn.rvMap (fun i => (ts i).realize (Sum.elim v xs'))
      rw [eta1 (fun i => (ts i).realize (Sum.elim v xs)), eta1 (fun i => (ts i).realize (Sum.elim v xs')),
        hP xs hx, hP xs' hx']
      exact hA.2 P (Finset.mem_singleton_self P)

/-- The truth of a quantifier-free formula depends only on the RV slots and on the `rv` of finitely
many polynomials. -/
theorem qf_formula (hv : ∀ a, sortEval (sα a) (v a))
    (hR : ∀ a, sα a = .vf → ∀ h : sortEval .vf (v a), (⟨v a, h⟩ : VFType (M := M)) ∈ R)
    (ψ : LRV.BoundedFormula α N) (hqf : ψ.IsQF) (hws : WellSorted sα sn ψ) :
    ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
      (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
        (ψ.Realize v xs ↔ ψ.Realize v xs') := by
  induction hqf with
  | falsum => exact ⟨∅, fun _ _ _ _ _ => Iff.rfl⟩
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | vf =>
          obtain ⟨P, hP⟩ := vf_term sα sn v R hv hR t ht
          obtain ⟨Q, hQ⟩ := vf_term sα sn v R hv hR u hu
          refine ⟨{P - Q}, fun xs xs' hx hx' hA => ?_⟩
          have hkey : ∀ ys : Fin N → M, (∀ i, sortEval (sn i) (ys i)) →
              ((Term.bdEqual t u).Realize v ys ↔ iRv (polyValue R (P - Q) ys).val = iRVZero) := by
            intro ys hy
            change t.realize (Sum.elim v ys) = u.realize (Sum.elim v ys) ↔ _
            rw [hP ys hy, hQ ys hy]
            have hsub : polyValue R (P - Q) ys = polyValue R P ys - polyValue R Q ys :=
              MvPolynomial.eval₂_sub _ _ _
            have hz : iRv (polyValue R (P - Q) ys).val = iRVZero ↔
                polyValue R (P - Q) ys = (0 : VFType (M := M)) := CanonicalRV.encodedRv_zero_iff _
            rw [hz, hsub]
            constructor
            · intro h
              exact sub_eq_zero_of_eq (Subtype.ext h)
            · intro h
              have h' : polyValue R P ys = polyValue R Q ys := sub_eq_zero.mp h
              exact congrArg Subtype.val h'
          rw [hkey xs hx, hkey xs' hx', hA.2 (P - Q) (Finset.mem_singleton_self _)]
        | rv =>
          obtain ⟨F, hF⟩ := rv_term sα sn v R hv hR t ht
          obtain ⟨G, hG⟩ := rv_term sα sn v R hv hR u hu
          refine ⟨F ∪ G, fun xs xs' hx hx' hA => ?_⟩
          change t.realize (Sum.elim v xs) = u.realize (Sum.elim v xs) ↔
            t.realize (Sum.elim v xs') = u.realize (Sum.elim v xs')
          rw [hF xs xs' hx hx' (hA.mono Finset.subset_union_left),
            hG xs xs' hx hx' (hA.mono Finset.subset_union_right)]
    | rel Rl ts =>
      cases hws with
      | rel _ _ _ hts =>
        have key : (∀ i, Rel.argSort Rl i = .rv) →
            ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
              (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
                ((Relations.boundedFormula Rl ts).Realize v xs ↔
                  (Relations.boundedFormula Rl ts).Realize v xs') := by
          intro hrv
          have h' : ∀ i, ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
              (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
                (ts i).realize (Sum.elim v xs) = (ts i).realize (Sum.elim v xs') :=
            fun i => rv_term sα sn v R hv hR (ts i) (by rw [hts i, hrv i])
          choose G hG using h'
          refine ⟨Finset.univ.biUnion G, fun xs xs' hx hx' hA => ?_⟩
          change Structure.RelMap (L := LRV) Rl (fun i => (ts i).realize (Sum.elim v xs)) ↔
            Structure.RelMap (L := LRV) Rl (fun i => (ts i).realize (Sum.elim v xs'))
          have he : (fun i => (ts i).realize (Sum.elim v xs)) = fun i => (ts i).realize (Sum.elim v xs') :=
            funext fun i => hG i xs xs' hx hx' (hA.mono (Finset.subset_biUnion_of_mem G (Finset.mem_univ i)))
          rw [he]
        cases Rl with
        | memVF =>
          refine ⟨∅, fun xs xs' hx hx' _ => ?_⟩
          have h1 := CanonicalStructure.term_sort hM sα sn v xs hv hx (ts 0) (hts 0)
          have h2 := CanonicalStructure.term_sort hM sα sn v xs' hv hx' (ts 0) (hts 0)
          change Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize (Sum.elim v xs)) ↔
            Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize (Sum.elim v xs'))
          rw [eta1 (fun i => (ts i).realize (Sum.elim v xs)), eta1 (fun i => (ts i).realize (Sum.elim v xs'))]
          exact ⟨fun _ => h2, fun _ => h1⟩
        | memRV =>
          refine ⟨∅, fun xs xs' hx hx' _ => ?_⟩
          have h1 := CanonicalStructure.term_sort hM sα sn v xs hv hx (ts 0) (hts 0)
          have h2 := CanonicalStructure.term_sort hM sα sn v xs' hv hx' (ts 0) (hts 0)
          change Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize (Sum.elim v xs)) ↔
            Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize (Sum.elim v xs'))
          rw [eta1 (fun i => (ts i).realize (Sum.elim v xs)), eta1 (fun i => (ts i).realize (Sum.elim v xs'))]
          exact ⟨fun _ => h2, fun _ => h1⟩
        | memUnits => exact key (fun _ => rfl)
        | rvLe => exact key (fun _ => rfl)
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ =>
      obtain ⟨F, hF⟩ := ihφ hwφ
      obtain ⟨G, hG⟩ := ihψ hwψ
      refine ⟨F ∪ G, fun xs xs' hx hx' hA => ?_⟩
      exact imp_congr (hF xs xs' hx hx' (hA.mono Finset.subset_union_left))
        (hG xs xs' hx hx' (hA.mono Finset.subset_union_right))

/-- **A definable set depends only on the `rv` of finitely many polynomials.** -/
theorem definable_agree {A : Set M} {X : Set (Fin N → M)} (hX : DefinableOver A sn X)
    (hR : ∀ x ∈ A, ∀ h : sortEval .vf x, (⟨x, h⟩ : VFType (M := M)) ∈ R) :
    ∃ F : Finset (MvPolynomial (Fin N) R), ∀ xs xs' : Fin N → M,
      (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (xs' i)) → Agree sn R F xs xs' →
        (xs ∈ X ↔ xs' ∈ X) := by
  obtain ⟨p, ψ, hqf, hws, rfl⟩ := DefinableOver.quantifier_free hM hX
  obtain ⟨F, hF⟩ := qf_formula p.sorts sn p.values R p.sorted
    (fun a _ h => hR _ (p.mem_base a) h) ψ hqf hws
  refine ⟨F, fun xs xs' hx hx' hA => ?_⟩
  simp only [Set.mem_ofPred_eq]
  rw [hF xs xs' hx hx' hA]
  exact ⟨fun h => ⟨hx', h.2⟩, fun h => ⟨hx, h.2⟩⟩

end DiamondIntegral.Section8.NormalForm
