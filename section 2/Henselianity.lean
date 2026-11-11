import «section 2».Bases
import Section7.ValuationHenselian

/-! Proof steps for Lemma 2.11. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Polynomial IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

/-- The simple Hensel root is unique in the specified residue class.
This uses Mathlib's proof of Stacks Project tag 06RR. -/
theorem hensel_root_unique {R : Type*} [CommRing R] [IsLocalRing R]
    (f : R[X]) (a b c : R) (hb : f.eval b = 0) (hc : f.eval c = 0)
    (hba : b - a ∈ maximalIdeal R) (hca : c - a ∈ maximalIdeal R)
    (hu : IsUnit (f.derivative.eval a)) : b = c := by
  have hr : residue R b = residue R a := sub_eq_zero.mp (by
    simpa only [map_sub] using (residue_eq_zero_iff (b - a)).mpr hba)
  have hub : IsUnit (f.derivative.eval b) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [← Polynomial.eval_map_apply, hr, Polynomial.eval_map_apply]
    exact (residue_ne_zero_iff_isUnit _).mpr hu
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hb hc _ hub
  have hbc := (maximalIdeal R).sub_mem hba hca
  exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp
    (by simpa only [sub_sub_sub_cancel_right] using hbc))

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)

omit hM in
private theorem term_func0_realize {α : Type} (f : Fn 0)
    (z : α → M) : (Term.func (L := LRV) f Fin.elim0).realize z =
      Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
  congr 1
  funext i
  exact i.elim0

omit hM in
private theorem term_func1_realize {α : Type} (f : Fn 1) (t : LRV.Term α)
    (z : α → M) : (Term.func f ![t]).realize z = Structure.funMap (L := LRV) f ![t.realize z] := by
  change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
  congr 1
  funext i
  fin_cases i
  rfl

omit hM in
private theorem term_func2_realize {α : Type} (f : Fn 2) (t u : LRV.Term α)
    (z : α → M) : (Term.func f ![t,u]).realize z =
      Structure.funMap (L := LRV) f ![t.realize z,u.realize z] := by
  change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
  congr 1
  funext i
  fin_cases i <;> rfl

include hv in
/-- A residue class of the valuation ring, with exactly its original centre
as parameter. This is a sorted formula, independent of off-sort values. -/
theorem residueClass_definable (A : Set M) (a : VF M) (ha : a.val ∈ A) :
    DefinableAt A .vf {x | ∃ b : VF M, b.val = x ∧ v (b - a) < 1} := by
  let d : LRV.Term (Fin 1 ⊕ Fin 1) := .func Fn.vfAdd
    ![.var (.inr 0), .func Fn.vfNeg ![.var (.inl 0)] ]
  let u : LRV.Term (Fin 1 ⊕ Fin 1) := .func Fn.vfOne Fin.elim0
  let φ : LRV.BoundedFormula (Fin 1) 1 :=
    .imp (.rel Rel.rvLe ![.func Fn.rvMap ![d], .func Fn.rvMap ![u] ]) .falsum
  let r : Parameters A := ⟨1, ![a.val], fun _ => .vf,
    by intro i; fin_cases i; exact a.property,
    by intro i; fin_cases i; exact ha⟩
  have hw : WellSorted r.sorts (fun _ => .vf) φ := by
    apply WellSorted.imp
    · apply WellSorted.rel
      intro i
      fin_cases i <;> dsimp only [r, d, u] <;> decide
    · exact WellSorted.falsum _
  have he (x : VF M) : φ.Realize r.values ![x.val] ↔ v (x - a) < 1 := by
    have ht : (fun i => (![Term.func Fn.rvMap ![d], Term.func Fn.rvMap ![u] ] i).realize
        (Sum.elim r.values ![x.val])) =
        ![iRv (iVFAdd x.val (iVFNeg a.val)), iRv iVFOne] := by
      funext i
      fin_cases i
      · change (Term.func Fn.rvMap ![d]).realize _ = iRv _
        rw [term_func1_realize]
        change iRv (d.realize _) = iRv _
        congr 1
        dsimp only [d]
        rw [term_func2_realize]
        change iVFAdd x.val ((Term.func Fn.vfNeg ![.var (.inl 0)] :
          LRV.Term (Fin 1 ⊕ Fin 1)).realize (Sum.elim r.values ![x.val])) = _
        rw [term_func1_realize]
        rfl
      · change (Term.func Fn.rvMap ![u]).realize _ = iRv iVFOne
        rw [term_func1_realize]
        change iRv (u.realize _) = iRv iVFOne
        congr 1
        exact term_func0_realize Fn.vfOne _
    change (¬ Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => (![Term.func Fn.rvMap ![d], Term.func Fn.rvMap ![u] ] i).realize
        (Sum.elim r.values ![x.val]))) ↔ _
    rw [ht]
    change ¬ VFValued.predV (1 : VF M) (x - a) ↔ _
    rw [hv, map_one, not_le]
  refine ⟨⟨r, φ, hw, ?_⟩, ?_⟩
  · ext z
    have hz : ![z 0] = z := by funext i; fin_cases i; rfl
    constructor
    · rintro ⟨x, hx, hvx⟩
      have hzx : ![x.val] = z := by rw [hx]; exact hz
      exact ⟨by intro i; fin_cases i; change iVF (z 0); rw [← hx]; exact x.property,
        hzx ▸ (he x).mpr hvx⟩
    · rintro ⟨hx, hφ⟩
      exact ⟨⟨z 0, hx 0⟩, rfl, (he ⟨z 0, hx 0⟩).mp (hz.symm ▸ hφ)⟩
  · rintro _ ⟨x, rfl, _⟩
    exact x.property

include hv in
/-- The forward implication of Lemma 2.11. Only the standing VF-field
convention is needed for this implication. -/
theorem henselian_of_definableClosure_eq (S : Set M) (B : VFFieldBase S)
    (hclosed : definableClosure S = S) :
    HenselianLocalRing (v.comap B.field.subtype).valuationSubring := by
  classical
  letI : IsAlgClosed (VF M) := VFAlgClosed.isAlgClosed_vfType
  let K := B.field
  let w := v.comap K.subtype
  let R := w.valuationSubring
  let T := v.valuationSubring
  let ι : R →+* T :=
    { toFun := fun x => ⟨(x : K).val, x.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let : HenselianLocalRing T := SpecialTransformations.Section7.valuationRing_henselian v
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a hfa hu
  let F := f.map ι
  let p := f.map R.subtype
  have hfa' : F.eval (ι a) ∈ maximalIdeal T := by
    apply (Valuation.mem_maximalIdeal_iff (VF M) v).mpr
    rw [Polynomial.eval_map_apply]
    exact (Valuation.mem_maximalIdeal_iff K w).mp hfa
  have hu' : IsUnit (F.derivative.eval (ι a)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply]
    exact hu.map ι
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian F (hf.map ι) (ι a) hfa' hu'
  have heval (z : T) : (F.eval z).val = p.eval₂ K.subtype z.val := by
    change T.subtype (F.eval z) = _
    rw [← Polynomial.eval_map_apply, Polynomial.eval_map, Polynomial.eval₂_map]
    dsimp only [p]
    rw [Polynomial.eval₂_map]
    rfl
  have hbroot : p.eval₂ K.subtype b.val = 0 := by
    rw [← heval, hb]
    rfl
  have hbclose : v (b.val - (a : K).val) < 1 :=
    (Valuation.mem_maximalIdeal_iff (VF M) v).mp hba
  let C : Set M := {x | ∃ z : VF M, z.val = x ∧ v (z - (a : K).val) < 1}
  let U := PolynomialRoots.rootSet K p ∩ C
  have hU : DefinableAt S .vf U :=
    (PolynomialRoots.rootSet_definable S K
      (fun x => (B.mem_iff x.val).mp x.property) p).inter
      (residueClass_definable v hv S (a : K).val
        ((B.mem_iff _).mp (a : K).property))
  have hUb : b.val.val ∈ U := ⟨⟨b.val.property, hbroot⟩, ⟨b.val, rfl, hbclose⟩⟩
  have hsingle : U = {b.val.val} := by
    ext x
    constructor
    · rintro ⟨⟨hx, hxroot⟩, z, rfl, hzclose⟩
      have hzval : v z ≤ 1 := by
        have he : z = (z - (a : K).val) + (a : K).val := by ring
        rw [he]
        exact (v.map_add _ _).trans (max_le hzclose.le
          ((Valuation.mem_valuationSubring_iff w _).mp a.property))
      let z' : T := ⟨z, (Valuation.mem_valuationSubring_iff v _).mpr hzval⟩
      have hzroot : F.eval z' = 0 := by
        apply Subtype.val_injective
        rw [heval]
        exact hxroot
      have hzclass : z' - ι a ∈ maximalIdeal T :=
        (Valuation.mem_maximalIdeal_iff (VF M) v).mpr hzclose
      have he := hensel_root_unique F (ι a) z' b hzroot hb hzclass hba hu'
      exact congrArg (fun y : T => y.val.val) he
    · rintro rfl
      exact hUb
  have hdb : DefinableClosureAt S .vf b.val.val := by
    change DefinableAt S .vf {b.val.val}
    rw [← hsingle]
    exact hU
  have hbS : b.val.val ∈ S := hclosed ▸ (show b.val.val ∈ definableClosure S from ⟨.vf, hdb⟩)
  let bK : K := ⟨b.val, (B.mem_iff b.val).mpr hbS⟩
  let bR : R := ⟨bK, b.property⟩
  have hib : ι bR = b := rfl
  refine ⟨bR, ?_, ?_⟩
  · change f.eval bR = 0
    apply (show Function.Injective ι from fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun t : T => t.val) h)))
    rw [map_zero, ← Polynomial.eval_map_apply, hib]
    exact hb
  · exact (Valuation.mem_maximalIdeal_iff (VF M) v).mp hba
    |> (Valuation.mem_maximalIdeal_iff K w).mpr

end DiamondIntegral.Section2
