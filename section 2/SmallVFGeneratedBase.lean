import «section 2».Bases
import CanonicalCountable
import VFAlgClosed
import Section4.FullDimension
import Mathlib.ModelTheory.Skolem

/-!
# Small temporary VF-generated bases for geometric statements

A countable elementary substructure containing the finite defining
parameters has a VF field and representatives for all its RV elements.
This supplies the temporary base used in Lemmas 2.48 and 2.50, without
imposing VF-generation on the original ground parameter set.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem elementary_singleton_mem (C : LRV.ElementarySubstructure M) (x : M)
    (hx : (C : Set M).Definable₁ LRV {x}) : x ∈ (C : Set M) := by
  obtain ⟨y,hy,hyC⟩ := C.meetsDefinable {x} (Set.singleton_nonempty x) hx
  exact Set.mem_singleton_iff.mp hy ▸ hyC

noncomputable def elementaryVFGeneratedFieldBase (C : LRV.ElementarySubstructure M) :
    VFGeneratedFieldBase C.toSubstructure := by
  classical
  have hinv : ∀ x : VF M, x.val ∈ (C : Set M) → (x⁻¹).val ∈ (C : Set M) := by
    intro x hx
    exact elementary_singleton_mem C (x⁻¹).val
      (definableClosureAt_vf_inv (C : Set M) x
        (definableClosureAt_of_mem (σ := .vf) hx x.property)).raw_definable
  let B := VFFieldBase.ofSubstructure C.toSubstructure hinv
  refine { toVFFieldBase := B, rv_lift := ?_ }
  intro t ht htRV
  have hconst : (C : Set M).DefinableFun LRV (fun _ : Fin 1 → M => t) :=
    LRV.definableFun_const (Fin 1) ht
  have hrv : (C : Set M).DefinableFun LRV (fun z : Fin 1 → M => iRv (z 0)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show (C : Set M).DefinableMap LRV (fun z : Fin 1 → M => ![z 0]) from by
        intro i
        fin_cases i
        exact Set.DefinableFun.proj LRV)
  let D : Set M := {x | iVF x ∧ iRv x = t}
  have hD : (C : Set M).Definable₁ LRV D := by
    change (C : Set M).Definable LRV {z : Fin 1 → M | z 0 ∈ D}
    convert ((definableAt_sort (C : Set M) .vf).raw_definable).inter (hrv.ofPred_eq hconst) using 1
    ext z
    rfl
  obtain ⟨a,ha⟩ := rv_surjective (M := M) ⟨t,htRV⟩
  have hneD : D.Nonempty := ⟨a.val,a.property,congrArg Subtype.val ha⟩
  obtain ⟨x,hxD,hxC⟩ := C.meetsDefinable D hneD hD
  let y : VF M := ⟨x,hxD.1⟩
  exact ⟨⟨y,(B.mem_iff y).mpr hxC⟩,hxD.2⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_countable_vf_generated_base
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : Set M) (hF : F.Finite) :
    ∃ C : LRV.ElementarySubstructure M, F ⊆ (C : Set M) ∧ Cardinal.mk C ≤ Cardinal.aleph0 ∧
      ∃ B : VFGeneratedFieldBase C.toSubstructure,
        ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val < 1 := by
  classical
  obtain ⟨ε,hε0,hε⟩ := model_valuation_nontrivial hv
  let T := insert ε.val F
  haveI : Finite T := (hF.insert ε.val).to_subtype
  have hT : Cardinal.mk T ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hLang : LRV.card ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  letI : IsAlgClosed (VF M) := VFAlgClosed.isAlgClosed_vfType
  haveI : Infinite (VF M) := inferInstance
  have hMcard : Cardinal.aleph0 ≤ Cardinal.mk M :=
    (Cardinal.aleph0_le_mk (VF M)).trans (Cardinal.mk_subtype_le _)
  obtain ⟨C,hTC,hCard⟩ := LRV.exists_elementarySubstructure_card_eq T (Cardinal.aleph0 : Cardinal.{0}) le_rfl
    (by simpa only [Cardinal.lift_id] using hT)
    (by simpa only [Cardinal.lift_id] using hLang)
    (by simpa only [Cardinal.lift_id] using hMcard)
  let B := elementaryVFGeneratedFieldBase C
  have hεC : ε.val ∈ (C : Set M) := hTC (Or.inl rfl)
  have hεB : ε ∈ B.field := (B.mem_iff ε).mpr hεC
  refine ⟨C,fun x hx => hTC (Or.inr hx),?_,B,⟨ε,hεB⟩,?_,hε⟩
  · exact le_of_eq (by simpa only [Cardinal.lift_id] using hCard)
  · intro he
    exact hε0 (congrArg (fun x : B.field => x.val) he)

/-- A geometric statement may use a small VF-generated base containing
the finite parameters of its defining formula. The original S need not
be VF-generated, or itself small. -/
theorem exists_small_vf_generated_base_for_definable
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) {S : Set M} {ι : Type}
    (D : Set (ι → M)) (hD : S.Definable LRV D) :
    ∃ C : LRV.ElementarySubstructure M, Cardinal.mk C < κ ∧ (C : Set M).Definable LRV D ∧
      ∃ B : VFGeneratedFieldBase C.toSubstructure,
        ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val < 1 := by
  obtain ⟨F,hFS,hDF⟩ := Set.definable_iff_finitely_definable.mp hD
  obtain ⟨C,hFC,hcount,B,hnt⟩ := exists_countable_vf_generated_base hv (F : Set M) F.finite_toSet
  exact ⟨C,hcount.trans_lt hκ,hDF.mono hFC,B,hnt⟩

theorem exists_small_vf_generated_base_for_two_definable
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) {S : Set M} {ι α : Type}
    (D : Set (ι → M)) (hD : S.Definable LRV D)
    (E : Set (α → M)) (hE : S.Definable LRV E) :
    ∃ C : LRV.ElementarySubstructure M, Cardinal.mk C < κ ∧
      (C : Set M).Definable LRV D ∧ (C : Set M).Definable LRV E ∧
      ∃ B : VFGeneratedFieldBase C.toSubstructure,
        ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val < 1 := by
  obtain ⟨F,hFS,hDF⟩ := Set.definable_iff_finitely_definable.mp hD
  obtain ⟨G,hGS,hEG⟩ := Set.definable_iff_finitely_definable.mp hE
  obtain ⟨C,hFC,hcount,B,hnt⟩ := exists_countable_vf_generated_base hv
    ((F : Set M) ∪ (G : Set M)) (F.finite_toSet.union G.finite_toSet)
  exact ⟨C,hcount.trans_lt hκ,hDF.mono (fun x hx => hFC (Or.inl hx)),
    hEG.mono (fun x hx => hFC (Or.inr hx)),B,hnt⟩

end DiamondIntegral.Section2
