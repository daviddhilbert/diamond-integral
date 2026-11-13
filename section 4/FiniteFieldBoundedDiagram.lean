import «section 4».FieldBoundedProjection
import «section 4».FieldExpressionCounts
import «section 4».FieldExpressionCongruence
import «section 4».FiniteFieldFormulaParameters
import «section 4».BiUniqueFormula
import «section 4».ACFFormulaSpecialization
import «section 4».ACFLargeFiniteParameterField

/-! A finite diagram of definable bijections over a characteristic-zero
algebraically closed field admits integer point counts over arbitrarily
large finite fields. Counts preserve every positive-expression equality
in that diagram and give the affine line the field's cardinality. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FiniteFieldBoundedDiagram
open FieldPositiveExpressions DefinableBiUniqueRelation
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem counts_exist {K G J L : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [FirstOrder.Ring.CompatibleRing K] [Finite J] [Finite L]
    (arity : G → ℕ) (D : ∀ g, Set (Fin (arity g) → K))
    (hD : ∀ g, (Set.univ : Set K).Definable Language.ring (D g))
    (left right : J → Expr G)
    (graphs : ∀ j, Set (((left j).variables arity ⊕ (right j).variables arity) → K))
    (hgraphs : ∀ j, (Set.univ : Set K).Definable Language.ring (graphs j))
    (hbij : ∀ j, BiUnique ((left j).domain arity D) ((right j).domain arity D) (graphs j))
    (kept : L → G) (dim bound : L → ℕ)
    (select : ∀ l, Fin (dim l) → Fin (arity (kept l)))
    (hbounded : ∀ l, FieldBoundedProjection.Bounded (D (kept l)) (select l) (bound l))
    (a : G) (ha : arity a = 1) (hDa : D a = Set.univ) (N : ℕ) :
    ∃ q : ℕ, N < q ∧ 1 < q ∧ ∃ counts : G → ℕ,
      counts a = q ∧ (∀ j, (left j).eval counts = (right j).eval counts) ∧
        ∀ l, counts (kept l) ≤ bound l * q ^ dim l := by
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite L
  let atoms : Finset G := insert a ((Finset.univ.biUnion (fun j => (left j).vars ∪ (right j).vars)) ∪
    Finset.univ.image kept)
  have ha_atoms : a ∈ atoms := Finset.mem_insert_self _ _
  have hleft (j : J) : (left j).vars ⊆ atoms := by
    intro g hg
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ j, Finset.mem_union_left _ hg⟩))
  have hright (j : J) : (right j).vars ⊆ atoms := by
    intro g hg
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ j, Finset.mem_union_right _ hg⟩))
  have hkept (l : L) : kept l ∈ atoms :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩))
  let I := atoms ⊕ J
  let vars : I → Type
    | .inl g => Fin (arity g.val)
    | .inr j => (left j).variables arity ⊕ (right j).variables arity
  let sets : ∀ i : I, Set (vars i → K)
    | .inl g => D g.val
    | .inr j => graphs j
  have hsets (i : I) : (Set.univ : Set K).Definable Language.ring (sets i) := by
    cases i with
    | inl g => exact hD g.val
    | inr j => exact hgraphs j
  obtain ⟨params, φ, hφ⟩ := FiniteFieldFormulaParameters.common_formulas vars sets hsets
  let v : params → K := fun p => p.val
  let code (g : G) : Language.ring.Formula (params ⊕ Fin (arity g)) :=
    if hg : g ∈ atoms then φ (.inl ⟨g, hg⟩) else ⊥
  let graphCode (j : J) : Language.ring.Formula
      (params ⊕ ((left j).variables arity ⊕ (right j).variables arity)) := φ (.inr j)
  have hcode (g : G) (hg : g ∈ atoms) (x : Fin (arity g) → K) :
      (code g).Realize (Sum.elim v x) ↔ x ∈ D g := by
    simp only [code, dif_pos hg]
    exact hφ (.inl ⟨g, hg⟩) x
  have hdomain (g : G) (hg : g ∈ atoms) :
      {x | (code g).Realize (Sum.elim v x)} = D g := Set.ext (hcode g hg)
  have hleftDomain (j : J) :
      {x | ((left j).formula arity code).Realize (Sum.elim v x)} = (left j).domain arity D := by
    calc
      _ = (left j).domain arity (fun g => {x | (code g).Realize (Sum.elim v x)}) :=
        Set.ext (fun x => FieldPositiveExpressions.formula_realize arity code v (left j) x)
      _ = _ := Expr.domain_congr arity _ D (left j) (fun g hg => hdomain g (hleft j hg))
  have hrightDomain (j : J) :
      {x | ((right j).formula arity code).Realize (Sum.elim v x)} = (right j).domain arity D := by
    calc
      _ = (right j).domain arity (fun g => {x | (code g).Realize (Sum.elim v x)}) :=
        Set.ext (fun x => FieldPositiveExpressions.formula_realize arity code v (right j) x)
      _ = _ := Expr.domain_congr arity _ D (right j) (fun g hg => hdomain g (hright j hg))
  have hgraphDomain (j : J) : {x | (graphCode j).Realize (Sum.elim v x)} = graphs j :=
    Set.ext (fun x => hφ (.inr j) x)
  let conditions (j : J) : Language.ring.Formula params := BiUniqueFormula.formula
    ((left j).formula arity code) ((right j).formula arity code) (graphCode j)
  have hconditions (j : J) : (conditions j).Realize v := by
    have hb := hbij j
    rw [← hleftDomain j, ← hrightDomain j, ← hgraphDomain j] at hb
    exact (BiUniqueFormula.formula_realize ((left j).formula arity code)
      ((right j).formula arity code) (graphCode j) v).mpr hb
  let boundConditions (l : L) : Language.ring.Formula params :=
    FieldBoundedProjection.formula (code (kept l)) (select l) (bound l)
  have hboundConditions (l : L) : (boundConditions l).Realize v := by
    apply (FieldBoundedProjection.formula_realize _ _ _ _).mpr
    rw [hdomain (kept l) (hkept l)]
    exact hbounded l
  let sentence : Language.ring.Formula params :=
    ((code a).iAlls (Fin (arity a)) ⊓ Formula.iInf conditions) ⊓ Formula.iInf boundConditions
  have hsentence : sentence.Realize v := by
    simp only [sentence, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_iInf]
    refine ⟨⟨fun x => (hcode a ha_atoms x).mpr ?_, hconditions⟩, hboundConditions⟩
    rw [hDa]
    exact Set.mem_univ x
  obtain ⟨p, hp, hw⟩ := ACFFormulaSpecialization.formula_specializes sentence v hsentence
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw⟩ := hw
  let F := AlgebraicClosure (ZMod p)
  obtain ⟨E, hEfinite, hEgalois, hEparams, hElarge⟩ := ACFLargeFiniteParameterField.exists_large p
    (Set.range w) (Set.finite_range w) (max N 1)
  letI : Finite E := hEfinite
  letI : IsGalois E F := hEgalois
  have hwe (i : params) : w i ∈ Set.range (algebraMap E F) :=
    ⟨⟨w i, hEparams ⟨i, rfl⟩⟩, rfl⟩
  have hw' := Formula.realize_inf.mp (Formula.realize_inf.mp hw).1
  have hwBound : ∀ l, (boundConditions l).Realize w :=
    Formula.realize_iInf.mp (Formula.realize_inf.mp hw).2
  have hwAffine : ∀ x : Fin (arity a) → F, (code a).Realize (Sum.elim w x) :=
    Formula.realize_iAlls.mp hw'.1
  have hwConditions : ∀ j, (conditions j).Realize w := Formula.realize_iInf.mp hw'.2
  let setsF (g : G) : Set (Fin (arity g) → F) := {x | (code g).Realize (Sum.elim w x)}
  let counts (g : G) : ℕ := GaloisPointCounts.count (E := E) (setsF g)
  refine ⟨Nat.card E, (le_max_left N 1).trans_lt hElarge, (le_max_right N 1).trans_lt hElarge,
    counts, ?_, ?_, ?_⟩
  · have he : setsF a = Set.univ := by
      ext x
      exact iff_of_true (hwAffine x) (Set.mem_univ x)
    change GaloisPointCounts.count (E := E) (setsF a) = Nat.card E
    rw [he]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, ha, pow_one] using
      (GaloisPointCounts.univ (E := E) (K := F) (α := Fin (arity a)))
  · intro j
    have hb := (BiUniqueFormula.formula_realize ((left j).formula arity code)
      ((right j).formula arity code) (graphCode j) w).mp (hwConditions j)
    have hL := ACFFormulaSpecialization.definable_of_parameters (Set.range (algebraMap E F))
      ((left j).formula arity code) w hwe
    have hR := ACFFormulaSpecialization.definable_of_parameters (Set.range (algebraMap E F))
      ((right j).formula arity code) w hwe
    have hG := ACFFormulaSpecialization.definable_of_parameters (Set.range (algebraMap E F)) (graphCode j) w hwe
    have hc := DefinableBiUniqueRelation.rational_count_eq hb hL hR hG
    have hLF : {x | ((left j).formula arity code).Realize (Sum.elim w x)} =
        (left j).domain arity setsF :=
      Set.ext (fun x => FieldPositiveExpressions.formula_realize arity code w (left j) x)
    have hRF : {x | ((right j).formula arity code).Realize (Sum.elim w x)} =
        (right j).domain arity setsF :=
      Set.ext (fun x => FieldPositiveExpressions.formula_realize arity code w (right j) x)
    rw [hLF, hRF] at hc
    change GaloisPointCounts.count (E := E) ((left j).domain arity setsF) =
      GaloisPointCounts.count (E := E) ((right j).domain arity setsF) at hc
    rw [FieldExpressionCounts.count_domain, FieldExpressionCounts.count_domain] at hc
    exact hc

  · intro l
    have hb := (FieldBoundedProjection.formula_realize _ _ _ w).mp (hwBound l)
    have hc := FieldBoundedProjection.count_le (E := E) hb
    simpa only [counts, setsF, Nat.card_fin] using hc

end DiamondIntegral.Section4.FiniteFieldBoundedDiagram
