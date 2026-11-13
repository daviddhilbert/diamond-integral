import «section 4».FieldDefinableRing
import «section 4».FiniteFieldPointDiagram
import «section 4».FiniteRelationSeparation

/-! The pure-field definable Grothendieck presentation remains nontrivial
after killing the affine line. Every finite proposed relation admits a
finite-field point-count character modulo the field cardinality, where
the unit is 1 and the affine line is 0. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldAffineNontrivial
open FieldDefinableRing FieldPositiveExpressions
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [FirstOrder.Ring.CompatibleRing K]

theorem separate_finite (s : Finset (FreeCommRing (Chart K)))
    (hs : (s : Set (FreeCommRing (Chart K))) ⊆ {r | Relation K r}) :
    ∃ q : ℕ, ∃ f : FreeCommRing (Chart K) →+* ZMod q,
      f 1 ≠ 0 ∧ f (FreeCommRing.of (affine K)) = 0 ∧ ∀ r ∈ s, f r = 0 := by
  have hrep' (r : FreeCommRing (Chart K)) (hr : Relation K r) : ∃ a b : Expression K,
      ∃ R : Set ((a.variables Chart.arity ⊕ b.variables Chart.arity) → K),
        (Set.univ : Set K).Definable Language.ring R ∧
        DefinableBiUniqueRelation.BiUnique (domain K a) (domain K b) R ∧
        a.eval FreeCommRing.of - b.eval FreeCommRing.of = r := by
    cases hr with
    | bijective a b R hR h => exact ⟨a, b, R, hR, h, rfl⟩
  have hrep (r : s) := hrep' r.val (hs r.property)
  choose left right graphs hgraphs hbij he using hrep
  obtain ⟨q, _, hq, counts, haffine, hcounts⟩ := FiniteFieldPointDiagram.counts_exist
    Chart.arity Chart.domain (fun a : Chart K => a.definable)
    left right graphs hgraphs hbij (affine K) rfl rfl 1
  letI : Fact (1 < q) := ⟨hq⟩
  let f : FreeCommRing (Chart K) →+* ZMod q := FreeCommRing.lift (fun a => (counts a : ZMod q))
  refine ⟨q, f, ?_, ?_, ?_⟩
  · rw [map_one]
    exact one_ne_zero
  · change FreeCommRing.lift (fun a => (counts a : ZMod q)) (FreeCommRing.of (affine K)) = 0
    rw [FreeCommRing.lift_of, haffine]
    exact ZMod.natCast_self q
  · intro r hr
    let j : s := ⟨r, hr⟩
    change f j.val = 0
    rw [← he j, map_sub]
    change FreeCommRing.lift (fun a => (counts a : ZMod q)) ((left j).eval FreeCommRing.of) -
      FreeCommRing.lift (fun a => (counts a : ZMod q)) ((right j).eval FreeCommRing.of) = 0
    rw [FieldExpressionCounts.eval_lift, FieldExpressionCounts.eval_lift,
      FieldExpressionCounts.eval_cast, FieldExpressionCounts.eval_cast, hcounts j, sub_self]

theorem one_not_mem : (1 : FreeCommRing (Chart K)) ∉ Ideal.span (affineRelations K) := by
  apply FiniteRelationSeparation.not_mem_span
  intro s hs
  let t := s.filter (fun r => r ≠ FreeCommRing.of (affine K))
  have ht : (t : Set (FreeCommRing (Chart K))) ⊆ {r | Relation K r} := by
    intro r hr
    obtain ⟨hrs, hne⟩ := Finset.mem_filter.mp hr
    exact (hs hrs).resolve_left hne
  obtain ⟨q, f, h1, ha, hf⟩ := separate_finite K t ht
  refine ⟨q, f, h1, fun r hr => ?_⟩
  by_cases he : r = FreeCommRing.of (affine K)
  · simpa only [he] using ha
  · exact hf r (Finset.mem_filter.mpr ⟨hr, he⟩)

theorem quotient_one_ne_zero : (1 : AffineQuotient K) ≠ 0 := by
  change Ideal.Quotient.mk (Ideal.span (affineRelations K)) (1 : FreeCommRing (Chart K)) ≠ 0
  intro h
  exact one_not_mem K (Ideal.Quotient.eq_zero_iff_mem.mp h)

instance affineQuotient_nontrivial : Nontrivial (AffineQuotient K) :=
  nontrivial_of_ne 1 0 (quotient_one_ne_zero K)

end DiamondIntegral.Section4.FieldAffineNontrivial
