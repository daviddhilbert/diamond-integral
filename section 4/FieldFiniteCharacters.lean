import «section 4».FieldAffineNontrivial

/-! Every finite family of pure-field defining relations has integer
characters with arbitrarily large affine-line value. These characters
need not extend to the entire Grothendieck ring simultaneously. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldFiniteCharacters
open FieldDefinableRing FieldPositiveExpressions
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [FirstOrder.Ring.CompatibleRing K]

theorem exists_large (s : Finset (FreeCommRing (Chart K)))
    (hs : (s : Set (FreeCommRing (Chart K))) ⊆ {r | Relation K r}) (N : ℕ) :
    ∃ q : ℕ, N < q ∧ 1 < q ∧ ∃ f : FreeCommRing (Chart K) →+* ℤ,
      f (FreeCommRing.of (affine K)) = q ∧ ∀ r ∈ s, f r = 0 := by
  have hrep' (r : FreeCommRing (Chart K)) (hr : Relation K r) : ∃ a b : Expression K,
      ∃ R : Set ((a.variables Chart.arity ⊕ b.variables Chart.arity) → K),
        (Set.univ : Set K).Definable Language.ring R ∧
        DefinableBiUniqueRelation.BiUnique (domain K a) (domain K b) R ∧
        a.eval FreeCommRing.of - b.eval FreeCommRing.of = r := by
    cases hr with
    | bijective a b R hR h => exact ⟨a, b, R, hR, h, rfl⟩
  have hrep (r : s) := hrep' r.val (hs r.property)
  choose left right graphs hgraphs hbij he using hrep
  obtain ⟨q, hN, hq, counts, haffine, hcounts⟩ := FiniteFieldPointDiagram.counts_exist
    Chart.arity Chart.domain (fun a : Chart K => a.definable)
    left right graphs hgraphs hbij (affine K) rfl rfl N
  let f : FreeCommRing (Chart K) →+* ℤ := FreeCommRing.lift (fun a => (counts a : ℤ))
  refine ⟨q, hN, hq, f, ?_, ?_⟩
  · change FreeCommRing.lift _ (FreeCommRing.of (affine K)) = _
    rw [FreeCommRing.lift_of, haffine]
  · intro r hr
    let j : s := ⟨r, hr⟩
    change f j.val = 0
    rw [← he j, map_sub]
    change FreeCommRing.lift (fun a => (counts a : ℤ)) ((left j).eval FreeCommRing.of) -
      FreeCommRing.lift (fun a => (counts a : ℤ)) ((right j).eval FreeCommRing.of) = 0
    rw [FieldExpressionCounts.eval_lift, FieldExpressionCounts.eval_lift,
      FieldExpressionCounts.eval_cast, FieldExpressionCounts.eval_cast, hcounts j, sub_self]

end DiamondIntegral.Section4.FieldFiniteCharacters
