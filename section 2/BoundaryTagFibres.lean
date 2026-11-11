import «section 2».CoordinateBoundaryFamily

/-! The uniform raw family agrees with the actual finite unary boundary
over each tuple of fixed VF coordinates. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem coordinateBoundaryPairs_at_iff {n : ℕ} (A : Set (Fin (n+1) → M)) (i : Fin (n+1))
    (a : Fin n → M) (t : RVInfinity M) :
    Fin.snoc a t.val ∈ coordinateBoundaryPairs A i ↔
      (∀ j, iVF (a j)) ∧ t ∈ scalarRVBoundary (rawCoordinateSection A i a) := by
  have hsort : (Fin.snoc a t.val : Fin (n+1) → M) ∈
      GammaParameters.sortedUniverse (boundaryParameterSort n) ↔ ∀ j, iVF (a j) := by
    change (Fin.snoc a t.val : Fin (n+1) → M) ∈
      GammaParameters.sortedUniverse (Fin.lastCases .rv (fun _ : Fin n => .vf)) ↔ ∀ j, iVF (a j)
    rw [sorted_init_last_iff]
    simp only [Fin.init_snoc,Fin.snoc_last]
    change ((∀ j, iVF (a j)) ∧ iRV t.val) ↔ ∀ j, iVF (a j)
    exact and_iff_left t.property
  change (_ ∧ (∃ x, iVF x ∧ iRv x = (Fin.snoc a t.val : Fin (n+1) → M) (Fin.last n) ∧
      Fin.insertNth i x (Fin.init (Fin.snoc a t.val : Fin (n+1) → M)) ∈ A) ∧
    (∃ y, iVF y ∧ iRv y = (Fin.snoc a t.val : Fin (n+1) → M) (Fin.last n) ∧
      Fin.insertNth i y (Fin.init (Fin.snoc a t.val : Fin (n+1) → M)) ∉ A)) ↔ _
  rw [hsort]
  simp only [Fin.init_snoc,Fin.snoc_last]
  constructor
  · rintro ⟨ha,⟨x,hxVF,hxrv,hxA⟩,y,hyVF,hyrv,hyA⟩
    exact ⟨ha,⟨⟨x,hxVF⟩,hxA,Subtype.ext hxrv⟩,⟨⟨y,hyVF⟩,hyA,Subtype.ext hyrv⟩⟩
  · rintro ⟨ha,⟨x,hxA,hxt⟩,y,hyA,hyt⟩
    exact ⟨ha,⟨x.val,x.property,congrArg Subtype.val hxt,hxA⟩,
      y.val,y.property,congrArg Subtype.val hyt,hyA⟩

theorem coordinateBoundaryPairs_finite_tags (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin (n+1) → M)) (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (i : Fin (n+1)) (a : Fin n → M) (ha : ∀ j, iVF (a j)) :
    {t : RVInfinity M | Fin.snoc a t.val ∈ coordinateBoundaryPairs A i}.Finite := by
  have hsection := coordinate_section_definable B i a ha A hA
  convert lemma_2_35_unary_finite (tupleBase B a) (rawCoordinateSection A i a) hsection using 1
  ext t
  exact (coordinateBoundaryPairs_at_iff A i a t).trans (and_iff_right ha)

end DiamondIntegral.Section2
