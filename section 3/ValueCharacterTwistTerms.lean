import «section 3».ValueCharacterTwistPairs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

/-- Every correctly sorted term respects the partial original-ground
VF/RV symmetry. In particular all intermediate VF terms remain old-ground. -/
theorem rvCharacterPair_term {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (v w : α → M) (xs ys : Fin n → M)
    (hv : ∀ a, RVCharacterPair B χ (sα a) (v a) (w a))
    (hx : ∀ i, RVCharacterPair B χ (sn i) (xs i) (ys i))
    (t : LRV.Term (α ⊕ Fin n)) :
    ∀ σ, TmSort sα sn t = some σ → RVCharacterPair B χ σ
      (t.realize (Sum.elim v xs)) (t.realize (Sum.elim w ys)) := by
  induction t with
  | var z =>
    intro σ ht
    cases z with
    | inl a => cases Option.some.inj ht; exact hv a
    | inr i => cases Option.some.inj ht; exact hx i
  | func f ts ih =>
    intro σ ht
    obtain ⟨harg,rfl⟩ := (tmSort_func_iff sα sn f ts).mp ht
    exact rvCharacterPair_function B χ f _ _ (fun i => ih i _ (harg i))

/-- Equality is preserved and reflected, including RV equality. -/
theorem rvCharacterPair_equal {σ : SortTag} {u v u' v' : M}
    (hu : RVCharacterPair B χ σ u u') (hv : RVCharacterPair B χ σ v v') :
    u = v ↔ u' = v' := by
  cases σ with
  | vf => obtain ⟨a,rfl,rfl⟩ := hu; obtain ⟨b,rfl,rfl⟩ := hv; rfl
  | rv =>
    obtain ⟨a,rfl,rfl⟩ := hu
    obtain ⟨b,rfl,rfl⟩ := hv
    rw [← Subtype.ext_iff,← Subtype.ext_iff]
    exact (rvOriginalGroundCharacterTwistZero B χ).injective.eq_iff.symm

private theorem twistUnary (xs : Fin 1 → M) : xs = ![xs 0] := by
  funext i
  fin_cases i
  rfl
private theorem twistBinary (xs : Fin 2 → M) : xs = ![xs 0,xs 1] := by
  funext i
  fin_cases i <;> rfl

/-- Every language predicate respects the same partial symmetry. -/
theorem rvCharacterPair_relation {k : ℕ} (R : Rel k) (xs ys : Fin k → M)
    (h : ∀ i, RVCharacterPair B χ (Rel.argSort R i) (xs i) (ys i)) :
    Structure.RelMap (L := LRV) R xs ↔ Structure.RelMap (L := LRV) R ys := by
  cases R with
  | memVF =>
    obtain ⟨a,ha,ha'⟩ := h 0
    rw [twistUnary xs,twistUnary ys]
    change iVF (xs 0) ↔ iVF (ys 0)
    rw [ha,ha']
  | memRV =>
    obtain ⟨a,ha,ha'⟩ := h 0
    rw [twistUnary xs,twistUnary ys]
    change iRV (xs 0) ↔ iRV (ys 0)
    rw [ha,ha']
    exact iff_of_true a.property (rvOriginalGroundCharacterTwistZero B χ a).property
  | memUnits =>
    obtain ⟨a,ha,ha'⟩ := h 0
    rw [twistUnary xs,twistUnary ys]
    change iUnits (xs 0) ↔ iUnits (ys 0)
    rw [ha,ha']
    exact (rvOriginalGroundCharacterTwistZero_units B χ a).symm
  | rvLe =>
    obtain ⟨a,ha,ha'⟩ := h 0
    obtain ⟨b,hb,hb'⟩ := h 1
    rw [twistBinary xs,twistBinary ys]
    change iLe (xs 0) (xs 1) ↔ iLe (ys 0) (ys 1)
    rw [ha,ha',hb,hb']
    exact (rvOriginalGroundCharacterTwistZero_le B χ a b).symm

end DiamondIntegral.Section3
