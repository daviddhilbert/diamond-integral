import «section 6».RelativeCorrespondencePolynomials

/-! Restrict a fibre bijection to its exact inactive-coordinate
diagonal. Pointwise equality on the full prescribed fibres preserves
both unique-existence clauses, including the inverse clause. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open Classical
open SpecialTransformations.Section7
namespace DiamondIntegral.Section6
variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G] {n m : ℕ}

theorem fibreBijection_congr_on_fibres (v : Valuation K G)
    {A B : Set ((Fin n → K) × (Fin m → K))}
    {t : Fin n → RVCalc.RV v} {s : Fin m → RVCalc.RV v}
    (h : FibreBijection v A t s)
    (he : ∀ a ∈ RVFibre v t,∀ b ∈ RVFibre v s,(a,b) ∈ A ↔ (a,b) ∈ B) :
    FibreBijection v B t s := by
  constructor
  · intro a ha
    apply (existsUnique_congr (fun b => and_congr_right (fun hb => he a ha b hb))).mp
    exact h.1 a ha
  · intro b hb
    apply (existsUnique_congr (fun a => and_congr_right (fun ha => he a ha b hb))).mp
    exact h.2 b hb

theorem fibreBijection_restrict_inactive_diagonal (v : Valuation K G)
    {A : Set ((Fin n → K) × (Fin n → K))}
    {t s : Fin n → RVCalc.RV v} (i : Fin n) (h : FibreBijection v A t s)
    (hFixed : ∀ a ∈ RVFibre v t,∀ b ∈ RVFibre v s,(a,b) ∈ A → ∀ j,j ≠ i → b j = a j) :
    FibreBijection v {p | p ∈ A ∧ ∀ j,j ≠ i → p.2 j = p.1 j} t s := by
  apply fibreBijection_congr_on_fibres v h
  intro a ha b hb
  exact ⟨fun hA => ⟨hA,hFixed a ha b hb hA⟩,And.left⟩

end DiamondIntegral.Section6
