import «section 6».InvariantHull

/-! R109: exact factorization of a released annular piece through the
projection forgetting its newly free VF coordinate. These set equalities
precede the remaining lower-dimensional preparation construction. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ} {X : Type*}

theorem AlphaInvariant.coordinate_shift_iff {α : Fin n → Gamma M}
    {A : Set (Fin n → VF M)} (hA : AlphaInvariant α A)
    (a : Fin n → VF M) (j : Fin n) (d : VF M) (hd : (α j).val < vfValue d) :
    Function.update a j (a j + d) ∈ A ↔ a ∈ A := by
  apply hA
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self,add_sub_cancel_left] using hd
  · simpa only [Function.update_of_ne hi,sub_self,valueHom_eq_value] using gamma_lt_value_zero (α i)

def AnnularBundle (ρ ρ' : X → Gamma M) : Set (VF M × X) :=
  {p | (ρ p.2).val < vfValue p.1 ∧ vfValue p.1 ≤ (ρ' p.2).val}

def FocusBase (A : Set (VF M × X)) (focus : X → VF M) : Set X :=
  {x | (focus x,x) ∈ A}

def ReleasedPiece (A : Set (VF M × X)) (focus : X → VF M)
    (ρ ρ' : X → Gamma M) : Set (VF M × X) :=
  {p | p ∈ AnnularBundle ρ ρ' ∧ (focus p.2 + p.1,p.2) ∈ A}

theorem releasedPiece_factorization
    (A : Set (VF M × X)) (focus : X → VF M) (α ρ ρ' : X → Gamma M)
    (hαρ : ∀ x, α x ≤ ρ x)
    (hA : ∀ x a b, (α x).val < vfValue (a-b) → ((a,x) ∈ A ↔ (b,x) ∈ A)) :
    ReleasedPiece A focus ρ ρ' = AnnularBundle ρ ρ' ∩ Prod.snd ⁻¹' FocusBase A focus := by
  ext p
  change (p ∈ AnnularBundle ρ ρ' ∧ (focus p.2+p.1,p.2) ∈ A) ↔
    p ∈ AnnularBundle ρ ρ' ∧ (focus p.2,p.2) ∈ A
  constructor
  · rintro ⟨hp,hmem⟩
    have hd : (α p.2).val < vfValue ((focus p.2+p.1)-focus p.2) := by
      simpa only [add_sub_cancel_left] using
        (show (α p.2).val ≤ (ρ p.2).val from hαρ p.2).trans_lt hp.1
    exact ⟨hp,(hA p.2 _ _ hd).mp hmem⟩
  · rintro ⟨hp,hmem⟩
    have hd : (α p.2).val < vfValue ((focus p.2+p.1)-focus p.2) := by
      simpa only [add_sub_cancel_left] using
        (show (α p.2).val ≤ (ρ p.2).val from hαρ p.2).trans_lt hp.1
    exact ⟨hp,(hA p.2 _ _ hd).mpr hmem⟩

theorem annularBundle_rv_saturated (ρ ρ' : X → Gamma M)
    (x : X) (a b : VF M) (hrv : rv M a = rv M b) :
    (a,x) ∈ AnnularBundle ρ ρ' ↔ (b,x) ∈ AnnularBundle ρ ρ' := by
  have he : vfValue a = vfValue b := congrArg Values.vrv hrv
  change ((ρ x).val < vfValue a ∧ vfValue a ≤ (ρ' x).val) ↔
    ((ρ x).val < vfValue b ∧ vfValue b ≤ (ρ' x).val)
  rw [he]

end DiamondIntegral.Section6
