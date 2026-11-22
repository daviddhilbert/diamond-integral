import «section 8».Jets
import «section 8».HmLocalized
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxConcreteComparisons
import FubiniTheorems.Comparison.RESRawComparisonEquivalence

/-! Classes of truncations and the jet classes ((z:coeff:change), second equality).

* `dcClass X ∈ K^μ̂ Var_ℂ / (linear actions)`: the class of a diagonal constructible object, i.e. of
  the constructible set with its diagonal `μ̂`-action (the library's `toVarietyRing`).
* `theta_diagonalRESClass`: `Θ` of the RES class of the descended set of `X` is `dcClass X`. So the
  class of the definable RES set of a truncation (`truncation_definable`) is sent by `Θ` to the
  class of its coefficient set with weights `k/m`.
* `truncClass m b q hX`: `Θ([A[m;β]]) [𝔸]^{-mΣβ} ∈ K^μ̂ Var_ℂ[[𝔸]⁻¹]` for one label pattern `q`.
* `jetObject f m`: the jet set of `IsJet` as a diagonal constructible object, weights `k/m`
  (`jetObject_domain`, `jetObject_weights`); `jetClass f m = dcClass (jetObject f m)`.
* `z_coeff_change_jets`: `Θ(𝒳̃_f[m]) = [𝒳_m] [𝔸]^{-md}`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm

local instance truncClassStructure : LRV.Structure Carrier := canonicalInterpret
local instance truncClassModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

/-- The class of a diagonal constructible object in `K^μ̂ Var_ℂ / (linear actions)`. -/
def dcClass (X : DiagonalConstructible.Object) : EquivariantVariety.ModifiedRing :=
  Ideal.Quotient.mk EquivariantVariety.linearActionIdeal
    (DiagonalConstructible.toVarietyRing (DiagonalConstructible.objectClass X))

/-- `Θ` of the RES class of the descended set of `X` is the class of `X`. -/
theorem theta_diagonalRESClass (X : DiagonalConstructible.Object) :
    theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround (diagonalRESClass X)) =
      dcClass X := by
  rw [theta_5_14_concrete_mk, rawVarietyComparison_apply]
  change Ideal.Quotient.mk _ (DiagonalConstructible.toVarietyRing (resToDiagonal (diagonalRESClass X))) = _
  rw [resToDiagonal_diagonalRESClass]
  rfl

variable {n l : ℕ}

/-- `[𝔸]^{-k}` in `K^μ̂ Var_ℂ[[𝔸]⁻¹]`. -/
def Linv (k : ℕ) : Rloc := ((Lunit⁻¹ : Rlocˣ) : Rloc) ^ k

/-- `Θ([A[m;β]]) [𝔸]^{-mΣβ}` for the label pattern `q`. -/
def truncClass (m : ℕ+) (b : Fin n → ℕ) (q : Fin l → ℤ) {X : Set (Fin (n + l) → Carrier)}
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) : Rloc :=
  algebraMap EquivariantVariety.ModifiedRing Rloc
      (dcClass (truncObject m b q hX (Fintype.equivFin (Idx b ⊕ Fin l)))) * Linv (∑ i, b i)

/-! ### Jets -/

variable {d : ℕ} (f : MvPolynomial (Fin d) ℂ)

/-- The enumeration of the jet coordinates `(i, k)`, `i ≤ d`, `k ≤ m`. -/
abbrev jetEnum (m : ℕ+) := Fintype.equivFin (Idx (bOne (d := d) m) ⊕ Fin 0)

/-- **The jet variety `𝒳_m`** with its `μ_m`-action, as a diagonal constructible object: the
coefficient set of the truncation of `𝒳_f` at level `m` and cutoffs `1`. -/
def jetObject (m : ℕ+) : DiagonalConstructible.Object :=
  truncObject m (bOne m) Fin.elim0 (rawMilnor_definableOver f) (jetEnum m)

theorem jetObject_domain (m : ℕ+) :
    (jetObject f m).domain = {x | IsJet f m (fun i k => x (jetEnum m (.inl ⟨i, k⟩)))} := by
  change (truncObject m (bOne m) Fin.elim0 (rawMilnor_definableOver f) (jetEnum m)).domain = _
  rw [truncObject_domain]
  ext x
  exact milnor_coeffSet f m (x ∘ jetEnum m)

/-- The coordinate `a_{i,k}` has weight `k/m`: `μ_m` acts by `s ↦ ζ s`. -/
theorem jetObject_weights (m : ℕ+) (i : Fin d) (k : Fin ((m : ℕ) + 1)) :
    (jetObject f m).weights (jetEnum m (.inl ⟨i, k⟩)) = lev m k := by
  change (truncObject m (bOne m) Fin.elim0 (rawMilnor_definableOver f) (jetEnum m)).weights _ = _
  rw [truncObject_weights]
  simp [stdWt]

/-- `[𝒳_m]`. -/
def jetClass (m : ℕ+) : EquivariantVariety.ModifiedRing := dcClass (jetObject f m)

/-- **(z:coeff:change), second equality.** `Θ(𝒳̃_f[m]) = [𝒳_m] [𝔸]^{-md}`. -/
theorem z_coeff_change_jets (m : ℕ+) :
    truncClass m (bOne (d := d) m) Fin.elim0 (rawMilnor_definableOver f) =
      algebraMap EquivariantVariety.ModifiedRing Rloc (jetClass f m) * Linv ((m : ℕ) * d) := by
  rw [truncClass, jetClass, jetObject]
  congr 2
  simp [bOne, Finset.sum_const, mul_comm]

end DiamondIntegral.Section8.Truncation
