import Section3.BallGeometry
import Section3.GammaParameters
import Section3.Coordinates

set_option backward.isDefEq.respectTransparency false

/-!
# §2.1: real coordinates, imaginary values and parameter bases

The language, VF field and RV quotient are those of pinned ACVF-QE.
`RVInfinity` includes the single element `rv(0)`; `RV` excludes it, as in
the manuscript's notation. Gamma is the quotient by equality of values,
not by equality of RV classes. The reusable parameter interface keeps
Gamma names separate from real VF/RV parameters.

These conventions need only ACVF. Characteristic zero, saturation and base
generation are additional hypotheses on the results that require them.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable (M : Type) [LRV.Structure M]

abbrev VF := VFType (M := M)
abbrev RVInfinity := CanonicalRV.RVSort M

variable [hM : M ⊨ Axioms.ACVF]

def rvZero : RVInfinity M := ⟨iRVZero, rv_zero_mem hM⟩

abbrev RV := {t : RVInfinity M // t ≠ rvZero M}
abbrev GammaInfinity := Values.GammaTop (M := M)
abbrev Gamma := Values.Gamma (M := M)
abbrev ParameterBase := GammaParameters.Base (M := M)

/-- The companion library's closure-generated interface. This is distinct
from generation as an LRV substructure in Lemma 2.11. -/
abbrev DclVFGenerated (B : ParameterBase M) := GammaParameters.VFGeneratedBase B
abbrev DclVFGammaGenerated (B : ParameterBase M) := GammaParameters.VFGammaGeneratedBase B

/-- Actual Gamma parameters are interpreted by full invariant RV preimages;
choosing an RV representative does not add a real parameter to this base. -/
abbrev DefinableOverBase := @GammaParameters.DefinableOverBase M _ hM

/-- Mixed ambient coordinates, including zero/infinity RV tags. -/
abbrev Mixed (n m : ℕ) := (Fin n → VF M) × (Fin m → RVInfinity M)

def rv : VF M → RVInfinity M := CanonicalRV.encodedRv

def tupleRV {n : ℕ} (a : Fin n → VF M) : Fin n → RVInfinity M := fun i => rv M (a i)

/-- Existing RV coordinates are retained, rather than saturated or forgotten. -/
def rvCoordinates {n m : ℕ} (p : Mixed M n m) := (tupleRV M p.1, p.2)

variable {M}

def vfFibre {n m : ℕ} (A : Set (Mixed M n m)) (t : Fin m → RVInfinity M) :=
  {a | (a, t) ∈ A}

@[simp] theorem rv_eq_zero_iff (a : VF M) : rv M a = rvZero M ↔ a = 0 := by
  rw [Subtype.ext_iff]
  change iRv a.val = iRVZero ↔ a = 0
  exact CanonicalRV.encodedRv_zero_iff a

@[simp] theorem rv_zero : rv M (0 : VF M) = rvZero M := (rv_eq_zero_iff _).mpr rfl

theorem rv_surjective : Function.Surjective (rv M) := CanonicalRV.encodedRv_surjective

theorem tupleRV_surjective {n : ℕ} : Function.Surjective (@tupleRV M _ hM n) := by
  intro t
  choose a ha using fun i => rv_surjective (t i)
  exact ⟨a, funext ha⟩

theorem rvCoordinates_surjective {n m : ℕ} :
    Function.Surjective (@rvCoordinates M _ hM n m) := by
  rintro ⟨t, s⟩
  obtain ⟨a, ha⟩ := tupleRV_surjective t
  exact ⟨(a, s), Prod.ext ha rfl⟩

@[simp] theorem rv_fibre_zero : (rv M) ⁻¹' {rvZero M} = {(0 : VF M)} := by
  ext a
  exact rv_eq_zero_iff a

def vfValue (a : VF M) : GammaInfinity M := Values.vrv (rv M a)

theorem vfValue_surjective : Function.Surjective (vfValue (M := M)) :=
  Values.vrv_surjective.comp rv_surjective

@[simp] theorem vfValue_eq_infinity_iff (a : VF M) :
    vfValue a = Values.infinity (M := M) ↔ a = 0 := by
  rw [vfValue, Values.vrv_eq_infinity_iff]
  exact CanonicalRV.encodedRv_zero_iff a

/-- A nonzero VF point has an actual finite Gamma value. -/
def finiteValue (a : VF M) (ha : a ≠ 0) : Gamma M :=
  ⟨vfValue a, fun he => ha ((vfValue_eq_infinity_iff a).mp he)⟩

/-- This bridge explicitly reverses the paper's additive valuation order. -/
theorem vfValue_eq_iff {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (VF M) Γ₀)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) (a b : VF M) :
    vfValue a = vfValue b ↔ v a = v b :=
  Values.vf_value_eq_iff v hv a b

/-- VF generation implies (VF,Gamma) generation without adjoining names. -/
theorem dclVFGenerated_dclVFGammaGenerated {B : ParameterBase M} (hB : DclVFGenerated M B) :
    DclVFGammaGenerated M B := by
  obtain ⟨A, hAB, hA, hgen⟩ := hB
  exact ⟨A, ∅, hAB, Set.empty_subset _, hA, hgen⟩

end DiamondIntegral.Section2
