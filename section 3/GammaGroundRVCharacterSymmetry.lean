import «section 3».GammaGroundCharacterSymmetry
import «section 3».GammaGroundSyntaxBridge
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

/-- An actual original-Gamma-ground RV set is invariant under every
character twist fixing all original-ground RV points. -/
theorem gammaGroundRVSet_character_invariant {n : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) (u : Fin n → CanonicalRV.RVSort M) :
    u ∈ A.carrier ↔ (fun i => rvOriginalGroundCharacterTwistZero B χ (u i)) ∈ A.carrier := by
  have h := rvCharacterTwist_definableOverBase B χ hc (rvValues '' A.carrier) A.definable.toRVBase u
  change rvValues u ∈ rvValues '' A.carrier ↔
    rvValues (fun i => rvOriginalGroundCharacterTwistZero B χ (u i)) ∈ rvValues '' A.carrier at h
  simpa only [Set.mem_image,rvValues_injective.eq_iff,exists_eq_right] using h

/-- The same assertion for every finite tuple index, in the complete
raw-syntax API used for actual map graphs. -/
theorem gammaGroundRawRV_character_invariant {ι : Type} [Finite ι]
    (A : Set (ι → M)) (hA : GammaGroundRawDefinable hc B A)
    (hproper : ∀ z ∈ A, ∀ i, iRV (z i)) (u : ι → CanonicalRV.RVSort M) :
    (fun i => (u i).val) ∈ A ↔
      (fun i => (rvOriginalGroundCharacterTwistZero B χ (u i)).val) ∈ A := by
  letI := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T : Set (Fin (Fintype.card ι) → M) := {z | z ∘ e ∈ A}
  have ht : GammaGroundRawDefinable hc B T := hA.preimage_comp e
  have hp : ∀ z ∈ T, ∀ i, sortEval .rv (z i) := by
    intro z hz i
    have h := hproper (z ∘ e) hz (e.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,iRV,sortEval] using h
  have hn := (gammaGroundRawDefinable_iff_sortedBase hp).mp ht
  have hf := rvCharacterTwist_definableOverBase B χ hc T hn (u ∘ e.symm)
  simpa only [T,Set.mem_setOf_eq,Function.comp_def,Equiv.symm_apply_apply] using hf

end DiamondIntegral.Section3
