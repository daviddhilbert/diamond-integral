import «section 3».ValueCharacterTwistDefinable
import «section 3».GammaGroundSortedSyntax
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

def gammaCodeCharacterTwist (c : Code (M := M)) : Code (M := M) :=
  ⟨rvOriginalGroundCharacterTwistZero B χ c.val,by
    intro h
    have he : rvOriginalGroundCharacterTwistZero B χ c.val = 0 :=
      Subtype.ext (h.trans RVOperations.zero_val.symm)
    have hc : c.val = 0 := (rvOriginalGroundCharacterTwistZero B χ).injective
      (he.trans (rvOriginalGroundCharacterTwistZero_zero B χ).symm)
    exact c.property ((congrArg Subtype.val hc).trans RVOperations.zero_val)⟩

theorem gammaCodeCharacterTwist_value (c : Code (M := M)) :
    value (gammaCodeCharacterTwist B χ c) = value c := by
  apply Subtype.ext
  exact rvOriginalGroundCharacterTwistZero_value B χ c.val

/-- All original real and Gamma parameters are respected. Gamma code
representatives may move, and the full invariant preimage removes them. -/
theorem rvCharacterTwist_definableOverBase (hc : CanonicalStructure.IsCanonical (M := M))
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (u : Fin n → CanonicalRV.RVSort M) :
    (fun i => (u i).val) ∈ A ↔
      (fun i => (rvOriginalGroundCharacterTwistZero B χ (u i)).val) ∈ A := by
  obtain ⟨k,γ,_,R,hRA⟩ := hA
  let T : Set (Fin (k+n) → M) := {z |
    ((fun i => z (Fin.castAdd n i)),(fun i => z (Fin.natAdd k i))) ∈ R.carrier}
  have hd : B.real.Definable LRV T := by
    have h := R.definable
    rw [canonical_normalize_eq hc] at h
    exact h.preimage_comp (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k+n))
  have hp : ∀ z ∈ T, ∀ i, sortEval .rv (z i) := by
    intro z hz i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (R.proper _ hz).1 j |>.1
    · exact (R.proper _ hz).2 j
  have hd' := raw_definableOver_sorted hc B.real (fun _ => .rv) T hd hp
  let c := representatives γ
  let d := fun i => gammaCodeCharacterTwist B χ (c i)
  let t : Fin (k+n) → CanonicalRV.RVSort M := Fin.append (fun i => (c i).val) u
  have hf := rvCharacterTwist_definableOver B χ T hd' t
  have hrow (a : Fin k → CanonicalRV.RVSort M) (b : Fin n → CanonicalRV.RVSort M) :
      (fun i => (Fin.append a b i).val) ∈ T ↔
        ((fun i => (a i).val),(fun i => (b i).val)) ∈ R.carrier := by
    change ((fun i => (Fin.append a b (Fin.castAdd n i)).val),
      (fun i => (Fin.append a b (Fin.natAdd k i)).val)) ∈ R.carrier ↔ _
    simp only [Fin.append_left,Fin.append_right]
  have ht : (fun i => rvOriginalGroundCharacterTwistZero B χ (t i)) =
      Fin.append (fun i => (d i).val) (fun i => rvOriginalGroundCharacterTwistZero B χ (u i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [t,Fin.append_left,d,gammaCodeCharacterTwist]
    · simp only [t,Fin.append_right]
  change (fun i => (t i).val) ∈ T ↔
    (fun i => ((fun j => rvOriginalGroundCharacterTwistZero B χ (t j)) i).val) ∈ T at hf
  rw [ht] at hf
  change (fun i => (Fin.append (fun j => (c j).val) u i).val) ∈ T ↔ _ at hf
  rw [hrow,hrow] at hf
  have hcd : values c = values d := by
    funext i
    exact (gammaCodeCharacterTwist_value B χ (c i)).symm
  rw [← hRA]
  change (rawTuple c,(fun i => (u i).val)) ∈ R.carrier ↔
    (rawTuple c,(fun i => (rvOriginalGroundCharacterTwistZero B χ (u i)).val)) ∈ R.carrier
  exact hf.trans (R.invariant c d hcd _).symm

end DiamondIntegral.Section3
