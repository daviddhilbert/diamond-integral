import «section 3».ValueCharacterTwistFormulas
import Section3.SortedTuples
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

/-- Every actual old-ground parameter is fixed in its declared sort. -/
theorem rvCharacterPair_ground (σ : SortTag) (u : M)
    (hs : sortEval σ u) (hu : u ∈ B.real) : RVCharacterPair B χ σ u u := by
  have hd : DefinableClosureAtBase B σ u :=
    real_definableAtBase B σ {u} (definableClosureAt_of_mem hu hs)
  cases σ with
  | vf => exact ⟨⟨⟨u,hs⟩,hd⟩,rfl,rfl⟩
  | rv =>
    refine ⟨⟨u,hs⟩,rfl,?_⟩
    exact (congrArg Subtype.val
      (rvOriginalGroundCharacterTwistZero_fixes_ground B χ ⟨u,hs⟩ hd)).symm

/-- Every RV relation definable over the original real base is
invariant, with no assumption about an extension to the whole VF sort. -/
theorem rvCharacterTwist_definableOver {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOver B.real (fun _ => .rv) A) (u : Fin n → CanonicalRV.RVSort M) :
    (fun i => (u i).val) ∈ A ↔
      (fun i => (rvOriginalGroundCharacterTwistZero B χ (u i)).val) ∈ A := by
  obtain ⟨p,φ,hw,he⟩ := hA
  have hp := fun i => rvCharacterPair_ground B χ (p.sorts i) (p.values i)
    (p.sorted i) (p.mem_base i)
  have hx : ∀ i, RVCharacterPair B χ .rv (u i).val
      (rvOriginalGroundCharacterTwistZero B χ (u i)).val := fun i => ⟨u i,rfl,rfl⟩
  have hf := rvCharacterPair_formula B χ p.sorts (fun _ => .rv) p.values p.values
    _ _ hp hx φ hw
  rw [he]
  exact and_congr (iff_of_true (fun i => (u i).property)
    (fun i => (rvOriginalGroundCharacterTwistZero B χ (u i)).property)) hf

end DiamondIntegral.Section3
