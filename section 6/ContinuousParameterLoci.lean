import «section 6».FrozenUnaryRVDataPreparation
import Section8.ContinuityFamilies

/-! Definable parameter loci on which an entire VF function is
continuous. Parameters may include VF values and RV labels. This is
an admissibility condition for finite formula-choice uniformization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {ι : Type} [Finite ι] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def continuousParameterLocus (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) : Set (ι → M) :=
  {t | ∀ x ∈ vfRawUniverse n,Sum.elim t x ∈ continuousInputsFamily R}

theorem continuousParameterLocus_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (continuousParameterLocus R) := by
  have hBad := ((vfRawUniverse_definable S n).preimage_comp (Sum.inr : Fin n → ι ⊕ Fin n)).inter
    (continuousInputsFamily_definable hR).compl
  convert (hBad.exists_of_finite).compl using 1
  ext t
  change (∀ x,x ∈ vfRawUniverse n → Sum.elim t x ∈ continuousInputsFamily R) ↔
    ¬ ∃ x : Fin n → M,x ∈ vfRawUniverse n ∧ Sum.elim t x ∉ continuousInputsFamily R
  simp only [not_exists,not_and,not_not]

theorem mem_continuousParameterLocus_iff
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (t : ι → M)
    (f : (Fin n → VF M) → Fin m → VF M)
    (hSection : {z : Fin n ⊕ Fin m → M | Sum.elim t z ∈ R}=vfGraph f) :
    t ∈ continuousParameterLocus R ↔ Continuous f := by
  constructor
  · intro h
    apply continuous_iff_continuousAt.mpr
    intro x
    have hC := h (vfValues x) (fun i => (x i).property)
    change vfValues x ∈ continuousInputs {z | Sum.elim t z ∈ R} at hC
    rw [hSection,mem_continuousInputs_iff hv] at hC
    exact hC
  · intro h x hx
    let a : Fin n → VF M := fun i => ⟨x i,hx i⟩
    change vfValues a ∈ continuousInputs {z | Sum.elim t z ∈ R}
    rw [hSection,mem_continuousInputs_iff hv]
    exact h.continuousAt

end DiamondIntegral.Section6
