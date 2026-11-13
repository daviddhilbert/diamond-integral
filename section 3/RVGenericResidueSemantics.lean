import «section 3».GammaGroundRVCoordinateRows
import «section 3».RVResidueNormalizedPoints
import «section 3».ACFIndependentDiagonalScaling
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The same-ground infinite-row selector agrees with actual residue
genericity. The coefficient field is used only to test the normalized
relation; it is not added to the original ground. -/
theorem rvGenericCoordinate_at_residue_generic
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ => .rv) A)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (E : Subfield (ModelResidue M))
    (hR : (E : Set (ModelResidue M)).Definable Language.ring
      {x : Fin n → ModelResidue M | rvNormalizedTuple a x ∈ A})
    (x : Fin n → ModelResidue M) (hx : AlgebraicIndependent E x) (i : Fin n) :
    rvNormalizedTuple a x ∈ rvGenericCoordinate A i ↔ rvNormalizedTuple a x ∈ A := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero h00
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let R : Set (Fin n → ModelResidue M) := {z | rvNormalizedTuple a z ∈ A}
  let p := rvNormalizedTuple a x
  have hx0 : ∀ j, x j ≠ 0 := algebraicallyIndependent_coordinate_ne_zero E x hx
  have hp : ∀ j, NonzeroRV (p j) := fun j => rvNormalizedPoint_nonzero (a j) (x j) (hx0 j)
  have hps : ∀ j, sortEval .rv (p j) := by
    intro j
    simpa only [sortEval,iRV] using (hp j).1
  change p ∈ rvGenericCoordinate A i ↔ p ∈ A
  rw [mem_rvGenericCoordinate_iff A i p hps,and_iff_right (hp i)]
  have hfield := acf_generic_coordinate_side_infinite E R hR x hx i
  have hlift (P : Set (ModelResidue M)) (hP : P.Infinite) (Q : M → Prop)
      (hQ : ∀ z ∈ P, Q (rvNormalizedPoint (a i) z).val) :
      {w | SameScalar w (p i) ∧ Q w}.Infinite := by
    have hi := (hP.diff (Set.finite_singleton 0)).image
      (rvNormalizedPoint_raw_injective (a i)).injOn
    apply hi.mono
    rintro w ⟨z,hz,rfl⟩
    refine ⟨rvNormalizedPoint_sameScalar (a i) z (x i) ?_ (hx0 i),hQ z hz.1⟩
    simpa only [Set.mem_singleton_iff] using hz.2
  constructor
  · intro hi
    by_contra hm
    have hneg := hlift {z | Function.update x i z ∉ R} (hfield.2 hm)
      (fun w => Function.update p i w ∉ A) (by
        intro z hz
        change rvNormalizedTuple a (Function.update x i z) ∉ A at hz
        rw [rvNormalizedTuple_update] at hz
        exact hz)
    rcases gammaGroundRV_coordinate_row_finite_or_cofinite hc B A hA p i (hp i) with hf | hf
    · exact hi hf
    · exact hneg hf
  · intro hm
    exact hlift {z | Function.update x i z ∈ R} (hfield.1 hm)
      (fun w => Function.update p i w ∈ A) (by
        intro z hz
        change rvNormalizedTuple a (Function.update x i z) ∈ A at hz
        rw [rvNormalizedTuple_update] at hz
        exact hz)

end DiamondIntegral.Section3
