import «section 3».RVGenericResidueSemantics
import «section 3».RVGenericFullFibreInvariance
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

/-- A common coefficient field for finitely many intermediate selectors
identifies their entire finite iteration with the actual residue generic. -/
theorem rvGenericCoordinate_fold_at_residue_generic {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (E : Subfield (ModelResidue M))
    (L : List (Fin n))
    (hR : ∀ k ≤ L.length, (E : Set (ModelResidue M)).Definable Language.ring
      {x : Fin n → ModelResidue M | rvNormalizedTuple a x ∈ (L.take k).foldl rvGenericCoordinate A})
    (x : Fin n → ModelResidue M) (hx : AlgebraicIndependent E x) :
    rvNormalizedTuple a x ∈ L.foldl rvGenericCoordinate A ↔ rvNormalizedTuple a x ∈ A := by
  induction L generalizing A with
  | nil => rfl
  | cons i L ih =>
    let D := rvGenericCoordinate A i
    have hD : DefinableOverBase B (fun _ => .rv) D :=
      rvGenericCoordinate_definableOverBase hc hs h00 B hsmall A hA i
    have hRD : ∀ k ≤ L.length, (E : Set (ModelResidue M)).Definable Language.ring
        {z : Fin n → ModelResidue M | rvNormalizedTuple a z ∈ (L.take k).foldl rvGenericCoordinate D} := by
      intro k hk
      simpa only [List.take_succ_cons,List.foldl_cons,D] using hR (k+1) (Nat.succ_le_succ hk)
    have h0 : (E : Set (ModelResidue M)).Definable Language.ring
        {z : Fin n → ModelResidue M | rvNormalizedTuple a z ∈ A} := by
      simpa using hR 0 (Nat.zero_le _)
    exact (ih D hD hRD).trans (rvGenericCoordinate_at_residue_generic hc h00 B A hA a E h0 x hx i)

end DiamondIntegral.Section3
