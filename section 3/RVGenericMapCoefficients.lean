import «section 3».RVGenericFamilyCoefficients
import «section 3».ACFDependentFamilyCoefficients
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

/-- Normalized selectors and finitely many additional pure-field
relations have a common countable algebraically closed coefficient
field, even when their arities differ. -/
theorem rvGeneric_family_extra_coefficients {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n : ℕ} {ι δ : Type} [Finite ι] [Finite δ]
    (A : ι → Set (Fin n → M)) (hA : ∀ j, DefinableOverBase B (fun _ => .rv) (A j))
    (a : ι → Fin n → (CanonicalRV.RVSort M)ˣ) (L : List (Fin n))
    (α : δ → Type) (R : ∀ j, Set (α j → ModelResidue M))
    (hR : ∀ j, (Set.univ : Set (ModelResidue M)).Definable Language.ring (R j)) :
    ∃ E : Subfield (ModelResidue M), Cardinal.mk E ≤ Cardinal.aleph0 ∧ IsAlgClosed E ∧
      (∀ j k, k ≤ L.length → (E : Set (ModelResidue M)).Definable Language.ring
        {x : Fin n → ModelResidue M | rvNormalizedTuple (a j) x ∈ (L.take k).foldl rvGenericCoordinate (A j)}) ∧
      ∀ j, (E : Set (ModelResidue M)).Definable Language.ring (R j) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let J := (ι × Fin (L.length+1)) ⊕ δ
  let β : J → Type := fun j => j.elim (fun _ => Fin n) α
  let T : ∀ j : J, Set (β j → ModelResidue M) := fun j => match j with
    | .inl p => {x | rvNormalizedTuple (a p.1) x ∈ (L.take p.2.val).foldl rvGenericCoordinate (A p.1)}
    | .inr j => R j
  have hT : ∀ j : J, (Set.univ : Set (ModelResidue M)).Definable Language.ring (T j) := by
    intro j
    cases j with
    | inr j => exact hR j
    | inl p =>
      let V := (L.take p.2.val).foldl rvGenericCoordinate (A p.1)
      have ht : DefinableOverBase B (fun _ => .rv) V :=
        rvGenericCoordinate_fold_definableOverBase hc hs h00 B hsmall _ (hA p.1) _
      have hp : ∀ z ∈ V, ∀ i, iRV (z i) := by
        intro z hz i
        simpa only [sortEval,iRV] using ht.proper z hz i
      have hg : GammaGroundRawDefinable hc B V :=
        (gammaGroundRawDefinable_iff_sortedBase ht.proper).mpr ht
      exact gammaGroundRaw_residue_pullback_pure hκ hsmall V hg hp
        (fun i => (a p.1 i : CanonicalRV.RVSort M))
  obtain ⟨E,hE,hclosed,hET⟩ := acf_dependent_family_countable_algclosed_coefficients β T hT
  refine ⟨E,hE,hclosed,?_,fun j => hET (.inr j)⟩
  intro j k hk
  exact hET (.inl (j,⟨k,Nat.lt_succ_iff.mpr hk⟩))

end DiamondIntegral.Section3
