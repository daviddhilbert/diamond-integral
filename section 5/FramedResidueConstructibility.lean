import «section 5».PuiseuxResiduePresentation
import Section7.ResidueConstructibility

/-! Constructibility of normalized actual RV sets, retaining the displayed
coefficient field. In the concrete Puiseux presentation that field is C. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem normalized_residue_constructible {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : LRV.Substructure M)
    (E : Subfield (ModelResidue M)) (hE : residueParameterField B ≤ E) {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) (residueExtendedBase B E))
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, s i ∈ extendedCoefficients B E) :
    ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) E)), IsConstructible C ∧
      ∀ x : Fin n → ModelResidue M,
        x ∈ normalizedResidueSet A s ↔ fieldTuplePrime E x ∈ C := by
  letI : IsAlgClosed (SpecialTransformations.Milestone0.Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  exact field_definable_constructible E _ (normalizedResidueSet_definable hc B E hE A s hs)

/-- Transport pure-ring definability along a proved field equivalence.
All coefficients are in the displayed full coefficient field. -/
theorem ring_definable_preimage_equiv {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {n : ℕ} (D : Set (Fin n → L))
    (hD : (Set.univ : Set L).Definable Language.ring D) :
    (Set.univ : Set K).Definable Language.ring {x | (e ∘ x) ∈ D} := by
  rw [Set.definable_iff_exists_formula_sum] at hD ⊢
  obtain ⟨φ, hφ⟩ := hD
  let f : (Set.univ : Set L) ⊕ Fin n → (Set.univ : Set K) ⊕ Fin n :=
    Sum.map (fun a => ⟨e.symm a.val, trivial⟩) id
  refine ⟨φ.relabel f, ?_⟩
  ext x
  rw [Set.mem_setOf_eq, hφ]
  change φ.Realize (Sum.elim Subtype.val (e ∘ x)) ↔
    (φ.relabel f).Realize (Sum.elim Subtype.val x)
  rw [Formula.realize_relabel]
  let eL : K ≃[Language.ring] L := FirstOrder.Ring.languageEquivEquivRingEquiv.symm e
  have h := StrongHomClass.realize_formula eL φ
    (v := (Sum.elim Subtype.val x) ∘ f)
  have he : eL ∘ ((Sum.elim Subtype.val x) ∘ f) = Sum.elim Subtype.val (e ∘ x) := by
    funext i
    cases i with
    | inl a =>
      change e (e.symm a.val) = a.val
      exact e.apply_symm_apply _
    | inr i => rfl
  rw [he] at h
  exact h

namespace PuiseuxOriginal
local instance constructibilityModelStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

/-- Every normalized RV set in the concrete canonical model has actual
constructible complex coordinates. The earlier residue presentation fixes
the coefficient provenance rather than changing the definability base. -/
theorem complex_normalized_residue_constructible (B : LRV.Substructure Carrier) {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) (residueExtendedBase B ⊤))
    (s : Fin n → CanonicalRV.RVSort Carrier)
    (hs : ∀ i, s i ∈ extendedCoefficients B ⊤) :
    ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) (⊤ : Subfield ℂ))),
      IsConstructible C ∧ ∀ x : Fin n → ℂ,
        (complexResidueEquiv ∘ x) ∈ normalizedResidueSet A s ↔
          fieldTuplePrime (⊤ : Subfield ℂ) x ∈ C := by
  have hp := normalizedResidueSet_definable canonicalInterpret_isCanonical B ⊤ le_top A s hs
  have hd : (Set.univ : Set (ModelResidue Carrier)).Definable Language.ring
      (normalizedResidueSet A s) := hp
  exact field_definable_constructible (⊤ : Subfield ℂ) _
    (ring_definable_preimage_equiv complexResidueEquiv _ hd)

end PuiseuxOriginal
end DiamondIntegral.Section5
