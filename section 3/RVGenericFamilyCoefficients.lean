import «section 3».GammaGroundRawResiduePurity
import «section 3».RVGenericFullFibreInvariance
import «section 3».RVResidueNormalizedPoints
import «section 3».ACFFiniteFamilyCoefficients
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

/-- All intermediate selectors of finitely many normalized RV relations
have one countable algebraically closed coefficient field. Their original
Gamma ground and all full value-code preimages are retained. -/
theorem rvGeneric_family_countable_coefficients {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n : ℕ} {ι : Type} [Finite ι]
    (A : ι → Set (Fin n → M)) (hA : ∀ j, DefinableOverBase B (fun _ => .rv) (A j))
    (a : ι → Fin n → (CanonicalRV.RVSort M)ˣ) (L : List (Fin n)) :
    ∃ E : Subfield (ModelResidue M), Cardinal.mk E ≤ Cardinal.aleph0 ∧ IsAlgClosed E ∧
      ∀ j k, k ≤ L.length → (E : Set (ModelResidue M)).Definable Language.ring
        {x : Fin n → ModelResidue M | rvNormalizedTuple (a j) x ∈ (L.take k).foldl rvGenericCoordinate (A j)} := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let R (p : ι × Fin (L.length+1)) : Set (Fin n → ModelResidue M) :=
    {x | rvNormalizedTuple (a p.1) x ∈ (L.take p.2.val).foldl rvGenericCoordinate (A p.1)}
  have hR : ∀ p, (Set.univ : Set (ModelResidue M)).Definable Language.ring (R p) := by
    intro p
    let T := (L.take p.2.val).foldl rvGenericCoordinate (A p.1)
    have ht : DefinableOverBase B (fun _ => .rv) T :=
      rvGenericCoordinate_fold_definableOverBase hc hs h00 B hsmall _ (hA p.1) _
    have hp : ∀ z ∈ T, ∀ i, iRV (z i) := by
      intro z hz i
      simpa only [sortEval,iRV] using ht.proper z hz i
    have hg : GammaGroundRawDefinable hc B T :=
      (gammaGroundRawDefinable_iff_sortedBase ht.proper).mpr ht
    exact gammaGroundRaw_residue_pullback_pure hκ hsmall T hg hp
      (fun i => (a p.1 i : CanonicalRV.RVSort M))
  obtain ⟨E,hE,hclosed,hER⟩ := acf_finite_family_countable_algclosed_coefficients R hR
  refine ⟨E,hE,hclosed,?_⟩
  intro j k hk
  exact hER (j,⟨k,Nat.lt_succ_iff.mpr hk⟩)

end DiamondIntegral.Section3
