import «section 6».CoordinateFormRootControl

/-! Actual common bounded coordinate roots for all protected pieces
and every Gamma level. Every root lies in the original ambient set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_coordinate_measured_controlling_roots
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧
      (∀ i, CoordinateRootControl (G := G) R (C i).carrier) ∧
      CoordinateFormRootControl (G := G) R (gammaFormExtension ω) := by
  obtain ⟨R,N,hR,hForm⟩ := exists_coordinate_form_controlling_roots hc hs hsmall hv A hARV
    (gammaFormExtension ω) (gammaFormExtension_graph_definable ω)
  obtain ⟨Q,L,hQ,hControl⟩ := exists_finite_controlling_coordinate_roots hc hs hsmall hv A hARV C
  exact ⟨R.union Q,N+L,R.union_bound Q N L hR hQ,
    fun i => (hControl i).mono (fun _ hp => Or.inr hp),hForm.mono (fun _ hp => Or.inl hp)⟩

end DiamondIntegral.Section6
