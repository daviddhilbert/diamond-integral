import «section 6».BinaryMeasuredRootReduction
import «section 6».BinaryRootIteration

/-! Terminating actual binary measured root iteration. Every successor
retains the form and all protected maps while strictly decreasing the
uniform root bound. Empty roots invoke the actual measured terminal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_measured_preparation_of_root_bound {k : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (N : ℕ) : ∀ {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 2 r) S),
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier → IsRVPullback A.carrier →
      (∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) →
      ∀ (j : Fin r), (∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j) →
      ∀ R : CoordinateRootFamily A, R.Bound N →
      ∀ (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier),
      (∀ i, ProperInvariant S (P i).carrier) → (∀ i, CoordinateRootControl (G := G) R (P i).carrier) →
      ∀ ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) →
      CoordinateFormRootControl (G := G) R (gammaFormExtension ω) →
      Nonempty (MeasuredCoordinatePreparation (G := G) A P hPA ω) := by
  induction N with
  | zero =>
    intro r A hA hAD hARV htag j hHead R hN P hPA hP hControl ω hLevels hForm
    exact binary_measured_preparation_of_empty_coordinate_roots
      h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD hARV htag j hHead R
      (R.roots_empty_of_bound_zero hN) P hPA hP hControl ω hLevels hForm
  | succ N ih =>
    intro r A hA hAD hARV htag j hHead R hN P hPA hP hControl ω hLevels hForm
    obtain ⟨F⟩ := binary_measured_root_reduction_exists h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
      A hA hAD hARV htag j hHead R N hN P hPA hP hControl ω hLevels hForm
    let C (i) := (F.map.restrict (hPA i)).image
    have hCsub (i) : (C i).carrier ⊆ F.target.carrier := by
      rintro q ⟨p,hp⟩
      exact hp ▸ (F.map ⟨p.val,hPA i p.property⟩).property
    have hC (i) : ProperInvariant S (C i).carrier := by
      have h := (F.restrictions i).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
      exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
    have hLevelsF := F.special.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels F.form F.transport
    obtain ⟨T⟩ := ih F.target F.proper F.doublyBounded F.pullback F.tagged
      F.headTag F.head_tag F.roots F.bound C hCsub hC F.control F.form hLevelsF F.formControl
    exact ⟨T.precompose h00 P hPA F.map F.special F.restrictions hCsub ω F.form F.transport⟩

end DiamondIntegral.Section6
