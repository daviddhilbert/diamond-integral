import «section 6».BinaryMeasuredBaseRootIteration

/-! Complete two-dimensional proper preparation over the original
base: actual finite obstacles, terminating root iteration, and the
common protected preliminary preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_measured_tagged_preparation_with_base_displacement
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (j : Fin r) (hHead : ∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A P hPA ω,RVCoordinateDisplacement T.map 0 := by
  obtain ⟨R,N,hN,hControl,hForm⟩ := exists_coordinate_measured_controlling_roots hc hs hsmall hv A hARV P ω
  exact binary_measured_root_preparation_with_base_displacement h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A hA hAD hARV htag j hHead R hN P hPA hP hControl ω hLevels hForm

end DiamondIntegral.Section6
