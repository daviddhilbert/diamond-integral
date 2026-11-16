import «section 6».BinaryMeasuredPreparation
import «section 6».FiniteProperCovers

/-! The binary measured preparation construction under the actual finite
partition hypotheses of 6.21. Properness of the whole ambient and open
global Gamma levels are derived from its finite proper pieces. The
additional category-valued lifting conclusion is separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

theorem binary_measured_partition_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 2 r → Gamma M) (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph)) := by
  have hA := properInvariant_of_finite_cover h00 hc hκ hs hv A C hCA hC hCover
  have hExt (p : Mixed M 2 r) (hp : p ∈ A.carrier) :
      gammaFormExtension (gammaFormMap A ω hGraph) p = ω p := by
    rw [gammaFormExtension_at _ (⟨p,hp⟩ : A),gammaFormMap_at]
  have hGlobal := gamma_levels_open_of_finite_cover hv A C hCA hCover ω hLevels
  have hOpen (u γ) : IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧
      gammaFormExtension (gammaFormMap A ω hGraph) (a,u) = γ} := by
    convert hGlobal u γ using 1
    ext a
    constructor
    · rintro ⟨ha,hγ⟩
      exact ⟨ha,(hExt (a,u) ha).symm.trans hγ⟩
    · rintro ⟨ha,hγ⟩
      exact ⟨ha,(hExt (a,u) ha).trans hγ⟩
  exact binary_measured_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hCA hC
    (gammaFormMap A ω hGraph) hOpen

end DiamondIntegral.Section6
