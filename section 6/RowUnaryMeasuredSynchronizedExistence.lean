import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowUnaryMeasuredSynchronizedFocusStep
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowUnaryMeasuredSynchronizedPreparation

/-! (Row-form version for Remark 6.20, translated from `UnaryMeasuredSynchronizedExistence`.)
 The actual unary measured preparation comes with a synchronized
permitted chain, including every protected narrow component. No chain
or root family is supplied as an extra preparation hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

theorem unary_measured_synchronized_preparation_of_doublyBounded_tagged_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier)
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ}) :
    ∃ T : UnaryMeasuredPreparationRow (G := G) A C hCA ω,
      SynchronizedCentripetalChain (G := G) (Fin k) A T.target T.map C := by
  obtain ⟨R,N,hBound,hControl,hForm⟩ := exists_unary_measured_controlling_roots_row hc hv A C ω
  exact UnaryRootFamily.exists_measured_synchronized_process_of_bound_row h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A R hA hD hARV hTag hBound C hCA hC hControl ω hLevels hForm


end DiamondIntegral.Section6
