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
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration

/-! (Row-form version for Remark 6.20, translated from `UnaryMeasuredObstacles`.)
 Actual common bounded roots for a finite protected family and all
Gamma levels, followed by the terminating measured root construction.
No controlling roots or finite bound is a premise of the export. -/

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

theorem exists_unary_measured_controlling_roots_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (ω : RowFormOn A qR) :
    ∃ R : UnaryRootFamily A, ∃ N : ℕ, (∀ u, (R.fibre u).card ≤ N) ∧
      (∀ i, UnaryRootControl (G := G) R (C i).carrier) ∧
      UnaryFormRootControlRow (G := G) R (rowFormExtension ω) := by
  obtain ⟨Q,hQ,hQControl⟩ := exists_unary_gamma_obstacles_row hc hv A (rowFormExtension ω) (rowFormExtension_graph_definable ω)
  obtain ⟨P,hP,hPControl⟩ := exists_finite_unary_obstacles hc hv C
  let U := Q ∪ P
  have hU : S.Definable₁ LRV (Subtype.val '' (U : Set (VF M))) := by
    change S.Definable₁ LRV (Subtype.val '' ((Q ∪ P : Finset (VF M)) : Set (VF M)))
    rw [Finset.coe_union,Set.image_union]
    exact hQ.union hP
  have hUC (i : Fin k) : UnaryObstacleControl (G := G) U (C i).carrier := by
    intro a ρ hAvoid x hx y hy u
    exact hPControl i a ρ (fun z hz => hAvoid z (Finset.mem_union_right Q hz)) x hx y hy u
  have hUG (γ : Set (rawRVSpace (M := M) qR).Carrier) : UnaryObstacleControl (G := G) U
      {p | p ∈ A.carrier ∧ rowFormExtension ω p = γ} := by
    intro a ρ hAvoid x hx y hy u
    exact hQControl γ a ρ (fun z hz => hAvoid z (Finset.mem_union_left P hz)) x hx y hy u
  let R := UnaryRootFamily.fromObstacles A U hU
  refine ⟨R,U.card,fun u => ?_,fun i => UnaryRootFamily.fromObstacles_control U hU _ (hUC i),?_⟩
  · apply Finset.card_le_card
    intro x hx
    exact ((R.mem_fibre u x).mp hx).2
  · exact unaryFormRootControl_of_levels_row R (rowFormExtension ω)
      (fun γ => UnaryRootFamily.fromObstacles_control U hU _ (hUG γ))

theorem unary_measured_preparation_of_doublyBounded_tagged_row
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
    Nonempty (UnaryMeasuredPreparationRow (G := G) A C hCA ω) := by
  obtain ⟨R,N,hBound,hControl,hForm⟩ := exists_unary_measured_controlling_roots_row hc hv A C ω
  exact UnaryRootFamily.exists_measured_prepared_process_of_bound_row h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A R hA hD hARV hTag hBound C hCA hC hControl ω hLevels hForm

end DiamondIntegral.Section6
