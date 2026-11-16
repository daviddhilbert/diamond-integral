import «section 6».UnaryMeasuredRootIteration

/-! Actual common bounded roots for a finite protected family and all
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

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

theorem exists_unary_measured_controlling_roots
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    ∃ R : UnaryRootFamily A, ∃ N : ℕ, (∀ u, (R.fibre u).card ≤ N) ∧
      (∀ i, UnaryRootControl (G := G) R (C i).carrier) ∧
      UnaryFormRootControl (G := G) R (gammaFormExtension ω) := by
  obtain ⟨Q,hQ,hQControl⟩ := exists_unary_gamma_obstacles hc hv A (gammaFormExtension ω) (gammaFormExtension_graph_definable ω)
  obtain ⟨P,hP,hPControl⟩ := exists_finite_unary_obstacles hc hv C
  let U := Q ∪ P
  have hU : S.Definable₁ LRV (Subtype.val '' (U : Set (VF M))) := by
    change S.Definable₁ LRV (Subtype.val '' ((Q ∪ P : Finset (VF M)) : Set (VF M)))
    rw [Finset.coe_union,Set.image_union]
    exact hQ.union hP
  have hUC (i : Fin k) : UnaryObstacleControl (G := G) U (C i).carrier := by
    intro a ρ hAvoid x hx y hy u
    exact hPControl i a ρ (fun z hz => hAvoid z (Finset.mem_union_right Q hz)) x hx y hy u
  have hUG (γ : Gamma M) : UnaryObstacleControl (G := G) U
      {p | p ∈ A.carrier ∧ gammaFormExtension ω p = γ} := by
    intro a ρ hAvoid x hx y hy u
    exact hQControl γ a ρ (fun z hz => hAvoid z (Finset.mem_union_left P hz)) x hx y hy u
  let R := UnaryRootFamily.fromObstacles A U hU
  refine ⟨R,U.card,fun u => ?_,fun i => UnaryRootFamily.fromObstacles_control U hU _ (hUC i),?_⟩
  · apply Finset.card_le_card
    intro x hx
    exact ((R.mem_fibre u x).mp hx).2
  · exact unaryFormRootControl_of_levels R (gammaFormExtension ω)
      (fun γ => UnaryRootFamily.fromObstacles_control U hU _ (hUG γ))

theorem unary_measured_preparation_of_doublyBounded_tagged
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
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    Nonempty (UnaryMeasuredPreparation (G := G) A C hCA ω) := by
  obtain ⟨R,N,hBound,hControl,hForm⟩ := exists_unary_measured_controlling_roots hc hv A C ω
  exact UnaryRootFamily.exists_measured_prepared_process_of_bound h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A R hA hD hARV hTag hBound C hCA hC hControl ω hLevels hForm

end DiamondIntegral.Section6
