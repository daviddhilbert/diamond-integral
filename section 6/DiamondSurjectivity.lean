import «section 6».DiamondGroupoid
import «section 6».DiamondLift
import «section 6».DiamondGrothendieck
import «section 6».NormalizedOrderedUnaryChains
import «section 6».MeasuredExistenceFieldBase
import «section 6».ZeroArityMeasuredPreparation
import «section 6».GammaFormMaps

/-! Corollary 6.37 (`L:sur:c`), surjectivity: every object of `μVF^◇[n]` over a
VF-generated base is isomorphic in `μVF^◇[n]` to the lift `μL(U, π)` of a
doubly bounded measured RV object, so the lift classes exhaust `K_+ μVF^◇[n]`.

Section 6's special covariant chains factor into relatively unary proper
covariant homeomorphisms: regularization changes no VF coordinate, a
centripetal step changes only its own coordinate, and the zero-centred
normalization factors through `RetainedUnaryHomeChain`
(`ZeroCenteredData.relatively_unary_chain`). Lemma 6.21, applied to the single
piece `A`, gives such a chain onto a lift with the form preserved, and the
chain has unit derivative at VF-generic points. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondSurjectivity
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondGrothendieck

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Retained relatively unary chains factor into relatively unary proper
covariant homeomorphisms. -/
theorem retained_factor {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {π : Fin r → Fin s}
    (F : RetainedUnaryHomeChain (G := G) S f π) : UnaryFactorization G A B f := by
  induction F with
  | identity A _ => exact UnaryFactorization.id A
  | unary j home relative _ _ => exact UnaryFactorization.step home (Or.inr ⟨j, j, VFUnaryRelativeAt.relativelyUnary relative⟩)
  | comp _ _ ihf ihs => exact UnaryFactorization.comp ihf ihs

/-- Special covariant chains factor into relatively unary proper covariant
homeomorphisms. -/
theorem special_factor (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (H : SpecialCovariantChain (G := G) A B f) : UnaryFactorization G A B f := by
  induction H with
  | identity A _ => exact UnaryFactorization.id A
  | regularize A hA hVF =>
    refine UnaryFactorization.step
      (regularization_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ A hA hVF) ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr ⟨⟨0, hn⟩, ⟨0, hn⟩, VFUnaryRelativeAt.relativelyUnary (fun _ _ _ => rfl)⟩
  | centripetal A D =>
    refine UnaryFactorization.step (D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ)
      (Or.inr ⟨D.coordinate, D.coordinate, VFUnaryRelativeAt.relativelyUnary (fun p j hj => ?_)⟩)
    change (D.point p.val).1 j = p.val.1 j
    exact Function.update_of_ne hj _ _
  | zeroCentered A D =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact UnaryFactorization.step (D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ) (Or.inl hn)
    · obtain ⟨F, _⟩ := D.relatively_unary_chain (G := G) h00 hc linear hκ hs hv hsmall hΓ hn
      exact retained_factor F
  | comp _ _ ihf ihg => exact UnaryFactorization.comp ihf ihg

/-- The measured RV object carried by Lemma 6.21's lift data. -/
def liftDataObject {r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (L : MeasuredRVLiftData (G := G) A ω) : MeasuredRVObject (M := M) S n where
  object := L.object
  finiteVolume := L.finiteVolume
  nonzero u i h := L.valueBounded.nonzero (L.object.value u) ⟨u, rfl⟩ i (Subtype.ext h)
  form := L.rvForm

theorem liftDataObject_doublyBounded {r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (L : MeasuredRVLiftData (G := G) A ω) : (liftDataObject L).doublyBounded :=
  ⟨L.domainBounded, L.valueBounded⟩

/-- Lift data for an object with its own form gives an isomorphism of
`μVF^◇[n]` onto the lifted object. -/
theorem isomorphic_of_liftData (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (A : VFObject (M := M) S n) {ω : Map A.carrier (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (hω : ∀ p, (ω p).val = (A.form p).val) (L : MeasuredRVLiftData (G := G) A.carrier ω)
    (hP : ProperInvariant S (rvLift (liftDataObject L).object).carrier) :
    Isomorphic G A (liftObject (liftDataObject L) hP) := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  refine morphism_of_generic h00 hc hs hsmall L.map (L.special.bijective h00)
    (special_factor h00 hc linear hκ hs hv hsmall hΓ L.special) (fun p hp => ?_)
  obtain ⟨D, hD, hdet⟩ := L.special.unit_derivative_of_independent h00 hc hκ.le hs hsmall hv p hp
  refine ⟨D, hD, ?_⟩
  have hlabel : liftLabelMap (liftDataObject L).object (L.map p) = L.labelMap p :=
    Subtype.ext (L.label_eq p).symm
  have hform : gammaMapValue (liftForm (liftDataObject L)) (L.map p) = gammaMapValue A.form p := by
    rw [liftForm_value, hlabel]
    exact (L.form_preserves p).trans (hω p)
  rw [hdet]
  change vfValue 1 = (gammaMapValue A.form p / gammaMapValue (liftForm (liftDataObject L)) (L.map p)).val
  rw [hform, div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one, map_one]

/-- Corollary 6.37, surjectivity in positive degree: every object of
`μVF^◇[n+1]` over a VF-generated base is isomorphic to a lift. -/
theorem exists_isomorphic_lift (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : VFObject (M := M) (T : Set M) (n + 1)) :
    ∃ U : MeasuredRVObject (M := M) (T : Set M) (n + 1), ∃ hU : U.doublyBounded,
      Isomorphic G A (liftObject U (measuredRVLift_properInvariant h00 hc hκ hs hv U hU)) := by
  let ω := gammaFormExtension A.form
  have hGraph := gammaFormExtension_graph_definable A.form
  let C : Fin 1 → DefSet (rawMixedSpace (M := M) (n + 1) A.labels) (T : Set M) := fun _ => A.carrier
  have hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ} := by
    intro i γ
    have he : {p | p ∈ (C i).carrier ∧ ω p = γ} = A.levelSet γ := by
      ext p
      constructor
      · rintro ⟨hp, hγ⟩
        refine ⟨hp, ?_⟩
        have h := gammaFormExtension_at A.form ⟨p, hp⟩
        exact h.symm.trans hγ
      · rintro ⟨hp, hγ⟩
        refine ⟨hp, ?_⟩
        exact (gammaFormExtension_at A.form ⟨p, hp⟩).trans hγ
    exact he.symm ▸ A.levelSet_geometry γ
  obtain ⟨_, hT⟩ := lemma_6_21_vfGenerated (G := G) h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt A.carrier C
    (fun _ => le_rfl) (fun _ => A.proper) (fun p hp => ⟨0, hp⟩) ω hGraph hLevels
  obtain ⟨L, _, _⟩ := hT 0 A.finiteRV
  have hω : ∀ p, (((gammaFormMap A.carrier ω hGraph).comp (Map.inclusion (fun _ h => h))) p).val =
      (A.form p).val := fun p => gammaFormExtension_at A.form p
  have hU := liftDataObject_doublyBounded L
  refine ⟨liftDataObject L, hU, ?_⟩
  exact isomorphic_of_liftData h00 hc linear hκ hs hv hsmall hΓ A hω L _

/-- Corollary 6.37, surjectivity in degree zero. -/
theorem exists_isomorphic_lift_zero (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (A : VFObject (M := M) S 0) :
    ∃ U : MeasuredRVObject (M := M) S 0, ∃ hU : U.doublyBounded,
      Isomorphic G A (liftObject U (measuredRVLift_properInvariant h00 hc hκ hs hv U hU)) := by
  obtain ⟨_, _, _, hL⟩ := lemma_6_21_zero_arity (G := G) (k := 1) h00 A.carrier A.proper
    (fun _ => A.carrier) (fun _ => le_rfl) (fun _ => A.proper) A.form
  obtain ⟨L, _, _⟩ := hL 0 A.finiteRV
  have hω : ∀ p, ((A.form.comp (Map.inclusion (fun _ h => h))) p).val = (A.form p).val := fun _ => rfl
  have hU := liftDataObject_doublyBounded L
  refine ⟨liftDataObject L, hU, ?_⟩
  exact isomorphic_of_liftData h00 hc linear hκ hs hv hsmall hΓ A hω L _

end DiamondIntegral.Section6.DiamondSurjectivity
