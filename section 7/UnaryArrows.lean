import «section 7».IntermediateFormsInput
import «section 7».LiftClasses

/-! The steps of a relatively unary factorization as morphisms between objects
(for Proposition 7.24), on the intermediate-forms input.

This is the only file that unpacks the input `IntermediateForms M G`
(`section 7/IntermediateFormsInput.lean`). For an object `A` of `μVF^◇[n]` and
one step `f : A → B` of a factorization, `stepObject` is `B` with the form
given by the input (proper invariant by Section 6
`ProperCovariant.target_properInvariant`), and `stepMorphism` is the morphism
`A → stepObject` with underlying map `f`, relatively unary as `f` is
(`morphism_of_generic_map`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.UnaryArrows
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section7.IntermediateFormsInput
open DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hIF : IntermediateForms M G)
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} (A : VFObject (M := M) (T : Set M) n) {s : ℕ}
variable (B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)) (f : Map A.carrier B)
variable (homeo : ProperCovariantHomeomorphism (G := G) f)
variable (unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j)

include hIF h00 hc hκ hs hv hV hVT hTV hnt hsmall hΓ homeo unary in
/-- The input at one step. -/
theorem step_spec : StepForms A B f := hIF hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ A B f homeo unary

/-- The form on the target of a step. -/
def stepForm : Map B (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  Classical.choose (step_spec hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary).2

/-- **The target of a step, as an object of `μVF^◇[n]`.** -/
def stepObject : VFObject (M := M) (T : Set M) n where
  labels := s
  carrier := B
  form := stepForm hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary
  proper := homeo.covariant.target_properInvariant h00 hc lin hκ hs hv hsmall hΓ homeo.bijective.surjective
  formCovariant :=
    (Classical.choose_spec (step_spec hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary).2).1
  finiteRV := (step_spec hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary).1

theorem stepObject_carrier :
    (stepObject hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary).carrier = B := rfl

/-- **A step is a morphism** `A → stepObject` with underlying map `f`. -/
theorem stepMorphism :
    ∃ K : Morphism G A (stepObject hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary),
      K.map = f :=
  morphism_of_generic_map h00 hc hs hsmall (B := stepObject hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f
    homeo unary) f homeo.bijective (UnaryFactorization.step homeo unary)
    (Classical.choose_spec (step_spec hIF h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A B f homeo unary).2).2

end DiamondIntegral.Section7.UnaryArrows
