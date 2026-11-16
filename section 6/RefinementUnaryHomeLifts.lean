import «section 6».RefinementPortDerivatives
import «section 6».BoundedOrderedUnaryChains

/-! Actual finite relatively unary homeomorphism chains lift through
full RV refinements. The lift retains every refining label, all actual
intermediate double bounds and the complete original-map square. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S}

structure RVRefinementUnaryHomeLift (X : RVRefinementFrame A) (f : Map A B) where
  target : RVRefinementFrame B
  map : Map X.base target.base
  labels : Fin X.arity → Fin target.arity
  chain : RetainedUnaryHomeChain (G := G) S map labels
  bounded : chain.DoublyBounded
  commutes : ∀ p : X.base,target.oldPoint (map p)=f (X.oldPoint p)

namespace RVRefinementUnaryHomeLift

def identity (X : RVRefinementFrame A) : RVRefinementUnaryHomeLift (G := G) X (Map.id A) where
  target := X
  map := Map.id X.base
  labels := id
  chain := .identity X.base X.proper
  bounded := X.doublyBounded
  commutes := fun _ => rfl

def comp {X : RVRefinementFrame A} {f : Map A B} {g : Map B C}
    (F : RVRefinementUnaryHomeLift (G := G) X f)
    (H : RVRefinementUnaryHomeLift (G := G) F.target g) : RVRefinementUnaryHomeLift (G := G) X (g.comp f) where
  target := H.target
  map := H.map.comp F.map
  labels := H.labels ∘ F.labels
  chain := .comp F.chain H.chain
  bounded := ⟨F.bounded,H.bounded⟩
  commutes := fun p => (H.commutes (F.map p)).trans (congrArg g (F.commutes p))

def unary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (X : RVRefinementFrame A) (f : Map A B) (j : Fin n)
    (hF : ProperCovariantHomeomorphism f)
    (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt f p)
    (π : Fin r → Fin s) (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (hBD : VFDoublyBounded B.carrier) : RVRefinementUnaryHomeLift (G := G) X f := by
  have hB := hF.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hF.bijective.surjective
  let Y := X.portTarget h00 hc hκ hs hv f hF.bijective π hRetain hB hBD
  let F : RetainedUnaryHomeChain (G := G) S (X.portMap hc f) (Fin.natAdd s) :=
    .unary j (X.port_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f hF π hRetain hBD)
      (X.port_relative hc f j hRelative) (X.port_generic_unit hc hv f hUnit) (X.port_retained hc f)
  refine {
    target := Y
    map := X.portMap hc f
    labels := Fin.natAdd s
    chain := F
    bounded := ⟨X.doublyBounded,Y.doublyBounded⟩
    commutes := ?_ }
  intro p
  apply Subtype.ext
  exact retainedRVOutput_selected hc (f.comp X.oldMap) p

end RVRefinementUnaryHomeLift

def RetainedUnaryHomeChain.liftRefinement
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} {π : Fin r → Fin s} (F : RetainedUnaryHomeChain (G := G) S f π) :
    F.DoublyBounded → (X : RVRefinementFrame A) → RVRefinementUnaryHomeLift (G := G) X f := by
  induction F with
  | identity A hA =>
    intro hD X
    exact .identity X
  | unary j hHome hRelative hUnit hRetain =>
    intro hD X
    exact .unary h00 hc linear hκ hs hv hsmall hΓ X _ j hHome hRelative hUnit _ hRetain hD.2
  | comp first second ihf ihg =>
    intro hD X
    let F := ihf hD.1 X
    let H := ihg hD.2 F.target
    exact .comp F H

theorem OrderedStandardContractionLift.exists_refinement_unary_lift
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {q : ℕ} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S A U} (V : OrderedStandardContractionLift T)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (X : RVRefinementFrame A) :
    Nonempty (RVRefinementUnaryHomeLift (G := G) X V.map) := by
  obtain ⟨F,hF⟩ := V.bounded_relatively_unary_chain h00 hc linear hκ hs hv hsmall hΓ hA hAD
  exact ⟨F.liftRefinement h00 hc linear hκ hs hv hsmall hΓ hF X⟩

end DiamondIntegral.Section6
