import «section 6».RelativeShearCharts
import «section 6».UnaryStandardContractionStages
import «section 6».RVCoordinateDisplacements

/-! The strengthened first-stage induction records displacement
stability on fixed-label inactive fibres. The unary existence theorem
already has this property. In every arity, the actual geometry below
constructs the approved derivative exception rather than assuming it. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure ShearContractionStage (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  stage : StandardContractionStage (G := G) A
  displacement : SameLabelShearDisplacement stage.lift (Fin.last n)

def UnaryStandardContraction.toShearStage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (T : UnaryStandardContraction (G := G) A) :
    ShearContractionStage (G := G) A where
  stage := T.toStage h00 hc linear hκ hs hv hsmall hΓ
  displacement := fun p q _ hTags _ => T.special.unary_rv_displacement h00 (Fin.last 0) p q hTags

theorem exists_unary_shear_contraction_stage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier) :
    Nonempty (ShearContractionStage (G := G) A) := by
  obtain ⟨T⟩ := lemma_6_27_unary h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA
  exact ⟨T.toShearStage h00 hc linear hκ hs hv hsmall hΓ⟩

def shear_contraction_stage_of_bundle
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {B : DefSet (rawMixedSpace (M := M) (n+1) s) S} (f : Map A B)
    (hHome : ProperCovariantHomeomorphism f) (hBD : VFDoublyBounded B.carrier)
    (hRelative : ∀ p : A,∀ i : Fin n,(f p).val.1 i.castSucc=p.val.1 i.castSucc)
    (hStable : SameLabelShearDisplacement f (Fin.last n))
    (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (k : Fin s)
    (hBundle : B.carrier=(rvCoordinateBundle (vfDropLast B).image k).carrier) :
    ShearContractionStage (G := G) A := by
  have hOther (p : A) (i : Fin (n+1)) : i ≠ Fin.last n → (f p).val.1 i=p.val.1 i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h
      exact (h rfl).elim
    · intro _
      exact hRelative p j
  have hOpen (u v) : IsOpen (graphFibreSource f u v) := by
    obtain ⟨α,β,hα,hβ,hD,hR,hCov⟩ := hHome.covariant.radii u v
    exact (hD.isClopen hv).isOpen
  have hGeneric := relative_shear_generic_unit h00 hc hκ.le hs hsmall hv f (Fin.last n) hOther hStable hOpen
  let H := exists_mixed_unit_derivative_exception hc hs hsmall (Nat.zero_lt_succ n) f hGeneric
  let E := H.choose
  have hE := H.choose_spec
  exact {
    stage := {
      arity := s
      target := B
      lift := f
      home := hHome
      proper := hHome.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHome.bijective.surjective
      doublyBounded := hBD
      relative := hRelative
      oldLabels := π
      oldLabels_injective := hπ
      retained := hRetain
      leading := k
      bundle := hBundle
      exceptional := E
      exceptional_subset := hE.1
      exceptional_dim := hE.2.1
      unitDerivative := hE.2.2 }
    displacement := hStable }

end DiamondIntegral.Section6
