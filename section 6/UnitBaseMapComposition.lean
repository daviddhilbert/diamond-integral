import «section 6».CarriedBaseRestoration
import «section 6».ActiveCarriedRefinementSteps

/-! Finite compositions and actual active full-disc steps are retained
bounded unit base maps. This supplies the maps used in restoration;
no derivative or finite-chain witness is accepted as an extra input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RetainedUnitBaseMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def comp
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnitBaseMap (G := G) A) (H : RetainedUnitBaseMap (G := G) F.target) :
    RetainedUnitBaseMap (G := G) A where
  arity := H.arity
  target := H.target
  map := H.map.comp F.map
  sourceBounded := F.sourceBounded
  targetBounded := H.targetBounded
  home := lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ F.home H.home
  labels := H.labels ∘ F.labels
  labels_injective := H.labels_injective.comp F.labels_injective
  retained := fun p i => (H.retained (F.map p) (F.labels i)).trans (F.retained p i)
  unit := fun p hInd => (H.unit (F.map p)
    (independent_map_of_finiteFibres hc F.map (Map.finiteFibres_of_injective F.home.bijective.injective) p hInd)).comp
    (F.unit p hInd)

def ofChain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} {π : Fin r → Fin s}
    (F : RetainedUnaryHomeChain (G := G) S f π) (hF : F.DoublyBounded) (hπ : Function.Injective π) :
    RetainedUnitBaseMap (G := G) A where
  arity := s
  target := B
  map := f
  sourceBounded := hF.source
  targetBounded := hF.target
  home := F.homeomorphism h00 hc linear hκ hs hv hsmall hΓ
  labels := π
  labels_injective := hπ
  retained := F.retained
  unit := F.generic_unit hc

def ofActiveStep
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (k : Fin r) (D : CentripetalData (G := G) (rvCoordinateBundle A k))
    (hCoord : D.coordinate=Fin.last n) : RetainedUnitBaseMap (G := G) (rvCoordinateBundle A k) := by
  let H := activeBundleStepRetarget_unary_chain h00 hc linear hκ hs hv hsmall hΓ D hCoord
  let F := H.choose
  have hF : F.DoublyBounded := H.choose_spec
  exact ofChain h00 hc linear hκ hs hv hsmall hΓ F hF
    ((Fin.natAdd_injective (1+r) (n+1)).comp (Fin.natAdd_injective r 1))

end DiamondIntegral.Section6.RetainedUnitBaseMap
