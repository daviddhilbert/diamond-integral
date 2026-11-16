import «section 6».UnaryContextLifts

/-! A unary mean step with an actual simultaneous ambient lift in any
VF dimension. The common coefficient protects both finite families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def UnaryPreparationContext.afterStep
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {i : Fin m}
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A)
    (F : RVFocusRealization (G := G) D.toRVFocusData)
    (H : RVFocusRealization (G := G) (X.focusData D))
    (hCoeff : H.component.coefficient=F.component.coefficient) :
    UnaryPreparationContext (regularizeMap F.component.map.image).image i := by
  let f := centripetalStepMap F.component
  let g := centripetalStepMap H.component
  have hg : Function.Bijective g := (regularization_bijective _).comp (H.component.bijective h00)
  let q := f.comp (X.projection.comp (g.inverse hg))
  refine ⟨m+(1+X.arity),(regularizeMap H.component.map.image).image,X.nextLabels,q,?_,
    regularization_properInvariant h00 hc hκ hs hv _ (H.component.image_properInvariant h00 hc hκ hs hv)
      H.component.image_vfDoublyBounded,
    regularized_vfDoublyBounded H.component.image_vfDoublyBounded,
    H.component.regularized_image_rvPullback h00 X.pullback,?_⟩
  · intro p
    obtain ⟨a,rfl⟩ := hg.surjective p
    change (f (X.projection (g.inverse hg (g a)))).val=_
    rw [Map.inverse_apply]
    exact (RVFocusRealization.context_regularized_point X D F H hCoeff a).symm
  · intro p hp z hz he
    rw [show (regularizeMap H.component.map.image).image.carrier=
      regularize '' H.component.map.image.carrier from regularization_carrier _] at hp hz
    exact regularized_tagged _ p hp z hz he

theorem UnaryFocusData.exists_protected_context_step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (D : UnaryFocusData A) {i : Fin m}
    (X : UnaryPreparationContext A i)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ j,(C j).carrier ⊆ A.carrier) (hC : ∀ j,ProperInvariant S (C j).carrier)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (hP : ∀ j,ProperInvariant S (P j).carrier) :
    ∃ E : CentripetalData (G := G) A,E.coordinate=0 ∧ E.activeTags=D.activeTags ∧
      (∀ x u,E.focus x u=D.focus u) ∧
      (∀ j,∃ J : CentripetalData (G := G) (C j),ApertureRestrictionData E J) ∧
      Nonempty (UnaryContextLift (G := G) X (centripetalStepMap E) P) := by
  obtain ⟨F,H,hCoeff,hLower,hFull⟩ := RVFocusData.exists_paired_protected_components
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt D.toRVFocusData
    (X.focusData D) (X.focusImage_subset D) C hCA hC P hPX hP
  let Y := X.afterStep h00 hc hκ hs hv D F H hCoeff
  let g := centripetalStepMap H.component
  have hg : Function.Bijective g := (regularization_bijective _).comp (H.component.bijective h00)
  refine ⟨F.component,F.coordinate,F.activeTags,F.focus,hLower,⟨{
    target := Y
    map := g
    chain := synchronized_centripetal_step h00 hc hκ hs hv H.component P
      (fun j => (hFull j).choose) (fun j => (hFull j).choose_spec)
    commutes := ?_
    fixed := RVFocusRealization.context_fixed_coordinate X D H
    retainedLabels := fun j => Fin.natAdd m (Fin.natAdd 1 j)
    retained := fun p j => by
      change (regularize (H.component.point p.val)).2 (Fin.natAdd m (Fin.natAdd 1 j))=p.val.2 j
      simp only [regularize,CentripetalData.point,Fin.append_right] }⟩⟩
  intro p
  change centripetalStepMap F.component (X.projection (g.inverse hg (g p)))=_
  rw [Map.inverse_apply]

end DiamondIntegral.Section6
