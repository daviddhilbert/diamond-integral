import «section 5».VarietyPresentationRefinement

/-! Every regular map admits one finite affine source refinement
mapping regularly into each of two prescribed affine atlases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
variable {X Y : Object}

structure AffineMorphismRefinement (c : AffineVarietyPresentation X)
    (d : AffineVarietyPresentation Y) (f : Morphism X Y) where
  atlas : AffineVarietyPresentation X
  sourceIndex : atlas.presentation.index → c.presentation.index
  targetIndex : atlas.presentation.index → d.presentation.index
  sourceMap : ∀ k,Morphism (atlas.presentation.piece k) (c.presentation.piece (sourceIndex k))
  targetMap : ∀ k,Morphism (atlas.presentation.piece k) (d.presentation.piece (targetIndex k))
  source_fac : ∀ k,(sourceMap k).hom ≫ (c.presentation.inclusion (sourceIndex k)).hom =
    (atlas.presentation.inclusion k).hom
  target_fac : ∀ k,(targetMap k).hom ≫ (d.presentation.inclusion (targetIndex k)).hom =
    (atlas.presentation.inclusion k).hom ≫ f.hom

theorem affine_morphism_refinement_exists (c : AffineVarietyPresentation X)
    (d : AffineVarietyPresentation Y) (f : Morphism X Y) :
    Nonempty (AffineMorphismRefinement c d f) := by
  letI (j : d.presentation.index) := d.presentation.immersion j
  let P (i : c.presentation.index) := d.presentation.pullback (f.comp (c.presentation.inclusion i))
  let A (i : c.presentation.index) (j : (P i).index) :=
    Classical.choice (finite_affine_variety_presentation ((P i).piece j))
  let q : AffineVarietyPresentation X := {
    presentation := c.presentation.refine (fun i => (P i).refine (fun j => (A i j).presentation))
    affine := fun k => (A k.1 k.2.1).affine k.2.2 }
  refine ⟨{
    atlas := q
    sourceIndex := fun k => k.1
    targetIndex := fun k => k.2.1
    sourceMap := fun k => ((P k.1).inclusion k.2.1).comp ((A k.1 k.2.1).presentation.inclusion k.2.2)
    targetMap := fun k => (commonImmersionRight (f.comp (c.presentation.inclusion k.1))
      (d.presentation.inclusion k.2.1)).comp ((A k.1 k.2.1).presentation.inclusion k.2.2)
    source_fac := fun _ => rfl
    target_fac := ?_ }⟩
  intro k
  have h := reducedPullback_condition (f.comp (c.presentation.inclusion k.1)).hom
    (d.presentation.inclusion k.2.1).hom
  simpa only [q,P,ImmersedPresentation.refine,ImmersedPresentation.pullback,
    Morphism.comp,commonImmersionLeft,commonImmersionRight,invariantImmersedInclusion,
    Category.assoc] using congrArg (fun m =>
      ((A k.1 k.2.1).presentation.inclusion k.2.2).hom ≫ m) h.symm

end DiamondIntegral.Section5.EquivariantVariety
