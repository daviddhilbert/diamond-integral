import «section 5».ReducedInducedSchemes

/-! Closed and open images determine the corresponding immersion
properties for reduced source and target schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

theorem reduced_immersion_closed_of_range {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Y) [IsImmersion f]
    (hf : IsClosed (Set.range f)) : IsClosedImmersion f := by
  let Z : Closeds Y := ⟨Set.range f, hf⟩
  letI := reducedClosedScheme_isReduced Z
  letI := reducedClosedInclusion_isClosedImmersion Z
  let e := reducedImmersionIso f (reducedClosedInclusion Z)
    (reducedClosedInclusion_range Z).symm
  have he : e.hom ≫ reducedClosedInclusion Z = f := reducedImmersionIso_fac _ _ _
  rw [← he]
  infer_instance

theorem reduced_immersion_open_of_range {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Y) [IsImmersion f] (hf : IsOpen (Set.range f)) : IsOpenImmersion f := by
  let U : Y.Opens := ⟨Set.range f, hf⟩
  letI : AlgebraicGeometry.IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  let e := reducedImmersionIso f U.ι (Scheme.Opens.range_ι U).symm
  have he : e.hom ≫ U.ι = f := reducedImmersionIso_fac _ _ _
  rw [← he]
  infer_instance

end DiamondIntegral.Section5
