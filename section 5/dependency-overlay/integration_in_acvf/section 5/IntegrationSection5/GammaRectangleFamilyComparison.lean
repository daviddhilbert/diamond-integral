import IntegrationSection5.SharedRVProductComparison
import IntegrationSection5.MixedUnaryPreparations

/-! Uniform standard contraction comparison for every original-Gamma family whose RV fibres are rectangles, including empty or singleton factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}

def RVFibreRectangles (A : Set (Point (M := M) 2 m)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → (![vfAt p 0,vfAt q 1],p.2) ∈ A

theorem mixed_rectangle_projection_eq (A : Set (Point (M := M) 2 m)) (hA : RVFibreRectangles A) :
    A = {p | activeUnaryProjection 0 id p ∈ mixedUnaryProjectionSet A 0 ∧
      activeUnaryProjection 1 id p ∈ mixedUnaryProjectionSet A 1} := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,hp,rfl⟩,⟨p,hp,rfl⟩⟩
  · rintro ⟨⟨x,hx,hxp⟩,⟨y,hy,hyp⟩⟩
    have hvx : vfAt x 0 = vfAt p 0 := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hxp
    have hvy : vfAt y 1 = vfAt p 1 := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hyp
    have hlx : x.2 = p.2 := congrArg (fun z : Point (M := M) 1 m => z.2) hxp
    have hly : y.2 = p.2 := congrArg (fun z : Point (M := M) 1 m => z.2) hyp
    have h := hA x hx y hy (hlx.trans hly.symm)
    have he : (![vfAt x 0,vfAt y 1],x.2) = p := by
      apply Prod.ext
      · funext i
        fin_cases i
        · exact hvx
        · exact hvy
      · exact hlx
    exact he ▸ h

structure GammaMixedStandardComparison (G : GammaParameters.Base (M := M)) {m : ℕ}
    (A : Set (Point (M := M) 2 m)) where
  codes : Set M
  real_contains : G.real ⊆ codes
  source : DefSet (M := M) codes 2 m
  source_eq : carrier source = A
  source_gamma : GammaSetDefinable G (carrier source)
  contraction12 : StandardContraction source (Equiv.refl _)
  contraction21 : StandardContraction source (Equiv.swap 0 1)
  program12_gamma : GammaProgramDefinable G contraction12.program
  program21_gamma : GammaProgramDefinable G contraction21.program
  comparison : GammaRVIso G contraction12.contractionObject contraction21.contractionObject

theorem gamma_rectangle_family_comparison {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) (hRect : RVFibreRectangles A) :
    Nonempty (GammaMixedStandardComparison G A) := by
  obtain ⟨P⟩ := mixed_unary_preparations hs h00 hsmall F A hA
  have hSource : carrier P.source =
      {p | activeUnaryProjection 0 id p ∈ carrier P.sourceD ∧
        activeUnaryProjection 1 id p ∈ carrier P.sourceE} := by
    rw [P.source_eq,P.sourceD_eq,P.sourceE_eq]
    exact mixed_rectangle_projection_eq A hRect
  have hSG : GammaSetDefinable G (carrier P.source) := P.source_eq.symm ▸ hA
  obtain ⟨C12,C21,h12,h21,e⟩ := sharedRV_product_standard_contractions
    P.specialD P.specialE P.gammaD P.gammaE P.pullbackD P.pullbackE P.source hSource hSG
  exact ⟨{
    codes := P.codes
    real_contains := P.real_contains
    source := P.source
    source_eq := P.source_eq
    source_gamma := hSG
    contraction12 := C12
    contraction21 := C21
    program12_gamma := h12
    program21_gamma := h21
    comparison := e.some }⟩

end IntegrationInACVF.Section5
