import «section 3».GammaGroundEssentialVFGerms
import «section 3».GammaGroundFibreInterior

/-! Cofull same-ground source restrictions retain the essential germ.
Open VF fibres additionally retain every original fixed-label Jacobian. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3.GammaGroundEssentialVFMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

def restrictSource (f : GammaGroundEssentialVFMap A B)
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (hE : E.carrier ⊆ f.source.carrier)
    (hsmall : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ)) : GammaGroundEssentialVFMap A B := by
  let F := f.map.restrict hE
  have hF : Function.Injective F := by
    intro p q he
    exact Subtype.ext (congrArg (fun z : f.source => z.val) (f.bijective.injective he))
  have htar : Section2.vfDimension (B.sdiff F.image).carrier < (n : WithBot ℕ) := by
    apply gammaGround_small_complement_of_generic B F.image hκ hs hS hv hn
    intro b
    obtain ⟨a, ha⟩ := (f.genericEquiv hκ hs hS hv hn).surjective b
    let p : E := ⟨a.val.val, gammaGround_mem_of_small_complement E hκ hs hS hv hn hsmall a⟩
    exact ⟨p, congrArg (fun z : GammaGroundGeneric B => z.val.val) ha⟩
  exact ⟨E, F.image, hE.trans f.source_subset,
    by rintro y ⟨p, rfl⟩; exact f.target_subset (F p).property,
    hsmall, htar, F.toImage, F.toImage_bijective hF⟩

theorem genericEquiv_restrictSource (f : GammaGroundEssentialVFMap A B)
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (hE : E.carrier ⊆ f.source.carrier)
    (hsmall : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ)) :
    (f.restrictSource hκ hs hS hv hn E hE hsmall).genericEquiv hκ hs hS hv hn =
      f.genericEquiv hκ hs hS hv hn := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem restrictSource_jacobian (f : GammaGroundEssentialVFMap A B)
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (hE : E.carrier ⊆ f.source.carrier)
    (hsmall : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ))
    (hopen : ∀ p : E, ∃ δ : Values.Gamma (M := M), ∀ x ∈ vfBall p.val.1 δ, (x, p.val.2) ∈ E.carrier)
    (p : E) (J : Section2.VF M)
    (hJ : HasMixedVFJacobianAt f.map ⟨p.val, hE p.property⟩ J) :
    HasMixedVFJacobianAt (f.restrictSource hκ hs hS hv hn E hE hsmall).map p J := by
  obtain ⟨F, ⟨ρ, hρ⟩, hder⟩ := hJ
  obtain ⟨δ, hδ⟩ := hopen p
  refine ⟨F, ⟨max ρ δ, fun x hx => ?_⟩, hder⟩
  obtain ⟨hxA, hF⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
  have hxE := hδ x (vfBall_anti (le_max_right _ _) hx)
  exact ⟨hxE, hF⟩

end DiamondIntegral.Section3.GammaGroundEssentialVFMap
