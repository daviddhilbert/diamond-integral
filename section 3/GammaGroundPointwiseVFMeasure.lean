import «section 3».GammaGroundEssentialVFMeasure
import «section 3».GammaGroundEssentialVFRestriction
import «section 3».GammaGroundRegularMeasureLocus

/-! Generic preservation has a pointwise preserving representative on
a definable cofull subset with open VF fibres, over the same Gamma ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3.GammaGroundEssentialVFMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r s : ℕ}

section Data
variable [TopologicalSpace (Section2.VF M)] {W : Type} [CommMonoidWithZero W]
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}

def Preserves (j : Section2.VF M →*₀ W) (a : A → W) (b : B → W)
    (f : GammaGroundEssentialVFMap A B) : Prop :=
  ∀ p : f.source, ∃ J : Section2.VF M, HasMixedVFJacobianAt f.map p J ∧
    a ⟨p.val, f.source_subset p.property⟩ = b ⟨(f.map p).val, f.target_subset (f.map p).property⟩ * j J

theorem Preserves.toGeneric {j : Section2.VF M →*₀ W} {a : A → W} {b : B → W}
    {f : GammaGroundEssentialVFMap A B} (h : f.Preserves j a b) : f.PreservesGeneric j a b := fun p _ => h p
end Data

variable [hchar : CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

def sourceForm (f : GammaGroundEssentialVFMap A B) (ω : GammaGroundVolumeForm hc ground A) :
    GammaGroundVolumeForm hc ground f.source := ω.comp (GammaGroundMap.inclusion f.source_subset)

def targetForm (f : GammaGroundEssentialVFMap A B) (σ : GammaGroundVolumeForm hc ground B) :
    GammaGroundVolumeForm hc ground f.target := σ.comp (GammaGroundMap.inclusion f.target_subset)

include hchar hκ hs hS hv hn in
theorem regularMeasureLocus_cofull (f : GammaGroundEssentialVFMap A B)
    (ω : GammaGroundVolumeForm hc ground A) (σ : GammaGroundVolumeForm hc ground B)
    (hf : f.PreservesGeneric Values.vfValueHom (fun a => (gammaGroundFormValue ω a).val)
      (fun b => (gammaGroundFormValue σ b).val)) :
    Section2.vfDimension (A.sdiff (gammaGroundRegularMeasureLocus hn f.map (f.sourceForm ω) (f.targetForm σ))).carrier <
      (n : WithBot ℕ) := by
  apply gammaGround_small_complement_of_generic A _ hκ hs hS hv hn
  intro a
  let p : f.source := ⟨a.val.val, gammaGround_mem_of_small_complement f.source hκ hs hS hv hn f.source_small a⟩
  obtain ⟨J, hJ, hw⟩ := hf p a.property
  obtain ⟨L, F, hF, hder⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f.map p a.property
  have hfull : HasMixedVFJacobianAt f.map p (LinearMap.toMatrix' L).det := ⟨F, hF, hder.hasJacobianAt⟩
  rw [hJ.unique hfull] at hw
  exact (mem_gammaGroundRegularMeasureLocus hn f.map (f.sourceForm ω) (f.targetForm σ) a.val.val).mpr
    ⟨p, rfl, L, ⟨F, hF, hder⟩, hw⟩

include hchar in
theorem exists_pointwise_preserving (f : GammaGroundEssentialVFMap A B)
    (ω : GammaGroundVolumeForm hc ground A) (σ : GammaGroundVolumeForm hc ground B)
    (hf : f.PreservesGeneric Values.vfValueHom (fun a => (gammaGroundFormValue ω a).val)
      (fun b => (gammaGroundFormValue σ b).val)) :
    ∃ g : GammaGroundEssentialVFMap A B,
      g.Preserves Values.vfValueHom (fun a => (gammaGroundFormValue ω a).val) (fun b => (gammaGroundFormValue σ b).val) ∧
        g.genericEquiv hκ hs hS hv hn = f.genericEquiv hκ hs hS hv hn := by
  let D := gammaGroundRegularMeasureLocus hn f.map (f.sourceForm ω) (f.targetForm σ)
  let E := gammaGroundFibreInterior hn D
  have hE : E.carrier ⊆ f.source.carrier :=
    (gammaGroundFibreInterior_subset hn D).trans
      (gammaGroundRegularMeasureLocus_subset hn f.map (f.sourceForm ω) (f.targetForm σ))
  have hsmall : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ) :=
    gammaGroundFibreInterior_preserves_cofull A D hκ hs hS hv hn
      (regularMeasureLocus_cofull hκ hs hS hv hn f ω σ hf)
  let g := f.restrictSource hκ hs hS hv hn E hE hsmall
  refine ⟨g, ?_, genericEquiv_restrictSource hκ hs hS hv hn f E hE hsmall⟩
  intro p
  have hpD := gammaGroundFibreInterior_subset hn D p.property
  obtain ⟨q, hq, L, hL, hw⟩ :=
    (mem_gammaGroundRegularMeasureLocus hn f.map (f.sourceForm ω) (f.targetForm σ) p.val).mp hpD
  let p0 : f.source := ⟨p.val, hE p.property⟩
  have hpq : p0 = q := Subtype.ext hq.symm
  have hJ : HasMixedVFJacobianAt f.map p0 (LinearMap.toMatrix' L).det := by
    rw [hpq]
    obtain ⟨F, hF, hder⟩ := hL
    exact ⟨F, hF, hder.hasJacobianAt⟩
  refine ⟨(LinearMap.toMatrix' L).det,
    restrictSource_jacobian hκ hs hS hv hn f E hE hsmall (gammaGroundFibreInterior_open_fibres hn D) p _ hJ, ?_⟩
  rw [← hpq] at hw
  exact hw

end DiamondIntegral.Section3.GammaGroundEssentialVFMap
