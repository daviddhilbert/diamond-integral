import «section 5».NativeRelativeGammaFubini
import «section 5».NativeUnitWeightedValues

/-! The relative Gamma formula expressed by the actual Euler level sets,
independent of every auxiliary finite certificate partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem native_relative_gamma_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (hproj : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ X.carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rvGammaFamilyLift T) =
      nativeTorusClass B ^ n * nativeUnitWeightedValue h00 linear hκ hs hr hγ hΓ kind X
        (fun x => rvGammaFibreEulerValue hc h00 hκ hs hr hγ T x kind)
        (rv_gamma_fibre_euler_constructible hc h00 hκ hs hr hγ X T kind).1
        (rv_gamma_fibre_euler_constructible hc h00 hκ hs hr hγ X T kind).2 := by
  obtain ⟨N,A,c,hsub,hd,hcov,hcst,he⟩ := native_relative_gamma_fubini_partition
    h00 linear hκ hs hr hγ hΓ kind X T hproj
  have hw := nativeUnitWeightedValue_partition h00 linear hκ hs hr hγ hΓ kind X _
    (rv_gamma_fibre_euler_constructible hc h00 hκ hs hr hγ X T kind).1
    (rv_gamma_fibre_euler_constructible hc h00 hκ hs hr hγ X T kind).2 A c hsub hd hcov hcst
  exact he.trans (congrArg (fun w => nativeTorusClass B ^ n * w) hw.symm)

end DiamondIntegral.Section5
