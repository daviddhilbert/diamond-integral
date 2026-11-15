import «section 5».NativeCylinderFubini
import «section 5».DefinableCylinderEndpoints

/-! The varying cylinder identity applies to the actual family itself;
endpoint maps are extracted from its full definable fibres. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def unaryGammaFamilyLift
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (volumeGammaSpace hc))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1)) :=
  ⟨{u | (Fin.init u,rvUnitValueHom (u (Fin.last n))) ∈ T.carrier},
    T.definable.preimage (unitGraphInputValueMap hc B.real n)⟩

theorem native_described_cylinder_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (shape : CylinderFibreKind)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (volumeGammaSpace hc)))
    (hproj : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ X.carrier)
    (hfibre : ∀ x : X, shape.Describes (fun γ : Values.Gamma (M := M) => (x.val,γ) ∈ T.carrier)) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (unaryGammaFamilyLift T) =
      (shape.eulerFactor kind : RESDimensionFreeReduction.Ring B) * nativeTorusClass B *
        nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  obtain ⟨f,ho,hrw⟩ := definable_cylinder_endpoints X shape T hfibre
  have he : (unaryGammaFamilyLift T).carrier = (groundGammaCylinderLift shape f).carrier := by
    ext u
    constructor
    · intro hu
      have hm : (Fin.init u,rvUnitValueHom (u (Fin.last n))) ∈ T.carrier := hu
      have hx := hproj _ _ hm
      exact ⟨⟨Fin.init u,hx⟩,rfl,(hrw ⟨Fin.init u,hx⟩ _).mp hm⟩
    · rintro ⟨x,hx,hc⟩
      have hm := (hrw x _).mpr hc
      change (Fin.init u,rvUnitValueHom (u (Fin.last n))) ∈ T.carrier
      exact hx ▸ hm
  exact (nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (GammaGroundBijection.ofCarrierEq he)).trans
      (native_cylinder_fubini h00 linear hκ hs hr hγ hΓ kind X shape f ho)

end DiamondIntegral.Section5
