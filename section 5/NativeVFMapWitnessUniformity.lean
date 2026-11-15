import «section 5».NativeMixedMapFibres
import «section 5».NativeVFLiftEqualitySchemata

/-! The actual positive fibre hypothesis of Theorem 5.17, for two native
definable maps to the same mixed base, gives a finite original-ground
catalog of whole VF lifting and stabilized RES equality packages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s p q : ℕ}

def NativeBoundedVFFibreLiftEquality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C) (z : Fin (p+q) → M) : Prop :=
  ∃ k l : ℕ,
    ∃ U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k,
    ∃ V : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l,
      Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f z) (gammaGroundObjectLift U)) ∧
      Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f' z) (gammaGroundObjectLift V)) ∧
      nativeRVEvaluation h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) .bounded
          (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) =
      nativeRVEvaluation h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) .bounded
          (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart V))

theorem native_vf_map_finite_whole_witness_catalog
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C)
    (h : ∀ z ∈ nativeMixedDomain C, NativeBoundedVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    ∃ J : Finset (NativeVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc .bounded
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val),
      ∀ z ∈ nativeMixedDomain C,∃ W ∈ J,W.Valid hc z := by
  apply native_vf_lift_equality_finite_catalog hκ hs hr hγ .bounded (nativeMixedDomain C)
    (nativeMixedDomain_definable C) (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val
    (nativeMixedMapFibreFormula f).property (nativeMixedMapFibreFormula f').property
  intro z hz
  obtain ⟨k,l,U,V,⟨H⟩,⟨K⟩,he⟩ := h z hz
  exact native_vf_lift_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ .bounded
    (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val z
    ((nativeMixedDomain_definable C).proper z hz)
    (nativeMixedMapFibreAt f z) (nativeMixedMapFibreAt f' z)
    (nativeMixedMapFibreAt_domain f z).symm (nativeMixedMapFibreAt_domain f' z).symm U V H K he

end DiamondIntegral.Section5
