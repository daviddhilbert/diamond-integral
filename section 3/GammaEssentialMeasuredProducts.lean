import «section 3».GammaEssentialVFProducts
import «section 3».GammaGroundEssentialVFMeasure

/-! Actual Cartesian products of essential representatives preserve
the complete Gamma measure equation. The determinant is the product of
the two checked block Jacobians, uniformly in zero-degree factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n m : ℕ}

theorem gammaMeasuredVF_product_weight_pair (U : GammaGroundMeasuredVFData hc B n)
    (V : GammaGroundMeasuredVFData hc B m) (u : U.domain) (v : V.domain) :
    gammaGroundMeasuredVFWeight (U.product V)
      ((gammaGroundMixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩) =
        gammaGroundMeasuredVFWeight U u * gammaGroundMeasuredVFWeight V v := by
  unfold gammaGroundMeasuredVFWeight
  rw [GammaGroundMeasuredVFData.product_form]
  change (gammaGroundFormValue U.form ⟨(gammaGroundMixedUnpack U.domain V.domain
      ((gammaGroundMixedPack U.domain V.domain).toImage _)).val.1,_⟩).val *
    (gammaGroundFormValue V.form ⟨(gammaGroundMixedUnpack U.domain V.domain
      ((gammaGroundMixedPack U.domain V.domain).toImage _)).val.2,_⟩).val = _
  rw [gammaMixedUnpack_pack]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaEssential_product_preserves
    {U U' : GammaGroundMeasuredVFData hc B n} {V V' : GammaGroundMeasuredVFData hc B m}
    (f : GammaGroundEssentialVFMap U.domain U'.domain) (g : GammaGroundEssentialVFMap V.domain V'.domain)
    (hf : f.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight U'))
    (hg : g.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight V) (gammaGroundMeasuredVFWeight V')) :
    (f.product hκ hs hr hv g).PreservesGeneric Values.vfValueHom
      (gammaGroundMeasuredVFWeight (U.product V)) (gammaGroundMeasuredVFWeight (U'.product V')) := by
  intro p hp
  let z := gammaGroundMixedUnpack f.source g.source p
  let u : f.source := ⟨z.val.1,z.property.1⟩
  let v : g.source := ⟨z.val.2,z.property.2⟩
  have hpoint : (gammaGroundMixedPack f.source g.source).toImage ⟨(u.val,v.val),u.property,v.property⟩ = p :=
    gammaMixedPack_unpack f.source g.source p
  have hu : AlgebraicIndependent (vfParameterField B.real) u.val.1 := by
    have h := hp.comp (Fin.castAdd m) (Fin.castAdd_injective n m)
    rw [← hpoint] at h
    change AlgebraicIndependent (vfParameterField B.real) (Fin.append u.val.1 v.val.1 ∘ Fin.castAdd m) at h
    simpa only [Function.comp_def,Fin.append_left] using h
  have hv' : AlgebraicIndependent (vfParameterField B.real) v.val.1 := by
    have h := hp.comp (Fin.natAdd n) (Fin.natAdd_injective m n)
    rw [← hpoint] at h
    change AlgebraicIndependent (vfParameterField B.real) (Fin.append u.val.1 v.val.1 ∘ Fin.natAdd n) at h
    simpa only [Function.comp_def,Fin.append_right] using h
  obtain ⟨J,hJ,hwJ⟩ := hf u hu
  obtain ⟨K,hK,hwK⟩ := hg v hv'
  refine ⟨J*K,?_,?_⟩
  · change HasMixedVFJacobianAt (gammaMixedProductMap f.map g.map) p (J*K)
    rw [← hpoint]
    exact gammaMixedProduct_jacobian f.map g.map u v J K hJ hK
  · let u₀ : U.domain := ⟨u.val,f.source_subset u.property⟩
    let v₀ : V.domain := ⟨v.val,g.source_subset v.property⟩
    let u₁ : U'.domain := ⟨(f.map u).val,f.target_subset (f.map u).property⟩
    let v₁ : V'.domain := ⟨(g.map v).val,g.target_subset (g.map v).property⟩
    have hSource : (⟨p.val,(f.product hκ hs hr hv g).source_subset p.property⟩ : (U.product V).domain) =
        (gammaGroundMixedPack U.domain V.domain).toImage ⟨(u₀.val,v₀.val),u₀.property,v₀.property⟩ :=
      Subtype.ext (congrArg (fun q : gammaGroundMixedProductDomain f.source g.source => q.val) hpoint).symm
    have hTarget : (⟨((f.product hκ hs hr hv g).map p).val,
        (f.product hκ hs hr hv g).target_subset ((f.product hκ hs hr hv g).map p).property⟩ : (U'.product V').domain) =
        (gammaGroundMixedPack U'.domain V'.domain).toImage ⟨(u₁.val,v₁.val),u₁.property,v₁.property⟩ := by
      apply Subtype.ext
      change (gammaMixedProductMap f.map g.map p).val = _
      rw [← hpoint,gammaMixedProductMap_pair]
      rfl
    rw [hSource,hTarget,gammaMeasuredVF_product_weight_pair,gammaMeasuredVF_product_weight_pair]
    rw [hwJ,hwK,map_mul]
    ac_rfl

end DiamondIntegral.Section3
