import «section 5».NativeWeakVFLiftSchemata
import «section 5».NativeWeakFiniteRVSchemaPromotion
import «section 5».NativeWeakRVLiftPresentations
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
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p n r m s : ℕ} {sp : Fin p → SortTag}

theorem native_weak_vf_lift_equality_schema_at_parameter
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) m s))
    (hA : {w | Fin.append z w ∈ D} = nativeMixedDomain A)
    (hC : {w | Fin.append z w ∈ E} = nativeMixedDomain C)
    {k l : ℕ}
    (U : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (V : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l)
    (H : GammaGroundBijection A (nativeWeakRVObjectLift U))
    (K : GammaGroundBijection C (nativeWeakRVObjectLift V))
    (he : nativeRVSetValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
      (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
        U.domain =
      nativeRVSetValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
      (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
        V.domain) :
    ∃ W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E, W.ValidWeak hc z := by
  obtain ⟨F,hF,hFd,hFv⟩ := native_weak_finite_rv_schema_at_parameter hκ hs hr hγ z hz U
  obtain ⟨G,hG,hGd,hGv⟩ := native_weak_finite_rv_schema_at_parameter hκ hs hr hγ z hz V
  obtain ⟨HP,hHP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    D (finiteRVSchemaLiftDomain hc F).val A (nativeWeakRVObjectLift U) hA
    (finiteRVSchemaLiftDomain_presents_weak_native_lift z hz U F hFv) H
  obtain ⟨KP,hKP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    E (finiteRVSchemaLiftDomain hc G).val C (nativeWeakRVObjectLift V) hC
    (finiteRVSchemaLiftDomain_presents_weak_native_lift z hz V G hGv) K
  have heRow : nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (finiteRVSchemaDomain F) z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (finiteRVSchemaDomain G) z :=
    (native_rv_row_value_of_presentation h00 linear hκ hs hr hγ hΓ kind z (nativeRVObjectOfGammaSet U.domain) (finiteRVSchemaDomain F) hFd).trans
      (he.trans (native_rv_row_value_of_presentation h00 linear hκ hs hr hγ hΓ kind z (nativeRVObjectOfGammaSet V.domain)
        (finiteRVSchemaDomain G) hGd).symm)
  obtain ⟨W,hW⟩ := rv_evaluation_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ kind
    (finiteRVSchemaDomain F) (finiteRVSchemaDomain G) z hz heRow
  exact ⟨⟨k,U.arity,F,l,V.arity,G,HP,KP,W⟩,hF,hG,hHP,hKP,hW⟩


end DiamondIntegral.Section5
