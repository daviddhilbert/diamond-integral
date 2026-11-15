import «section 5».NativeFiniteRVLiftDomains
import «section 5».NativeMixedCodeRealization
import «section 5».NativeRVLabelGraphs

/-! An exact full label-graph presentation identifies the whole VF lift
literally at the displayed parameter. All VF and old RV coordinates are
retained, including zero-coordinate strata. -/
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
variable {p k : ℕ} {sp : Fin p → SortTag}

theorem finiteRVSchemaLiftDomain_presented_native_row
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (F : GammaFiniteRVSchema B p U.arity k sp)
    (hV : ∀ x : Fin U.arity → M, ∀ y : Fin k → M,
      Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append x y ∈ nativeRVLabelGraph U)
    (q : Section2.Mixed M k U.arity) :
    Fin.append z (nativeMixedCode q) ∈ (finiteRVSchemaLiftDomain hc F).val ↔
      q ∈ (gammaGroundObjectLift U).carrier := by
  have hrow : Fin.append z (nativeMixedCode q) ∈ (finiteRVSchemaLiftDomain hc F).val ↔
      Fin.append (Fin.append z (rvValues q.2)) (rvValues (Section2.tupleRV M q.1)) ∈ F.volume :=
    finiteRVSchemaLiftDomain_row hc F z (vfValues q.1) (rvValues q.2) hz
      (fun i => (q.1 i).property) (fun i => (q.2 i).property)
  refine hrow.trans ((hV _ _).trans ((nativeRVLabelGraph_append_iff U _ _).trans ?_))
  constructor
  · rintro ⟨u,hx,hy⟩
    exact ⟨u,rvValues_injective hx,rvValues_injective hy⟩
  · rintro ⟨u,hx,hy⟩
    exact ⟨u,congrArg rvValues hx,congrArg rvValues hy⟩

theorem finiteRVSchemaLiftDomain_presents_native_lift
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (F : GammaFiniteRVSchema B p U.arity k sp)
    (hV : ∀ x : Fin U.arity → M, ∀ y : Fin k → M,
      Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append x y ∈ nativeRVLabelGraph U) :
    {w | Fin.append z w ∈ (finiteRVSchemaLiftDomain hc F).val} = nativeMixedDomain (gammaGroundObjectLift U) := by
  ext w
  constructor
  · intro h
    have hw : w ∈ sortedUniverse (Fin.append (fun _ : Fin k => .vf) (fun _ : Fin U.arity => .rv)) := by
      intro i
      simpa only [Fin.append_right] using (finiteRVSchemaLiftDomain hc F).property.proper _ h (Fin.natAdd p i)
    let q := nativeMixedPointOfCode w hw
    have hcode : nativeMixedCode q = w := nativeMixedPointOfCode_code w hw
    have hq : q ∈ (gammaGroundObjectLift U).carrier :=
      (finiteRVSchemaLiftDomain_presented_native_row z hz U F hV q).mp (hcode.symm ▸ h)
    exact ⟨q,hq,hcode⟩
  · rintro ⟨q,hq,rfl⟩
    exact (finiteRVSchemaLiftDomain_presented_native_row z hz U F hV q).mpr hq

end DiamondIntegral.Section5
