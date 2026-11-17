import «section 3».GammaRetainedRelativeContractionValues
import «section 3».GammaMixedRVLabelAttachments

/-! Appending actual RV data retains the old Gamma density and gives
a VF-fixed full measured bridge. This permits finite partition tags to
be treated by the already checked label-cut contraction scissors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
namespace GammaRetainedMeasuredVFData
variable (U : GammaRetainedMeasuredVFData hc B (n+1))
variable {R : GammaGroundDefSet hc B (rawRVSpace (M := M) l)} (K : GammaGroundMap U.domain R)

def attachRV : GammaRetainedMeasuredVFData hc B (n+1) where
  arity := U.arity+l
  domain := (gammaMixedAttachRV U.domain K).image
  finite := gammaMixedAttachRV_finite U.domain K U.finite
  labels := GammaGroundDefSet.univ hc B (rawRVSpace (U.arity+l))
  labels_mem _ := Set.mem_univ _
  form := gammaTotalRVCoordinateForm (Fin.castAdd l) U.form.extendByOne

theorem attachRV_form (p : U.domain) :
    (U.attachRV K).form ⟨(gammaMixedAttachRV U.domain K p).val.2,Set.mem_univ _⟩ =
      U.form ⟨p.val.2,U.labels_mem p⟩ := by
  change U.form.extendByOne ⟨Fin.append p.val.2 (K p).val ∘ Fin.castAdd l,Set.mem_univ _⟩ = _
  have h : Fin.append p.val.2 (K p).val ∘ Fin.castAdd l = p.val.2 := funext (Fin.append_left _ _)
  rw [h]
  exact U.form.extendByOne_apply ⟨p.val.2,U.labels_mem p⟩

def attachRVBridge (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    GammaFullMeasuredBijection U.toMeasured (U.attachRV K).toMeasured :=
  gammaFullMeasuredFixedVF C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv
    (gammaMixedAttachRVBijection U.domain K) (fun _ => rfl) (by
      intro p
      exact congrArg (fun z : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
        (cast (gammaCarrier hc) z.val).val) (U.attachRV_form K p).symm)

theorem attachRVBridge_value (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : U.toMeasured.domain) :
    ((U.attachRVBridge K C hBC hv).map.map p).val = (p.val.1,Fin.append p.val.2 (K p).val) := rfl

end GammaRetainedMeasuredVFData
end DiamondIntegral.Section3
