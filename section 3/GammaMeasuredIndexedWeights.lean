import «section 3».GammaMeasuredIndexedForms
import «section 3».GammaMeasuredCodeProducts
import «section 3».GammaNativeCombinedWeights

/-! Indexed weights are the unchanged fibre density times the joint
structural volume. Their factorization does not choose a density code. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
variable (BP : GammaFiniteGraphPresentation B p d T R)
variable (hF : ∀ t ∈ T, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP)

theorem GammaMeasuredRVSchema.indexed_volume
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val =
      Fin.append (BP.totalVolume (indexedLeft u.val)) (F.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val)) := by
  let v := Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u
  have hP := ((P.graph_iff v.val (P.volume v).val).mp ⟨v,rfl,rfl⟩).2.2
  exact (gammaNativeRVGroundVolume_value (gammaUniversalObject P.toGamma) u).trans hP.symm

theorem GammaMeasuredRVSchema.indexed_density
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma))
    (c : (volumeGammaSpace hc).domain)
    (hCode : (volumeGammaSpace hc).decode c = (F.indexedForm BP hF P u).val) :
    F.rowDensity (rvValues (indexedLeft u.val)) (indexedRight u.val) c :=
  (F.rowGammaValue_graph _ (hF _ (F.indexed_mem BP P u).1)
    ⟨indexedRight u.val,(F.indexed_mem BP P u).2⟩ c).mpr hCode

theorem GammaMeasuredRVSchema.indexed_weight
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    gammaNativeCombinedWeight (gammaUniversalObject P.toGamma) (F.indexedForm BP hF P) u =
      (∏ j, Values.vrv (BP.totalVolume (indexedLeft u.val) j)) *
      ((gammaGroundFormValue (F.indexedForm BP hF P) u).val *
        ∏ j, Values.vrv (F.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val) j)) := by
  unfold gammaNativeCombinedWeight
  rw [F.indexed_volume BP P u]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  ac_rfl

end DiamondIntegral.Section3
