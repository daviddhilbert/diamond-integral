import «section 3».GammaEmptyIndexedStructuralVolumes
import «section 3».GammaMeasuredActualIsomorphismWitnesses

/-! Zero-index realization agrees with the literal measured RV object.
The label projection is bijective, the structural tuple has only an
empty prefix, and the complete Gamma density graph gives the same form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable (U : GammaGroundMeasuredRVObject hc B (k+1))
variable (F : GammaMeasuredRVSchema hc B 0 U.underlying.arity (k+1) (fun _ => .rv))
variable (hF : F.valid Fin.elim0)
variable (hD : ∀ r, r ∈ F.object.rowDomain Fin.elim0 ↔ r ∈ U.underlying.domain.carrier)
variable (hV : ∀ r y, F.object.rowVolume Fin.elim0 r y ↔
  ∃ u : U.underlying.domain, u.val = r ∧ (U.underlying.volume u).val = y)
variable (hW : ∀ r c, F.rowDensity Fin.elim0 r c ↔
  ∃ u : U.underlying.domain, u.val = r ∧ (U.form u).val = (volumeGammaSpace hc).decode c)
variable (P : F.object.IndexedPresentation (gammaEmptyParameterIndex B))

include hW in
theorem gammaEmptyIndexed_form
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    F.indexedForm (gammaEmptyParameterIndex B) (fun t _ => F.emptyRV_valid hF t) P u =
      U.form (gammaEmptyIndexedLabels F U.underlying.domain hD P u) := by
  obtain ⟨c,hc⟩ := (volumeGammaSpace hc).onto
    (F.indexedForm (gammaEmptyParameterIndex B) (fun t _ => F.emptyRV_valid hF t) P u).val
  have hrow := F.indexed_density (gammaEmptyParameterIndex B) (fun t _ => F.emptyRV_valid hF t) P u c hc
  have he : rvValues (indexedLeft u.val) = Fin.elim0 := Subsingleton.elim _ _
  have hrow0 := Eq.mp (congrArg (fun z => F.rowDensity z (indexedRight u.val) c) he) hrow
  obtain ⟨a,ha,hav⟩ := (hW (indexedRight u.val) c).mp hrow0
  have hea : a = gammaEmptyIndexedLabels F U.underlying.domain hD P u := Subtype.ext ha
  apply Subtype.ext
  exact hc.symm.trans ((congrArg (fun a => (U.form a).val) hea).symm.trans hav).symm

theorem gammaMeasured_combinedWeight_value {j : ℕ} (X : GammaGroundMeasuredRVObject hc B j)
    (u : X.underlying.domain) :
    (X.combinedWeight u).val = (gammaGroundFormValue X.form u).val *
      ∏ i, Values.vrv ((X.underlying.volume u).val i) := by
  change Values.gammaValHom (gammaGroundFormValue X.form u * ∏ i, Section2.rvFiniteValue _) = _
  rw [map_mul,map_prod]
  rfl

include hD hV hW in
def gammaEmptyIndexed_measured_hom :
    GammaGroundMeasuredRVHom
      (F.indexedObject (gammaEmptyParameterIndex B) (fun t _ => F.emptyRV_valid hF t) P)
      (U.reindexVolume (finCongr (by omega : (0+k)+1 = k+1))) := by
  let V := gammaUniversalObject P.toGamma
  let π := F.indexedForm (gammaEmptyParameterIndex B) (fun t _ => F.emptyRV_valid hF t) P
  let hfull := gammaEmptyIndexed_full U F hF hD hV P
  let X : GammaGroundMeasuredRVObject hc B ((0+k)+1) := ⟨Section5.nativeRVGroundObject V hfull,π⟩
  let g := gammaEmptyIndexedLabelBijection F U.underlying.domain hD P
  let H : GammaGroundMeasuredRVHom X (U.reindexVolume (finCongr (by omega : (0+k)+1 = k+1))) := {
    bijection := g
    preserves := by
      intro u
      rw [GammaGroundMeasuredRVObject.reindex_combinedWeight]
      apply Subtype.ext
      rw [gammaNativeFullMeasured_weight V hfull π u,gammaMeasured_combinedWeight_value]
      unfold gammaNativeCombinedWeight
      rw [gammaEmptyIndexed_volume U F hF hD hV P u,Fin.prod_univ_add]
      simp only [Fin.append_left,Fin.append_right,Fin.prod_univ_zero,one_mul]
      have he := gammaEmptyIndexed_form U F hF hD hW P u
      exact congrArg (fun q => (cast (gammaCarrier hc) q.val).val *
        ∏ i, Values.vrv ((U.underlying.volume (g.map u)).val i)) he }
  exact H.comp (gammaNativeFullWeightNormalizationHom V hfull π).symm

end DiamondIntegral.Section3
