import «section 3».GammaEmptyIndexedLabelBijections
import «section 3».GammaNativeFullWeightNormalization

/-! Projection from a zero-indexed full row preserves its entire
structural volume, up to its empty prefix. Consequently its native
presentation already has full weight, before normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable (U : GammaGroundMeasuredRVObject hc B (k+1))
variable (F : GammaMeasuredRVSchema hc B 0 U.underlying.arity (k+1) (fun _ => .rv))
variable (hF : F.valid Fin.elim0)
variable (hD : ∀ r, r ∈ F.object.rowDomain Fin.elim0 ↔ r ∈ U.underlying.domain.carrier)
variable (hV : ∀ r y, F.object.rowVolume Fin.elim0 r y ↔
  ∃ u : U.underlying.domain, u.val = r ∧ (U.underlying.volume u).val = y)
variable (P : F.object.IndexedPresentation (gammaEmptyParameterIndex B))

include hF hD hV in
theorem gammaEmptyIndexed_volume
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val =
      Fin.append (Fin.elim0 : Fin 0 → RV (M := M))
        (U.underlying.volume (gammaEmptyIndexedLabels F U.underlying.domain hD P u)).val := by
  let z := rvValues (indexedLeft u.val)
  let r := indexedRight u.val
  let value := F.object.rowValue z r
  have hz : z = Fin.elim0 := Subsingleton.elim _ _
  have hvalid : F.valid z := Eq.mpr (congrArg F.valid hz) hF
  have hr := (F.indexed_mem (gammaEmptyParameterIndex B) P u).2
  have hrow : F.object.rowVolume z r value :=
    (F.object.rowValue_graph z hvalid.1 r hr value).mpr rfl
  have hrow0 : F.object.rowVolume Fin.elim0 r value :=
    Eq.mp (congrArg (fun w => F.object.rowVolume w r value) hz) hrow
  obtain ⟨a,ha,hav⟩ := (hV r value).mp hrow0
  have hea : a = gammaEmptyIndexedLabels F U.underlying.domain hD P u := Subtype.ext ha
  have hvol : (U.underlying.volume (gammaEmptyIndexedLabels F U.underlying.domain hD P u)).val = value := by
    rw [← hea]
    exact hav
  exact (F.indexed_volume (gammaEmptyParameterIndex B) P u).trans
    (congrArg₂ Fin.append (Subsingleton.elim _ _) hvol.symm)

include hF hD hV in
theorem gammaEmptyIndexed_nonzero
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    ∀ i, ((Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val i).val ≠ iRVZero := by
  rw [gammaEmptyIndexed_volume U F hF hD hV P u]
  intro i
  refine Fin.addCases (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin (k+1) => ?_) i
  simp only [Fin.append_right]
  exact U.underlying.nonzero (gammaEmptyIndexedLabels F U.underlying.domain hD P u) j

include hF hD hV in
theorem gammaEmptyIndexed_full : GammaFullWeightAt (gammaUniversalObject P.toGamma) := by
  apply (gammaFullWeightAt_iff_nonzero (gammaUniversalObject P.toGamma)).mpr
  intro u i hi
  let v := (Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma)).symm u
  have he := gammaNativeRVGroundVolume_value (gammaUniversalObject P.toGamma) v
  apply gammaEmptyIndexed_nonzero U F hF hD hV P v i
  exact (congrArg (fun t => (t i).val) he).trans
    (hi.trans (CanonicalStructure.sortZero_normalize .rv))

end DiamondIntegral.Section3
