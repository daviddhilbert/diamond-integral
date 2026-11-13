import «section 3».RVGammaFormValuePartition
import «section 3».FullGammaFunctionEvaluation
import «section 3».GammaGroundFiniteValuePoints
import «section 3».RESUnitCoordinates
import «section 3».GammaGroundRVLabelValues
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

/-- A Gamma-valued weight on a finite-value-support residue domain has
finite image, and every value is definable over the original ground. -/
theorem gammaGroundRESUnit_gamma_weight_finite_named {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (w : GammaGroundVolumeForm hc B R) :
    (Set.range (fun a : R => (w a).val)).Finite ∧
      ∀ a : R, GammaDefinableClosureAtBase B (w a).val := by
  obtain ⟨N,f,hf⟩ := rvUnitGammaGraph_finite_value_functions hκ hs h00 hc B hsmall hγsmall
    R.carrier (fun a => (w a).val) (gammaGroundRVUnitGammaForm_graph R w)
  have hfin : (⋃ i : Fin N, (f i).val '' (rvUnitTupleValues '' R.carrier)).Finite :=
    Set.finite_iUnion (fun i => hR.image (f i).val)
  have hrange : (Set.range (fun a : R => (w a).val)).Finite := by
    apply hfin.subset
    rintro δ ⟨a,rfl⟩
    obtain ⟨i,hi⟩ := hf a
    exact Set.mem_iUnion.mpr ⟨i,rvUnitTupleValues a.val,⟨a.val,a.property,rfl⟩,hi⟩
  refine ⟨hrange,?_⟩
  let v := GammaGroundMap.ofGlobal R
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
      (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)
  have he : v.image.carrier = rvUnitTupleValues '' R.carrier := by
    ext γ
    exact ⟨fun ⟨a,ha⟩ => ⟨a.val,a.property,ha⟩,fun ⟨a,ha,he⟩ => ⟨⟨a,ha⟩,he⟩⟩
  intro a
  obtain ⟨i,hi⟩ := hf a
  rw [← hi]
  apply (f i).property.eval_definable
  exact gammaGroundGamma_finite_tuple_point_definable v.image (he ▸ hR)
    (rvUnitTupleValues a.val) ⟨a,rfl⟩

/-- The actual combined weight of every measured RES object is a
finite-valued original-ground function, with no restriction on its form. -/
theorem gammaGroundMeasuredRES_combined_weight_finite_named {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (X : GammaGroundMeasuredRESObject hc B r) :
    (Set.range X.obj.combinedWeight).Finite ∧
      ∀ a, GammaDefinableClosureAtBase B (X.obj.combinedWeight a) := by
  let C := gammaGroundRESUnitChart h00 (show GammaGroundRESObject hc B r from ⟨X.obj.underlying,X.property⟩)
  let w := X.obj.combinedWeightForm.comp C.bijection.symm.map
  obtain ⟨hf,hn⟩ := gammaGroundRESUnit_gamma_weight_finite_named hκ hs h00 hsmall hγsmall
    C.native C.finite_values w
  have hw (a : X.obj.underlying.domain) : (w (C.bijection.map a)).val = X.obj.combinedWeight a := by
    change (X.obj.combinedWeightForm (C.bijection.symm.map (C.bijection.map a))).val = _
    have he := congrArg (fun z : C.object.obj.domain => (X.obj.combinedWeightForm z).val)
      (C.bijection.map.inverse_apply C.bijection.bijective a)
    exact he.trans (X.obj.combinedWeightForm_value a)
  constructor
  · apply hf.subset
    rintro δ ⟨a,rfl⟩
    exact ⟨C.bijection.map a,hw a⟩
  · intro a
    rw [← hw a]
    exact hn (C.bijection.map a)
end DiamondIntegral.Section3
