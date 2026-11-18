import «section 3».GammaGroundJacobianValue
import «section 3».GammaGroundFiniteTopForms
import «section 3».GammaGroundDifferentiation
import Integration7.NonzeroScalarRVMaps

/-! Original-ground Jacobian density functions. Zero and undefined
determinants are replaced by one. At every independent point of a
bijection, the actual Gamma value is the value of its nonzero Jacobian. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}

def gammaGroundJacobianRVMap (hn : 0 < n) (f : GammaGroundMap A D) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 1)) :=
  (GammaGroundMap.ofGlobal _ _
    ((nonzeroRVScalarMap B.real).comp (scalarEncodedRVMap B.real))
    (fun _ => Set.mem_univ _)).comp (gammaGroundJacobianValueMap hn f)

theorem gammaGroundJacobianRVMap_nonzero (hn : 0 < n) (f : GammaGroundMap A D) (p : A) :
    (gammaGroundJacobianRVMap hn f p).val 0 ≠ 0 :=
  nonzero_rv_scalar_map_nonzero B.real _

theorem gammaGroundJacobianRVMap_of_derivative (hn : 0 < n) (f : GammaGroundMap A D)
    (p : A) (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) (h0 : (LinearMap.toMatrix' L).det ≠ 0) :
    (gammaGroundJacobianRVMap hn f p).val 0 = CanonicalRV.encodedRv (LinearMap.toMatrix' L).det := by
  have hj := gammaGroundJacobianValueMap_of_derivative hn f p L hL
  have hNZ : ((scalarEncodedRVMap B.real) ⟨(gammaGroundJacobianValueMap hn f p).val,Set.mem_univ _⟩).val 0 ≠ 0 := by
    rw [scalar_encoded_rv_map_value,hj]
    exact (RVOperations.rv_ne_zero _).mpr h0
  change (nonzeroRVScalarMap B.real
    ((scalarEncodedRVMap B.real) ⟨(gammaGroundJacobianValueMap hn f p).val,Set.mem_univ _⟩)).val 0 = _
  rw [nonzero_rv_scalar_map_of_nonzero B.real _ hNZ,scalar_encoded_rv_map_value,hj]

def gammaGroundJacobianTopForm (hn : 0 < n) (f : GammaGroundMap A D) : GammaGroundTopForm hc B A :=
  (GammaGroundMap.ofGlobal _ _ (rvGammaTopMap B.real) (fun _ => Set.mem_univ _)).comp
    (gammaGroundJacobianRVMap hn f)

theorem gammaGroundJacobianTopForm_finite (hn : 0 < n) (f : GammaGroundMap A D) (p : A) :
    (gammaGroundJacobianTopForm hn f p).val ≠ Values.infinity (M := M) := by
  intro hz
  apply gammaGroundJacobianRVMap_nonzero hn f p
  exact Subtype.ext (((Values.vrv_eq_infinity_iff _).mp hz).trans RVOperations.zero_val.symm)

def gammaGroundJacobianDensityForm (hn : 0 < n) (f : GammaGroundMap A D) : GammaGroundVolumeForm hc B A :=
  (gammaGroundJacobianTopForm hn f).finite (gammaGroundJacobianTopForm_finite hn f)

theorem gammaGroundJacobianDensityForm_of_derivative (hn : 0 < n) (f : GammaGroundMap A D)
    (p : A) (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) (h0 : (LinearMap.toMatrix' L).det ≠ 0) :
    (gammaGroundFormValue (gammaGroundJacobianDensityForm hn f) p).val =
      Values.vfValueHom (LinearMap.toMatrix' L).det := by
  change Values.vrv ((gammaGroundJacobianRVMap hn f p).val 0) = _
  rw [gammaGroundJacobianRVMap_of_derivative hn f p L hL h0]
  rfl

theorem gammaGroundJacobianDensityForm_of_independent
    [CharZero (VFType (M := M))] {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VFType (M := M)) G]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (f : GammaGroundBijection A D) (p : A)
    (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    ∃ J : VFType (M := M), HasMixedVFJacobianAt f.map p J ∧ J ≠ 0 ∧
      (gammaGroundFormValue (gammaGroundJacobianDensityForm hn f.map) p).val = Values.vfValueHom J := by
  obtain ⟨J,K,hJ,hK,hJK⟩ := gammaGround_jacobian_inverse_of_independent hκ hs hr hv f p hp
  have hJ0 : J ≠ 0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz,mul_zero] using hJK)
  obtain ⟨L,hL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv f.map p hp
  have hLJ : HasMixedVFJacobianAt f.map p (LinearMap.toMatrix' L).det := by
    obtain ⟨F,hF,hDF⟩ := hL
    exact ⟨F,hF,hDF.hasJacobianAt⟩
  have hdet := hLJ.unique hJ
  refine ⟨J,hJ,hJ0,?_⟩
  rw [gammaGroundJacobianDensityForm_of_derivative hn f.map p L hL (hdet ▸ hJ0),hdet]

end DiamondIntegral.Section3
