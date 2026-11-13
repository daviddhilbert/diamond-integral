import «section 3».RVGenericFibreMonomials
import «section 3».RESCoefficientNeighborhoods
import «section 3».GammaMonomialArity
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- A finite-value-support target forces every exponent of a generic
fibre monomial to vanish. The resulting RES point is definable over
the actual map base, even when that base retains a residue parameter. -/
theorem gammaGroundRVUnitResidueMap_generic_fibre_definable {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m))
    (hR : (rvUnitTupleValues '' R.carrier).Finite) (F : GammaGroundMap A R)
    (x : A) (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) :
    ∃ c : Fin m → (CanonicalRV.RVSort M)ˣ,
      (∀ j, DefinableClosureAtBase B .rv (rvUnitValues c j)) ∧
      ∀ y : A, rvUnitTupleValues y.val = rvUnitTupleValues x.val → (F y).val = c := by
  obtain ⟨C,c,hcdef,hformula⟩ := gammaGroundRVUnitMap_generic_fibre_monomial
    hκ hs h00 hsmall hγsmall hΓ A R F x hγ
  have hcvalues := gammaGroundRVUnitTuple_point_values_definable hc c hcdef
  let v := GammaGroundMap.ofGlobal R
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
      (rvUnitGammaMap hc B.real m) (fun _ => Set.mem_univ _)
  have heR : v.image.carrier = rvUnitTupleValues '' R.carrier := by
    ext γ
    exact ⟨fun ⟨a,ha⟩ => ⟨a.val,a.property,ha⟩,
      fun ⟨a,ha,he⟩ => ⟨⟨a,ha⟩,he⟩⟩
  have hfvalues : ∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues (F x).val j) :=
    gammaGroundGamma_finite_tuple_point_definable v.image (heR.symm ▸ hR)
      (rvUnitTupleValues (F x).val) ⟨F x,rfl⟩
  have hzero : C = 0 := by
    funext j
    let z : Fin 2 → Values.Gamma (M := M) :=
      ![rvUnitTupleValues (F x).val j,rvUnitTupleValues c j]
    have hz : ∀ i, GammaDefinableClosureAtBase B (z i) := by
      intro i
      fin_cases i
      · exact hfvalues j
      · exact hcvalues j
    have hd := gammaDefinableClosure_integerCharacter (![1,-1] : Fin 2 → ℤ) z hz
    have hv := congrArg (fun t : Fin m → (CanonicalRV.RVSort M)ˣ => rvUnitValueHom (t j))
      (hformula x rfl)
    simp only [Pi.mul_apply,integerMonomialMap,map_mul,map_prod,map_zpow] at hv
    have he : integerCharacter (C j) (rvUnitTupleValues x.val) =
        integerCharacter (![1,-1] : Fin 2 → ℤ) z := by
      change (∏ k, rvUnitValueHom (x.val k) ^ C j k) = _
      calc
        _ = (rvUnitValueHom (c j))⁻¹ * rvUnitValueHom ((F x).val j) :=
          (eq_inv_mul_iff_mul_eq).mpr hv.symm
        _ = integerCharacter (![1,-1] : Fin 2 → ℤ) z := by
          simp [integerCharacter,z,mul_comm]
          exact mul_comm _ _
    exact hγ (C j) (he.symm ▸ hd)
  refine ⟨c,hcdef,?_⟩
  intro y hy
  rw [hformula y hy,hzero]
  funext j
  simp [integerMonomialMap]
end DiamondIntegral.Section3
