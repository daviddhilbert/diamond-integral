import «section 5».GroundRectangleAssembly
import «section 3».GammaGroundRVAngularQuotient
import «section 3».GammaGroundBijectionRestrictions
import «section 3».RVAngularValueReconstruction

/-! Transport the mixed value partition through an actual integral monomial
coordinate equivalence. The output pieces are cut out by a partition of
the original RV value support, with actual original-ground bijections. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def groundRVValueImage (Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)) :=
  (GammaGroundMap.ofGlobal Y (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
    (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).image

theorem groundRVValueImage_carrier (Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    (groundRVValueImage Y).carrier = rvUnitTupleValues '' Y.carrier := by
  ext γ
  exact ⟨fun ⟨y, hy⟩ => ⟨y.val, y.property, hy⟩,
    fun ⟨y, hy, he⟩ => ⟨⟨y, hy⟩, he⟩⟩

/-- Within one angular cell, the monomial charts are induced by a genuine
finite partition of the original value image, over the original ground. -/
theorem ground_angular_value_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    ∃ N : ℕ,
      ∃ β : Fin N → Fin K.zeroArity → Values.Gamma (M := M),
      ∃ R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity),
      ∃ G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity)),
      ∃ Y : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ D : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)),
      (∀ j i, GammaDefinableClosureAtBase B (β j i)) ∧
      (∀ j, rvUnitTupleValues '' (R j).carrier ⊆ {β j}) ∧
      (∀ j, Nonempty (GammaGroundBijection (Y j)
        ((R j).prod (gammaGroundRVUnitGammaPreimage (G j))))) ∧
      (∀ j, E.coordinateEquiv K '' (Y j).carrier =
        ((R j).prod (gammaGroundRVUnitGammaPreimage (G j))).carrier) ∧
      (∀ j, (Y j).carrier = X.carrier ∩ rvUnitTupleValues ⁻¹' (D j).carrier) ∧
      (∀ j k, j ≠ k → Disjoint (D j).carrier (D k).carrier) ∧
      (∀ γ, γ ∈ rvUnitTupleValues '' X.carrier ↔ ∃ j, γ ∈ (D j).carrier) := by
  let T := gammaGroundRVAngularMixedDomain X E K
  let A := gammaGroundRVAngularResidueDomain X E K
  have hsub : ∀ r γ, (r, γ) ∈ T.carrier → r ∈ A.carrier :=
    fun r γ h => ⟨⟨(r, γ), h⟩, rfl⟩
  obtain ⟨N, β, R, G, C, hβ, hR, hdis, hcov, hcut⟩ :=
    ground_mixed_value_normal_form hκ hs h00 hsmall hγsmall hΓ T A
      (gammaGroundRVAngularResidueDomain_finite_values X E K) hsub
  let e := E.coordinateEquiv K
  let v := fun x => (rvUnitTupleValues (e x).1, rvUnitTupleValues (e x).2)
  have hT : ∀ x, ((e x).1, rvUnitTupleValues (e x).2) ∈ T.carrier ↔ x ∈ X.carrier := by
    intro x
    have hh := Set.ext_iff.mp (gammaGroundRVAngularMixedDomain_full_preimage X E K) (e x)
    change (((e x).1, rvUnitTupleValues (e x).2) ∈ T.carrier) ↔ _ at hh
    rw [gammaGroundRVAngularCoordinateMap_image] at hh
    exact hh.trans ⟨fun ⟨y, hy, he⟩ => e.injective he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hv : ∀ x y, rvUnitTupleValues x = rvUnitTupleValues y → v x = v y := by
    intro x y hxy
    change (rvUnitTupleValues (E.coordinateEquiv K x).1, rvUnitTupleValues (E.coordinateEquiv K x).2) =
      (rvUnitTupleValues (E.coordinateEquiv K y).1, rvUnitTupleValues (E.coordinateEquiv K y).2)
    rw [← E.coordinate_value_naturality K x, ← E.coordinate_value_naturality K y, hxy]
  let f := gammaGroundRVAngularCoordinateBijection X E K
  let Z := fun j => (R j).prod (gammaGroundRVUnitGammaPreimage (G j))
  let Y := fun j => f.inverseImage (Z j)
  have hY : ∀ j x, x ∈ (Y j).carrier ↔ x ∈ X.carrier ∧ v x ∈ (C j).carrier := by
    intro j x
    constructor
    · rintro ⟨a, ha, hz⟩
      have h := (hcut j (e a.val).1 (rvUnitTupleValues (e a.val).2)).mpr hz
      exact ⟨ha ▸ a.property, ha ▸ h.2⟩
    · rintro ⟨hx, hc⟩
      have hz := (hcut j (e x).1 (rvUnitTupleValues (e x).2)).mp ⟨(hT x).mpr hx, hc⟩
      exact ⟨⟨x, hx⟩, rfl, hz⟩
  have hZ : ∀ j, (Z j).carrier ⊆ (gammaGroundRVAngularCoordinateMap X E K).image.carrier := by
    intro j z hz
    let x := e.symm z
    have he : e x = z := e.apply_symm_apply z
    have ht := (hcut j z.1 (rvUnitTupleValues z.2)).mpr hz
    have hx : x ∈ X.carrier := (hT x).mp (by simpa only [he] using ht.1)
    exact ⟨⟨x, hx⟩, he⟩
  let D := fun j => groundRVValueImage (Y j)
  have hD := fun j => groundRVValueImage_carrier (Y j)
  refine ⟨N, β, R, G, Y, D, hβ, hR, fun j => ⟨f.restrictTarget (Z j) (hZ j)⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, hz⟩, he⟩
      have haa : a.val = x := ha
      change e a.val ∈ (Z j).carrier at hz
      exact he ▸ haa ▸ hz
    · intro hz
      obtain ⟨a, ha⟩ := hZ j hz
      have he : e a.val = z := ha
      refine ⟨a.val, ⟨a, rfl, ?_⟩, he⟩
      change e a.val ∈ (Z j).carrier
      rw [he]
      exact hz
  · intro j
    ext x
    rw [hD j]
    constructor
    · intro hx
      exact ⟨((hY j x).mp hx).1, x, hx, rfl⟩
    · rintro ⟨hx, y, hy, he⟩
      apply (hY j x).mpr
      exact ⟨hx, hv y x he ▸ ((hY j y).mp hy).2⟩
  · intro j k hjk
    rw [hD j, hD k]
    apply Set.disjoint_left.mpr
    rintro γ ⟨x, hx, he⟩ ⟨y, hy, he'⟩
    have hvxy := hv x y (he.trans he'.symm)
    exact Set.disjoint_left.mp (hdis j k hjk) ((hY j x).mp hx).2
      (hvxy.symm ▸ ((hY k y).mp hy).2)
  · intro γ
    constructor
    · rintro ⟨x, hx, rfl⟩
      have ht := (hT x).mpr hx
      have hval : v x ∈ (groundMixedValueMap T).image.carrier := by
        rw [groundMixedValueMap_image]
        exact ⟨((e x).1, rvUnitTupleValues (e x).2), ht, rfl⟩
      obtain ⟨j, hj⟩ := (hcov (v x)).mp hval
      exact ⟨j, (hD j).symm ▸ ⟨x, (hY j x).mpr ⟨hx, hj⟩, rfl⟩⟩
    · rintro ⟨j, hj⟩
      obtain ⟨x, hx, he⟩ := hD j ▸ hj
      exact ⟨x, ((hY j x).mp hx).1, he⟩

end DiamondIntegral.Section5
