import «section 5».GroundValueCells

/-! Original-base definable assembly of mixed RV/Gamma rectangles.
All value cells, fixed-value residue factors and Gamma factors in the
conclusion are definable over the input real/Gamma ground. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {n m N : ℕ}

def groundPatternGamma
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m))))
    (G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (β : Fin n → Values.Gamma (M := M))
    (hβ : ∀ i, GammaDefinableClosureAtBase B (β i)) (s : Finset (Fin N)) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)) :=
  (GammaGroundMap.ofGlobal (groundValuePattern T G β hβ s)
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
    (universalProductSnd _ _ B.real) (fun _ => Set.mem_univ _)).image

theorem groundPatternGamma_carrier
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m))))
    (G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (β : Fin n → Values.Gamma (M := M))
    (hβ : ∀ i, GammaDefinableClosureAtBase B (β i)) (s : Finset (Fin N)) :
    (groundPatternGamma T G β hβ s).carrier =
      rectangleGammaCell rvUnitTupleValues id T.carrier (fun i => (G i).carrier) β s := by
  ext γ
  constructor
  · rintro ⟨q, hq⟩
    have h := (Set.ext_iff.mp (groundValuePattern_carrier T G β hβ s) q.val).mp q.property
    change q.val.2 = γ at hq
    change (β, γ) ∈ rectangleValueCell rvUnitTupleValues id T.carrier (fun i => (G i).carrier) β s
    have he : q.val = (β, γ) := Prod.ext h.2.1 hq
    exact he ▸ h
  · intro h
    have hh : (β, γ) ∈ (groundValuePattern T G β hβ s).carrier :=
      (Set.ext_iff.mp (groundValuePattern_carrier T G β hβ s) (β, γ)).mpr h
    exact ⟨⟨(β, γ), hh⟩, rfl⟩

/-- A finite rectangle cover with finite active value supports produces
an original-ground definable partition of the actual joint value image.
It is a partition by values, rather than just a partition of RV points. -/
theorem ground_finite_value_rectangle_partition
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m))))
    (R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (hfinite : ∀ i, (rvUnitTupleValues '' (R i).carrier).Finite)
    (hT : ∀ r γ, (r, γ) ∈ T.carrier ↔ ∃ i, r ∈ (R i).carrier ∧ γ ∈ (G i).carrier) :
    ∃ L : ℕ,
      ∃ β : Fin L → Fin n → Values.Gamma (M := M),
      ∃ Q : Fin L → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ H : Fin L → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)),
      ∃ D : Fin L → GammaGroundDefSet hc B
        (((volumeGammaSpace hc).power (Fin n)).prod ((volumeGammaSpace hc).power (Fin m))),
      (∀ j i, GammaDefinableClosureAtBase B (β j i)) ∧
      (∀ j, rvUnitTupleValues '' (Q j).carrier ⊆ {β j}) ∧
      (∀ j k, j ≠ k → Disjoint (D j).carrier (D k).carrier) ∧
      (∀ q, q ∈ (groundMixedValueMap T).image.carrier ↔ ∃ j, q ∈ (D j).carrier) ∧
      (∀ j r γ, (r, γ) ∈ T.carrier ∧ (rvUnitTupleValues r, γ) ∈ (D j).carrier ↔
        r ∈ (Q j).carrier ∧ γ ∈ (H j).carrier) := by
  obtain ⟨L, β, s, hdis, hcov, hrect, hfixed, hactive⟩ :=
    finite_valueInduced_rectangle_partition rvUnitTupleValues id T.carrier
      (fun i => (R i).carrier) (fun i => (G i).carrier) hT hfinite
  have hmap : (groundMixedActiveMap T).image.carrier =
      (rvUnitTupleValues ∘ Prod.fst) '' T.carrier := by
    ext γ
    exact ⟨fun ⟨x, hx⟩ => ⟨x.val, x.property, hx⟩,
      fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩
  have hfin : (groundMixedActiveMap T).image.carrier.Finite := by
    rw [hmap]
    exact rectangle_active_values_finite rvUnitTupleValues id T.carrier
      (fun i => (R i).carrier) (fun i => (G i).carrier) hT hfinite
  have hβ : ∀ j i, GammaDefinableClosureAtBase B (β j i) := by
    intro j
    apply gammaGroundGamma_finite_tuple_point_definable (groundMixedActiveMap T).image hfin
    exact hmap.symm ▸ hactive j
  let Q := fun j => groundResiduePattern R (β j) (hβ j) (s j)
  let H := fun j => groundPatternGamma T G (β j) (hβ j) (s j)
  let D := fun j => groundValuePattern T G (β j) (hβ j) (s j)
  have hD := fun j => groundValuePattern_carrier T G (β j) (hβ j) (s j)
  refine ⟨L, β, Q, H, D, hβ, hfixed, ?_, ?_, ?_⟩
  · intro j k hjk
    rw [hD j, hD k]
    exact hdis j k hjk
  · intro q
    rw [groundMixedValueMap_image]
    constructor
    · intro hq
      obtain ⟨j, hj⟩ := (hcov q).mp hq
      exact ⟨j, (hD j).symm ▸ hj⟩
    · rintro ⟨j, hj⟩
      exact (hcov q).mpr ⟨j, hD j ▸ hj⟩
  · intro j r γ
    rw [hD j]
    have hh := Set.ext_iff.mp (hrect j) (r, γ)
    change ((r, γ) ∈ T.carrier ∧
      (rvUnitTupleValues r, γ) ∈ rectangleValueCell rvUnitTupleValues id T.carrier
        (fun i => (G i).carrier) (β j) (s j)) ↔
      r ∈ (Q j).carrier ∧ γ ∈ (H j).carrier
    change _ ↔ _ ∧ γ ∈ (groundPatternGamma T G (β j) (hβ j) (s j)).carrier
    rw [groundPatternGamma_carrier]
    exact hh

/-- The required rectangle hypotheses come from the locally proved
Section 3 separation theorem, with its actual model/base assumptions. -/
theorem ground_mixed_value_normal_form {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m))))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hA : (rvUnitTupleValues '' A.carrier).Finite)
    (hsub : ∀ r γ, (r, γ) ∈ T.carrier → r ∈ A.carrier) :
    ∃ L : ℕ,
      ∃ β : Fin L → Fin n → Values.Gamma (M := M),
      ∃ Q : Fin L → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ H : Fin L → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)),
      ∃ D : Fin L → GammaGroundDefSet hc B
        (((volumeGammaSpace hc).power (Fin n)).prod ((volumeGammaSpace hc).power (Fin m))),
      (∀ j i, GammaDefinableClosureAtBase B (β j i)) ∧
      (∀ j, rvUnitTupleValues '' (Q j).carrier ⊆ {β j}) ∧
      (∀ j k, j ≠ k → Disjoint (D j).carrier (D k).carrier) ∧
      (∀ q, q ∈ (groundMixedValueMap T).image.carrier ↔ ∃ j, q ∈ (D j).carrier) ∧
      (∀ j r γ, (r, γ) ∈ T.carrier ∧ (rvUnitTupleValues r, γ) ∈ (D j).carrier ↔
        r ∈ (Q j).carrier ∧ γ ∈ (H j).carrier) := by
  obtain ⟨N, R, G, hfinite, _hdis, hcov⟩ :=
    gammaGroundRVUnitMixed_definable_products hκ hs h00 hsmall hγsmall hΓ T A hA hsub
  exact ground_finite_value_rectangle_partition T R G hfinite hcov

end DiamondIntegral.Section5
