import «section 5».AngularValuePartition
import «section 3».RVGroundAngularPartition
import «section 3».GammaGroundRVUnitDomains

/-! The initial angular partition is itself induced by original values.
The finite guarded-DNF patterns are Gamma predicates over the original
ground, rather than arbitrary disjoint RV subsets. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GuardedRVNormalForm
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem ground_global_angular_value_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    ∃ N : ℕ,
      ∃ Y : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ D : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)),
      (∀ i, Nonempty (RVAngularCell (Y i).carrier)) ∧
      (∀ i, (Y i).carrier = X.carrier ∩ rvUnitTupleValues ⁻¹' (D i).carrier) ∧
      (∀ i j, i ≠ j → Disjoint (D i).carrier (D j).carrier) ∧
      (∀ γ, γ ∈ rvUnitTupleValues '' X.carrier ↔ ∃ i, γ ∈ (D i).carrier) := by
  have hA := (gammaGroundRVUnit_definable_iff X.carrier).mp X.definable
  obtain ⟨p, F, hF⟩ := definableRV_guarded_DNF hA.common_names
  let J := RVDNFGlobalPattern F
  letI := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let P : Fin (Fintype.card J) → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)) :=
    fun i => ⟨{γ | globalGammaPattern F (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i) γ},
      gammaGroundGammaPower_predicate_definable _
        (globalGammaPattern_definable hκ hs h00 hc B hsmall p F (e i))⟩
  let Y := fun i => X.inter (gammaGroundRVUnitGammaPreimage (P i))
  have hmatch : ∀ x, x ∈ X.carrier ↔
      PolarityDNF.holds (RVLiteral.comparison (sourceVFFixedValues p n) (sourceRVFixedParameters p)
        (fun i => (x i : CanonicalRV.RVSort M))) F := by
    intro x
    have hx : rvUnitValues x ∈ rvUnitValues '' X.carrier ↔ x ∈ X.carrier :=
      ⟨fun ⟨y, hy, he⟩ => rvUnitValues_injective he ▸ hy, fun h => ⟨x, h, rfl⟩⟩
    exact hx.symm.trans (hF x).1
  have hY : ∀ i, (Y i).carrier =
      rvDNFPatternCell F (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i) := by
    intro i
    ext x
    change (x ∈ X.carrier ∧
      globalGammaPattern F (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i)
        (rvUnitTupleValues x)) ↔ _
    rw [hmatch x]
    exact and_congr Iff.rfl (globalGammaPattern_semantics F _ _ (e i) x)
  have hdis : ∀ i j, i ≠ j → Disjoint (Y i).carrier (Y j).carrier := by
    intro i j hij
    rw [hY i, hY j]
    exact rvDNFPatternCells_disjoint F _ _ (e i) (e j) (fun h => hij (e.injective h))
  have hcover : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (Y i).carrier := by
    intro x
    rw [hmatch x, rvDNFPatternCells_cover]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨i, hi⟩ := e.surjective a
      exact ⟨i, (hY i).symm ▸ (hi.symm ▸ ha)⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, hY i ▸ hi⟩
  have hinv : ∀ i x y, x ∈ X.carrier → y ∈ (Y i).carrier →
      rvUnitTupleValues x = rvUnitTupleValues y → x ∈ (Y i).carrier := by
    intro i x y hx hy hv
    refine ⟨hx, ?_⟩
    change rvUnitTupleValues x ∈ (P i).carrier
    rw [hv]
    exact hy.2
  let D := fun i => groundRVValueImage (Y i)
  have hD := fun i => groundRVValueImage_carrier (Y i)
  refine ⟨Fintype.card J, Y, D, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hY i]
    exact rvDNFPatternCell_angularCell F _ _ (e i)
  · intro i
    ext x
    rw [hD i]
    constructor
    · intro hx
      exact ⟨hx.1, x, hx, rfl⟩
    · rintro ⟨hx, y, hy, hv⟩
      exact hinv i x y hx hy hv.symm
  · intro i j hij
    rw [hD i, hD j]
    apply Set.disjoint_left.mpr
    rintro γ ⟨x, hx, hvx⟩ ⟨y, hy, hvy⟩
    exact Set.disjoint_left.mp (hdis i j hij) hx
      (hinv j x y hx.1 hy (hvx.trans hvy.symm))
  · intro γ
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := (hcover x).mp hx
      exact ⟨i, (hD i).symm ▸ ⟨x, hi, rfl⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨x, hx, hv⟩ := hD i ▸ hi
      exact ⟨x, hx.1, hv⟩

end DiamondIntegral.Section5
