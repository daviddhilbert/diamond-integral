import «section 5».OriginalFixedRVBijectionPromotion
import «section 5».OriginalRVTotalGraphs
import «section 5».NativeRVSetArithmetic
import «section 5».NativeRawWeightedValues
import «section 3».GammaGroundFiniteCoverPartition
import IntegrationSection6.GammaWitnessUniformity

/-! Original-base saturation uniformizes actual bijective fibre graphs.
Their total native values agree by a finite original-base partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem original_rv_bijection_finite_catalog
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (he : ∀ x : X, Nonempty (GammaGroundBijection
      (originalRVRowDomain hc D (rvValues x.val)) (originalRVRowDomain hc E (rvValues x.val)))) :
    ∃ J : Finset (GammaRelationFormula B p a b (fun _ => .rv)),
      ∀ z ∈ rawDomain X, ∃ H ∈ J, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
        D.val E.val H.val z := by
  apply gamma_finite_witnesses hκ hs hr hγ (fun _ => .rv) (rawDomain X) (rawDomain_definable X)
    (fun H : GammaRelationFormula B p a b (fun _ => .rv) =>
      {z | bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv) D.val E.val H.val z})
    (fun H => gamma_bijection_validity_definable (fun _ => .rv) (fun _ => .rv) (fun _ => .rv)
      D.property E.property H.property)
  rintro z ⟨x,hx,rfl⟩
  obtain ⟨f⟩ := he ⟨x,hx⟩
  exact original_fixed_rv_bijection_schema_at_parameter hc B (fun _ => .rv) (rvValues x)
    (fun i => (x i).property) D E _ _ (originalRVRowDomain_raw D _).symm
      (originalRVRowDomain_raw E _).symm f

theorem originalRVTotalFamily_base_partition
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) {ι : Type} [Fintype ι]
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint (originalRVTotalFamily (A i) D).carrier
      (originalRVTotalFamily (A j) D).carrier) ∧
    ∀ u, u ∈ (originalRVTotalFamily X D).carrier ↔ ∃ i, u ∈ (originalRVTotalFamily (A i) D).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact Set.disjoint_left.mp (hd i j hij)
      ((originalRVTotalFamily_mem (A i) D u).mp hi).1
      ((originalRVTotalFamily_mem (A j) D u).mp hj).1
  · intro u
    constructor
    · intro h
      obtain ⟨hx,hu⟩ := (originalRVTotalFamily_mem X D u).mp h
      obtain ⟨i,hi⟩ := (hcov _).mp hx
      exact ⟨i,(originalRVTotalFamily_mem (A i) D u).mpr ⟨hi,hu⟩⟩
    · rintro ⟨i,h⟩
      obtain ⟨hi,hu⟩ := (originalRVTotalFamily_mem (A i) D u).mp h
      exact (originalRVTotalFamily_mem X D u).mpr ⟨(hcov _).mpr ⟨i,hi⟩,hu⟩

theorem original_rv_total_value_of_pointwise_bijections
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (he : ∀ x : X, Nonempty (GammaGroundBijection
      (originalRVRowDomain hc D (rvValues x.val)) (originalRVRowDomain hc E (rvValues x.val)))) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X E) := by
  obtain ⟨J,hJ⟩ := original_rv_bijection_finite_catalog hκ hs hr hγ X D E he
  let e : Fin (Fintype.card ↥J) ≃ ↥J := (Fintype.equivFin ↥J).symm
  let V : Fin (Fintype.card ↥J) → GammaGroundDefSet hc B (rawRVSpace (M := M) p) := fun j =>
    ofRaw {z | bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv) D.val E.val (e j).val.val z}
      (gamma_bijection_validity_definable (fun _ => .rv) (fun _ => .rv) (fun _ => .rv)
        D.property E.property (e j).val.property)
  have hcover : ∀ x ∈ X.carrier, ∃ j, x ∈ (V j).carrier := by
    intro x hx
    obtain ⟨H,hH,hv⟩ := hJ (rvValues x) ⟨x,hx,rfl⟩
    obtain ⟨j,hj⟩ := e.surjective ⟨H,hH⟩
    refine ⟨j,?_⟩
    change bijectiveMapRowValid _ _ _ _ (e j).val.val _
    rw [hj]
    exact hv
  obtain ⟨N,A,hA,hd,hcov⟩ := gammaGround_finite_cover_partition X V hcover
  have hpiece (i : Fin N) :
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily (A i) D) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily (A i) E) := by
    rcases (hA i).2 with hempty | ⟨j,hj⟩
    · have hnil {r : ℕ} (F : GammaDomainFormula B p r (fun _ => .rv)) :
          (originalRVTotalFamily (A i) F).carrier = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact Set.notMem_empty _ (hempty ▸ ((originalRVTotalFamily_mem (A i) F u).mp hu).1)
      rw [nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind _ (hnil D),
        nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind _ (hnil E)]
    · exact nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
        (originalRVTotalBijection (A i) D E (e j).val (fun x => hj x.property))
  have hpD := originalRVTotalFamily_base_partition X D A hd hcov
  have hpE := originalRVTotalFamily_base_partition X E A hd hcov
  rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ _ hpD.1 hpD.2,
    nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ _ hpE.1 hpE.2]
  exact Finset.sum_congr rfl (fun i _ => hpiece i)

end DiamondIntegral.Section5
