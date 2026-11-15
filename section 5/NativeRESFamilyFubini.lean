import «section 5».RESLayoutTotalValues
import «section 5».RESLayoutUniformity

/-! Pointwise equality in the actual native RES quotient implies equality
of total RV-family values. All finite witnesses are chosen over the
original parameter base before the common finite partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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

theorem native_res_family_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : RESSetSchema B p a (fun _ => .rv)) (G : RESSetSchema B p b (fun _ => .rv))
    (hF : ∀ x : X, F.Valid hc (rvValues x.val))
    (hG : ∀ x : X, G.Valid hc (rvValues x.val))
    (he : ∀ x : X, nativeRESChartClass (F.chart hc (rvValues x.val) (hF x)) =
      nativeRESChartClass (G.chart hc (rvValues x.val) (hG x))) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F.domain) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X G.domain) := by
  have hf : ∀ z ∈ rawDomain X, F.Valid hc z := by
    rintro z ⟨x,hx,rfl⟩
    exact hF ⟨x,hx⟩
  have hg : ∀ z ∈ rawDomain X, G.Valid hc z := by
    rintro z ⟨x,hx,rfl⟩
    exact hG ⟨x,hx⟩
  obtain ⟨J,hJ⟩ := res_equality_finite_layout_catalog hκ hs B hr hγ _ (rawDomain X)
    (rawDomain_definable X) F G hf hg (by
      rintro z ⟨x,hx,rfl⟩
      exact he ⟨x,hx⟩)
  let e : Fin (Fintype.card ↥J) ≃ ↥J := (Fintype.equivFin ↥J).symm
  let V : Fin (Fintype.card ↥J) → GammaGroundDefSet hc B (rawRVSpace (M := M) p) := fun j =>
    ofRaw {z | (e j).val.Valid hc z} ((e j).val.valid_definable hc)
  have hcover : ∀ x ∈ X.carrier, ∃ j, x ∈ (V j).carrier := by
    intro x hx
    obtain ⟨W,hW,hv⟩ := hJ (rvValues x) ⟨x,hx,rfl⟩
    obtain ⟨j,hj⟩ := e.surjective ⟨W,hW⟩
    refine ⟨j,?_⟩
    change (e j).val.Valid hc (rvValues x)
    rw [hj]
    exact hv
  obtain ⟨N,A,hA,hd,hcov⟩ := gammaGround_finite_cover_partition X V hcover
  have hpiece (i : Fin N) :
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily (A i) F.domain) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily (A i) G.domain) := by
    rcases (hA i).2 with hempty | ⟨j,hj⟩
    · have hnil {r : ℕ} (D : GammaDomainFormula B p r (fun _ => .rv)) :
          (originalRVTotalFamily (A i) D).carrier = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact Set.notMem_empty _ (hempty ▸ ((originalRVTotalFamily_mem (A i) D u).mp hu).1)
      rw [nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind _ (hnil F.domain),
        nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind _ (hnil G.domain)]
    · exact (e j).val.total_native_equality h00 linear hκ hs hr hγ hΓ kind (A i)
        (fun x => hj x.property)
  have hpF := originalRVTotalFamily_base_partition X F.domain A hd hcov
  have hpG := originalRVTotalFamily_base_partition X G.domain A hd hcov
  rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ _ hpF.1 hpF.2,
    nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ _ hpG.1 hpG.2]
  exact Finset.sum_congr rfl (fun i _ => hpiece i)

end DiamondIntegral.Section5
