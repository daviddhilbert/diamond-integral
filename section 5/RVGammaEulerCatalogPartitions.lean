import «section 5».RVGammaFamilyRestrictions
import «section 3».GammaGroundFiniteCoverPartition

/-! Every actual mixed family has a finite disjoint original-ground RV
base partition carrying a complete valid Euler certificate on each piece. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem rv_gamma_euler_certificate_partition
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    ∃ N : ℕ, ∃ A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p),
      ∃ C : Fin N → OriginalEulerCertificate B (fun _ : Fin p => .rv) n,
      (∀ i, (A i).carrier ⊆ X.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) ∧
      ∀ i (x : A i), (C i).ValidFor hc (rvGammaFamilySchema T) (rvUnitValues x.val) := by
  let R := rvUnitValues '' X.carrier
  have hR : DefinableOverBase B (fun _ => .rv) R := (gammaGroundRVUnit_definable_iff _).mp X.definable
  have hD : ∀ z ∈ R, originalGammaSourceValid hc (rvGammaFamilySchema T) z := by
    rintro z ⟨x,hx,rfl⟩
    exact rvGammaFamilySchema_valid T x
  obtain ⟨J,hJ⟩ := original_euler_finite_catalog hc h00 hκ hs hr hγ R hR (rvGammaFamilySchema T) hD
  let e : Fin (Fintype.card ↥J) ≃ ↥J := (Fintype.equivFin ↥J).symm
  let E : Fin (Fintype.card ↥J) → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p) := fun i =>
    gammaGroundRVUnitSetOfBase _ ((e i).val.validFor_definable hc (rvGammaFamilySchema T))
  have hcover : ∀ x ∈ X.carrier, ∃ i, x ∈ (E i).carrier := by
    intro x hx
    obtain ⟨C,hC,hv⟩ := hJ (rvUnitValues x) ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := e.surjective ⟨C,hC⟩
    refine ⟨i,?_⟩
    change (∀ j, sortEval SortTag.rv (rvUnitValues x j)) ∧ (e i).val.ValidFor hc (rvGammaFamilySchema T) (rvUnitValues x)
    rw [hi]
    exact ⟨(fun j => (x j).val.property),hv⟩
  obtain ⟨N,A,hA,hd,hcov⟩ := gammaGround_finite_cover_partition X E hcover
  have hchoose (i : Fin N) : ∃ C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n,
      ∀ x : A i, C.ValidFor hc (rvGammaFamilySchema T) (rvUnitValues x.val) := by
    rcases (hA i).2 with hempty | ⟨j,hj⟩
    · exact ⟨⟨0,Fin.elim0⟩,fun x => (Set.notMem_empty x.val (hempty ▸ x.property)).elim⟩
    · refine ⟨(e j).val,?_⟩
      intro x
      exact (hj x.property).2
  choose C hC using hchoose
  exact ⟨N,A,C,(fun i => (hA i).1),hd,hcov,hC⟩

end DiamondIntegral.Section5
