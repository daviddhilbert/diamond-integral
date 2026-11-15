import «section 5».NativeRVRectangleFamilyFubini
import «section 5».RVRectangleUniformity

/-! Fubini for actual original-base RV families: equality of native row
values at every ambient parameter implies equality of literal total
values. Complete rectangle packages are selected by saturation. -/
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

theorem native_rv_family_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (E : GammaDomainFormula B p b (fun _ => .rv))
    (he : ∀ x : X, nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D (rvValues x.val) =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X E) := by
  obtain ⟨J,hJ⟩ := rv_rectangle_finite_catalog hc h00 hκ hs hr hγ hΓ (rawDomain X) (rawDomain_definable X) D
  obtain ⟨K,hK⟩ := rv_rectangle_finite_catalog hc h00 hκ hs hr hγ hΓ (rawDomain X) (rawDomain_definable X) E
  let e : Fin (Fintype.card (↥J × ↥K)) ≃ (↥J × ↥K) := (Fintype.equivFin _).symm
  let V : Fin (Fintype.card (↥J × ↥K)) → GammaGroundDefSet hc B (rawRVSpace (M := M) p) := fun j =>
    ofRaw {z | (e j).1.val.Valid hc z ∧ (e j).2.val.Valid hc z}
      (((e j).1.val.valid_definable hc).inter ((e j).2.val.valid_definable hc))
  have hcover : ∀ x ∈ X.carrier, ∃ j, x ∈ (V j).carrier := by
    intro x hx
    obtain ⟨W,hW,hw⟩ := hJ (rvValues x) ⟨x,hx,rfl⟩
    obtain ⟨U,hU,hu⟩ := hK (rvValues x) ⟨x,hx,rfl⟩
    obtain ⟨j,hj⟩ := e.surjective (⟨W,hW⟩,⟨U,hU⟩)
    refine ⟨j,?_⟩
    change (e j).1.val.Valid hc (rvValues x) ∧ (e j).2.val.Valid hc (rvValues x)
    rw [hj]
    exact ⟨hw,hu⟩
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
    · exact native_rv_rectangle_family_fubini h00 linear hκ hs hr hγ hΓ kind (A i)
        (e j).1.val (e j).2.val (fun x => (hj x.property).1) (fun x => (hj x.property).2)
        (fun x => he ⟨x.val,(hA i).1 x.property⟩)
  have hpD := originalRVTotalFamily_base_partition X D A hd hcov
  have hpE := originalRVTotalFamily_base_partition X E A hd hcov
  rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ _ hpD.1 hpD.2,
    nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ _ hpE.1 hpE.2]
  exact Finset.sum_congr rfl (fun i _ => hpiece i)

end DiamondIntegral.Section5
