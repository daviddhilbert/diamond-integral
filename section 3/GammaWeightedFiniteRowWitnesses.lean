import «section 3».GammaParametricFormConstraints
import Integration7.HKWeightedFiniteRowWitnesses

/-! An actual isomorphism of finite rows preserving arbitrary Gamma
forms promotes to a globally Gamma-constrained original-base formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem gammaWeighted_finite_row_formula_witness
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)
    (F : GammaFiniteRVSchema B p a 0 sp) (G : GammaFiniteRVSchema B p b 0 sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (hFA : F.rowDomain z ⊆ A.carrier) (hGD : G.rowDomain z ⊆ D.carrier)
    (e : GammaIso ⟨B.real ∪ Set.range z,B.gamma⟩
      {q : Point (M := M) 0 a | q.2 ∈ F.rowDomain z}
      {q : Point (M := M) 0 b | q.2 ∈ G.rowDomain z})
    (he : ∀ u, ω ⟨u.val.2,hFA u.property⟩ = π ⟨(e.equiv u).val.2,hGD (e.equiv u).property⟩) :
    ∃ H : GammaRelationFormula B p a b sp,
      H.val ⊆ gammaParametricFormConstraint A D ω π sp ∧ (gammaFiniteRowChartSchema F G H).valid z := by
  have hFD : rvValues '' F.rowDomain z = {r | Fin.append z r ∈ F.domain} :=
    Set.ext (fun r => (F.raw_row_domain_iff z r).symm)
  have hGD' : rvValues '' G.rowDomain z = {r | Fin.append z r ∈ G.domain} :=
    Set.ext (fun r => (G.raw_row_domain_iff z r).symm)
  let E := (IntegrationInACVF.Section7.HK.pureRVPointSortedIso e).congr hFD hGD'
  have hE : ∀ u, Fin.append (Fin.append z u.val) (E.equiv u).val ∈ gammaParametricFormConstraint A D ω π sp := by
    intro u
    let q := (IntegrationInACVF.Section7.HK.pureRVPointRawEquiv (F.rowDomain z)).symm
      ⟨u.val,(Set.ext_iff.mp hFD u.val).mpr u.property⟩
    have hq : rvValues q.val.2 = u.val := rfl
    have hout : (E.equiv u).val = rvValues (e.equiv q).val.2 := by
      rw [IntegrationInACVF.Section7.HK.sorted_iso_congr_value]
      have hh := IntegrationInACVF.Section7.HK.pure_rv_point_sorted_iso_value e q
      have hqu : IntegrationInACVF.Section7.HK.pureRVPointRawEquiv (F.rowDomain z) q =
          ⟨u.val,(Set.ext_iff.mp hFD u.val).mpr u.property⟩ :=
        (IntegrationInACVF.Section7.HK.pureRVPointRawEquiv (F.rowDomain z)).apply_symm_apply _
      rw [hqu] at hh
      exact hh
    rw [hout,← hq]
    exact (gammaParametricFormConstraint_append A D ω π sp z hF.1
      ⟨q.val.2,hFA q.property⟩ ⟨(e.equiv q).val.2,hGD (e.equiv q).property⟩).mpr (he q)
  obtain ⟨C,hCK,hC⟩ := IntegrationInACVF.Section7.HK.promote_row_bijection_within z hF.1
    (gammaParametricFormConstraint A D ω π sp) (gammaParametricFormConstraint_definable A D ω π sp) E hE
  refine ⟨⟨C.carrier,C.definable⟩,hCK,hF,hG,hC,?_⟩
  refine ⟨hF.1,?_⟩
  intro r hr hH hV hW
  exact congrArg (fun t : Fin 0 → M => SpecialTransformations.Section7.rawWeight t) (Subsingleton.elim _ _)

end DiamondIntegral.Section3
