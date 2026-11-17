import «section 3».GammaNativeStructuralValues
import IntegrationSection6.FiniteGammaUniversalCharts

/-! Actual original-ground native label bijections preserving structural
volume give native finite RV isomorphisms with the identical label map.
Real specialization is used only to certify the internal presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaNativeIsoOfGroundBijection (U V : GammaObjectAt B Set.univ n)
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hv : ∀ u, (Section5.nativeRVGroundVolume U u).val = (Section5.nativeRVGroundVolume V (f.map u)).val) :
    GammaIsoAt U V := by
  let P := Section5.nativeRVGroundDomainEquiv (hc := hc) U
  let Q := Section5.nativeRVGroundDomainEquiv (hc := hc) V
  let e := P.symm.trans ((Equiv.ofBijective f.map f.bijective).trans Q)
  have hΓ : GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
      (q : Point (M := M) 0 (rvObjectArity V.object.obj)) =>
      ∃ u : rvObjectDomain U.object.obj, u.val=p.2 ∧ (e u).val=q.2) := by
    apply GammaGraphDefinable.congr (Section5.groundRV_gamma_map f.map)
    intro p q
    constructor
    · rintro ⟨u,hu,hv⟩
      refine ⟨P u,hu,?_⟩
      change (Q (f.map (P.symm (P u)))).val=q.2
      rw [P.symm_apply_apply]
      exact hv
    · rintro ⟨u,hu,hv⟩
      exact ⟨P.symm u,hu,hv⟩
  let F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ Set.univ
      (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ _ _ _ e (by
      obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize hΓ
      exact @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj))
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity V.object.obj))
        (B.real ∪ Set.range (rawTuple t)) Set.univ _ hr (Set.subset_univ _))
  have hvol (u : rvObjectDomain U.object.obj) :
      @RVObject.value M N Set.univ n U.object.obj u = @RVObject.value M N Set.univ n V.object.obj (F u) := by
    have hh := hv (P.symm u)
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value] at hh
    change @RVObject.value M N Set.univ n U.object.obj (P (P.symm u)) =
      @RVObject.value M N Set.univ n V.object.obj (Q (f.map (P.symm u))) at hh
    rw [P.apply_symm_apply] at hh
    exact hh
  exact {
    iso := @isoOfDefinableBijection M N Set.univ n U.object V.object F e.bijective
      (fun u => congrArg (@rvWeight M N n) (hvol u))
    graph := hΓ }

theorem gammaNativeIsoOfGroundBijection_map (U V : GammaObjectAt B Set.univ n)
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hv : ∀ u, (Section5.nativeRVGroundVolume U u).val = (Section5.nativeRVGroundVolume V (f.map u)).val)
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    (Section5.nativeRVGroundIso (gammaNativeIsoOfGroundBijection U V f hv)).map u = f.map u := by
  apply Subtype.ext
  rfl

end DiamondIntegral.Section3
