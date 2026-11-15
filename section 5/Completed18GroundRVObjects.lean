import «section 5».Completed18GroundCodeGraphs
import IntegrationSection6.GammaNonzeroClasses
import IntegrationSection6.GammaFiniteGraphObjects

/-! A local finite-label RV object is an actual full-weight object in
the completed [18] RV category, with the same domain and label function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def groundRVPresentation (U : GammaGroundRVObject hc B k) :
    GammaFiniteGraphPresentation B U.arity k U.domain.carrier
      (fun x y => ∃ u : U.domain,u.val=x ∧ (U.volume u).val=y) :=
  Classical.choice (exists_gammaFiniteGraphPresentation (groundRV_gamma_set U.domain)
    (groundRV_gamma_volume U) (by
      intro x
      refine ⟨(U.volume ⟨x.val,x.property⟩).val,⟨⟨x.val,x.property⟩,rfl,rfl⟩,?_⟩
      rintro y ⟨u,hu,hv⟩
      have he : u = ⟨x.val,x.property⟩ := Subtype.ext hu
      exact hv.symm.trans (congrArg (fun v : U.domain => (U.volume v).val) he)) (by
      intro y
      let t : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k) := ⟨y,Set.mem_univ _⟩
      apply (U.finite t).subset
      rintro x ⟨u,hu,hv⟩
      have he : u = x := Subtype.ext hu
      apply Subtype.ext
      exact (congrArg (fun v : U.domain => (U.volume v).val) he).symm.trans hv))

def groundRVAt (U : GammaGroundRVObject hc B k) : GammaObjectAt B Set.univ k :=
  gammaObjectAtExtend (groundRVPresentation U).toGamma (Set.subset_univ _)

theorem groundRVAt_domain (U : GammaGroundRVObject hc B k) :
    (@DefSet.carrier LRV M N _ Set.univ
      (SpecialTransformations.Section5.rvObjectDomain (groundRVAt U).object.obj)) = U.domain.carrier :=
  (groundRVPresentation U).domain_eq

theorem groundRVAt_volume (U : GammaGroundRVObject hc B k)
    (u : SpecialTransformations.Section5.rvObjectDomain (groundRVAt U).object.obj) :
    ∃ a : U.domain,a.val=u.val ∧ (U.volume a).val =
      (SpecialTransformations.Section5.rvObjectVolume (groundRVAt U).object.obj u).val := by
  exact ((groundRVPresentation U).graph_iff _ _).mp ⟨u,rfl,rfl⟩ |>.2

theorem groundRVAt_full (U : GammaGroundRVObject hc B k) : GammaFullWeightAt (groundRVAt U) := by
  intro u
  obtain ⟨a,ha,hv⟩ := groundRVAt_volume U u
  change @rvWeight M N k
    (SpecialTransformations.Section5.rvObjectVolume (groundRVAt U).object.obj u).val = k
  rw [← hv]
  have hz : @iRVZero M N = @iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
  have hn (i : Fin k) : ((U.volume a).val i).val ≠ @iRVZero M N :=
    hz.symm ▸ U.nonzero a i
  change (∑ i : Fin k,if ((U.volume a).val i).val ≠ @iRVZero M N then 1 else 0) = k
  calc
    (∑ i : Fin k,if ((U.volume a).val i).val ≠ @iRVZero M N then 1 else 0) =
        ∑ _i : Fin k,(1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact if_pos (hn i)
    _ = k := by simp

end DiamondIntegral.Section5
