import IntegrationSection5.FibreFocusPresentation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}
open SpecialTransformations.Section3

def verticalMeanFocusData (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k) : FibreFocusData A 0 k where
  tagged := hTag
  locus := R.verticalHull
  locus_definable := R.verticalHull_definable
  center := verticalMeanCentre R
  center_graph := by
    have h := Map.graph_definable (R.meanMap h00 (d+1) (R.card_bound d hd) (verticalMeanActive R))
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext j
      fin_cases j
      exact hz.symm
  independent p hp q hq he := by
    have h := congrArg (dropHead (n := n) id) he
    rw [dropHead_erase_zero,dropHead_erase_zero] at h
    exact congrArg (fun b => Barycentre.mean (R.fibre b)) h
  center_sameRV p hp := by
    obtain ⟨x,hx,hxp⟩ := hp.2
    have hRoots : ∀ y ∈ R.fibre (dropHead id p), rv y = rv (vfAt p 0) := by
      intro y hy
      have hyt := hTag _ (R.subset ((R.mem_fibre _ _).mp hy))
      exact hyt.symm.trans (hTag p hp.1)
    exact mean_sameRV h00 (R.fibre (dropHead id p)) ⟨x,hx⟩ (vfAt p 0) hRoots
  locus_saturated p hp q hq hs ho := by
    have hd : dropHead id p = dropHead id q := Prod.ext (funext (fun j => ho j.succ (Fin.succ_ne_zero j))) ((sameRV_iff _ _).mp hs).2
    change (∃ x ∈ R.fibre (dropHead id p), rv x = rv (vfAt p 0)) ↔
      (∃ x ∈ R.fibre (dropHead id q), rv x = rv (vfAt q 0))
    have hr : rv (vfAt p 0) = rv (vfAt q 0) := ((sameRV_iff _ _).mp hs).1 0
    rw [hd,hr]

theorem verticalMeanFocusData_eta (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k) (p : A) :
    (verticalMeanFocusData R h00 d hd hTag).eta p.val = (verticalMeanMap R h00 d hd p).val := rfl

end IntegrationInACVF.Section5
