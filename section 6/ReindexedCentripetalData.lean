import «section 6».VFPermutationFocusGeometry

/-! Actual permitted centripetal data after a VF-coordinate change.
The focus graph, erased-coordinate covariance, all names and the exact
coefficient are transported over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def reindexVF (D : CentripetalData (G := G) A) (e : Fin n ≃ Fin n) :
    CentripetalData (G := G) (reindexedVFSet A e) where
  coordinate := e.symm D.coordinate
  activeTags := D.activeTags
  focus x u := D.focus (x ∘ e.symm) u
  focusMap := D.focusMap.comp (reindexedFocusProjection A D.activeTags e)
  focusMap_eq := by
    intro p
    change (D.focusMap (reindexedFocusProjection A D.activeTags e p)).val 0=
      D.focus (Function.update p.val.1 (e.symm D.coordinate) 0 ∘ e.symm) p.val.2
    rw [erased_comp_fin_equiv]
    exact D.focusMap_eq (reindexedFocusProjection A D.activeTags e p)
  sourceProper := reindexedVFSet_properInvariant A e D.sourceProper
  sourceDoublyBounded := reindexedVFSet_doublyBounded A e D.sourceDoublyBounded
  tagged := reindexedVFSet_tagged A e D.tagged
  continuous := by
    intro u hu
    have hPerm : Continuous (fun a : Fin n → VF M => a ∘ e.symm) :=
      continuous_pi (fun i => continuous_apply (e.symm i))
    have h := (D.continuous u hu).comp hPerm.continuousOn
      (show Set.MapsTo (fun a : Fin n → VF M => a ∘ e.symm)
        (vfFibre (reindexedVFSet A e).carrier u) (vfFibre A.carrier u) from
          fun a ha => (mem_reindexedVFSet A e (a,u)).mp ha)
    have hFun : (fun x : Fin n → VF M => D.focus (Function.update x (e.symm D.coordinate) 0 ∘ e.symm) u)=
        (fun x => D.focus (Function.update (x ∘ e.symm) D.coordinate 0) u) := by
      funext x
      rw [erased_comp_fin_equiv]
    rw [hFun]
    exact h
  focusRV := by
    intro p hp hu
    change rv M (D.focus (Function.update p.1 (e.symm D.coordinate) 0 ∘ e.symm) p.2)=
      rv M (p.1 (e.symm D.coordinate))
    rw [erased_comp_fin_equiv]
    exact D.focusRV (reindexVFPoint e.symm p) ((mem_reindexedVFSet A e p).mp hp) hu
  coefficient := D.coefficient
  coefficient_nonzero := D.coefficient_nonzero
  coefficient_nonnegative := D.coefficient_nonnegative
  coefficient_definable := D.coefficient_definable
  covariance := by
    intro u hu
    obtain ⟨α,β,hα,hβ,hInv,hCov,hDom⟩ := D.covariance u hu
    refine ⟨α,β ∘ e,hα,(fun i => hβ (e i)),?_,?_,?_⟩
    · intro a b hab
      have hOld : Congruent (fun i => if i=D.coordinate then α else β i)
          (a ∘ e.symm) (b ∘ e.symm) := by
        apply congruent_comp_fin_equiv _ e a b
        rw [coordinate_radius_comp_fin_equiv]
        exact hab
      exact (mem_reindexedVFSet A e (a,u)).trans
        ((hInv _ _ hOld).trans (mem_reindexedVFSet A e (b,u)).symm)
    · intro a ha b hb hab
      have hOld := congruent_comp_fin_equiv β e
        (Function.update a (e.symm D.coordinate) 0) (Function.update b (e.symm D.coordinate) 0) hab
      rw [erased_comp_fin_equiv,erased_comp_fin_equiv] at hOld
      change α.val < vfValue (D.focus (Function.update a (e.symm D.coordinate) 0 ∘ e.symm) u-
        D.focus (Function.update b (e.symm D.coordinate) 0 ∘ e.symm) u)
      rw [erased_comp_fin_equiv,erased_comp_fin_equiv]
      exact hCov (a ∘ e.symm) ((mem_reindexedVFSet A e (a,u)).mp ha)
        (b ∘ e.symm) ((mem_reindexedVFSet A e (b,u)).mp hb) hOld
    · intro a ha
      change α.val ≤ vfValue (D.coefficient*D.focus (Function.update a (e.symm D.coordinate) 0 ∘ e.symm) u)
      rw [erased_comp_fin_equiv]
      exact hDom (a ∘ e.symm) ((mem_reindexedVFSet A e (a,u)).mp ha)

end DiamondIntegral.Section6.CentripetalData
