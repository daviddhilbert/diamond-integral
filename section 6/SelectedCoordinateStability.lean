import «section 6».SelectedProgramContexts
import «section 6».JointCoordinateStability

/-! The actual source with arbitrary retained labels is invariant
in the active coordinate at the old variable aperture. This follows
from actual local components and preserves every protected membership. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}

theorem selectedUnaryBasePoint_update_tail (π : Fin r → Fin q)
    (p : Mixed M (n+1) q) (j : Fin n) (x : VF M) :
    selectedUnaryBasePoint π (Function.update p.1 j.succ x,p.2)=selectedUnaryBasePoint π p := by
  apply Prod.ext
  · funext i
    change Function.update p.1 j.succ x 0=p.1 0
    exact Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
  · rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem selected_coordinate_stable_of_fibre_components
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A P : MixedSetParameterTemplate (M := M) S 1 n s)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q)
    (hC : IsRVPullback C.carrier) (j : Fin n) (U : Set (Fin q → RVInfinity M))
    (ρ : (Fin q → RVInfinity M) → Gamma M)
    (hLocal : ∀ p ∈ (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η P)).carrier,
      p.2 ∈ U → ∃ b : B,∃ hb : selectedUnaryBasePoint π p=b.val,
        ∃ D : CentripetalData (G := G) (A.fibre (unaryFamilyParameter η b)),
        ∃ E : CentripetalData (G := G) (P.fibre (unaryFamilyParameter η b)),
          D.coordinate=j ∧ ApertureRestrictionData D E ∧ p.2 ∘ σ ∈ D.activeTags.carrier ∧
          (ρ p.2).val=vfValue (E.coefficient*E.extendedFocus (Fin.tail p.1,p.2 ∘ σ))) :
    ∀ p ∈ (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η P)).carrier,
      p.2 ∈ U → ∀ x : VF M,(ρ p.2).val < vfValue (p.1 j.succ-x) →
        (Function.update p.1 j.succ x,p.2) ∈
          (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η P)).carrier := by
  intro p hp hu x hClose
  obtain ⟨b,hb,D,E,hCoord,hCompat,hActive,hCut⟩ := hLocal p hp hu
  obtain ⟨hpC,hpPi⟩ := (mem_rvLabelPullback C _ _ p).mp hp
  have hBase := (selectedJointPoint_base π σ p).trans hb
  have hpLocal := (mem_unaryIndexedMixedFamily_at η P (selectedJointPoint π σ p) b hBase).mp hpPi
  rw [selectedJointPoint_local] at hpLocal
  have hOldClose : vfValue (E.coefficient*E.extendedFocus (Fin.tail p.1,p.2 ∘ σ)) <
      vfValue ((Fin.tail p.1) E.coordinate-x) := by
    rw [hCompat.coordinate,hCoord,← hCut]
    exact hClose
  have hNewPi := E.coordinate_cutoff_stable (Fin.tail p.1,p.2 ∘ σ) hpLocal
    ((hCompat.active_iff hpLocal).mpr hActive) x hOldClose
  rw [hCompat.coordinate,hCoord] at hNewPi
  have hLocalRV := D.tagged _ (hCompat.subset hpLocal) _ (hCompat.subset hNewPi) rfl
  have hTail := unaryIndexedTail_update (r := q) (s := 0) p j x
  have hRV : tupleRV M p.1=tupleRV M (Function.update p.1 j.succ x) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change rv M (p.1 0)=rv M (Function.update p.1 j.succ x 0)
      rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    · have hk := congrFun hLocalRV k
      change rv M ((Fin.tail p.1) k)=rv M (Function.update (Fin.tail p.1) j x k) at hk
      exact hk.trans (congrArg (rv M) (congrFun hTail k).symm)
  have hNewC : (Function.update p.1 j.succ x,p.2) ∈ C.carrier :=
    rvPullback_mem_of_sameRV hC hpC hRV rfl
  apply (mem_rvLabelPullback C _ _ _).mpr
  refine ⟨hNewC,(mem_unaryIndexedMixedFamily_at η P (selectedJointPoint π σ _) b
    ((selectedJointPoint_base π σ _).trans ((selectedUnaryBasePoint_update_tail π p j x).trans hb))).mpr ?_⟩
  rw [selectedJointPoint_local]
  change (Fin.tail (Function.update p.1 j.succ x),p.2 ∘ σ) ∈ (P.fibre (unaryFamilyParameter η b)).carrier
  rw [hTail]
  exact hNewPi

end DiamondIntegral.Section6
