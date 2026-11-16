import «section 6».UnaryIndexedFocusGraphs
import «section 6».ProtectedTaggedApertureRadii

/-! Coordinate invariance at a variable old aperture descends from
the actual fibrewise permitted components. The tagged local ambient
preserves all leading terms, keeping every replacement in the current
joint pullback and in its actual protected piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem unaryIndexedBasePoint_update (p : Mixed M (n+1) (r+s)) (j : Fin n) (x : VF M) :
    unaryFamilyBasePoint (Function.update p.1 j.succ x,p.2)=unaryFamilyBasePoint p := by
  apply Prod.ext
  · funext i
    fin_cases i
    change Function.update p.1 j.succ x 0=p.1 0
    exact Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
  · rfl

theorem unaryIndexedTail_update (p : Mixed M (n+1) (r+s)) (j : Fin n) (x : VF M) :
    Fin.tail (Function.update p.1 j.succ x)=Function.update (Fin.tail p.1) j x := by
  funext i
  by_cases hi : i=j
  · subst i
    simp only [Fin.tail,Function.update_self]
  · have hSucc : i.succ ≠ j.succ := fun h => hi (Fin.succ_injective _ h)
    simp only [Fin.tail,Function.update_of_ne hi,Function.update_of_ne hSucc]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem joint_coordinate_stable_of_fibre_components
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A P : MixedSetParameterTemplate (M := M) S 1 n s)
    (W Q : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hW : IsRVPullback W.carrier)
    (hQ : Q.carrier=W.carrier ∩ (unaryIndexedMixedFamily η P).carrier)
    (j : Fin n) (U : DefSet (rawRVSpace (M := M) (r+s)) S)
    (ρ : (Fin (r+s) → RVInfinity M) → Gamma M)
    (hLocal : ∀ p ∈ Q.carrier,p.2 ∈ U.carrier →
      ∃ b : B,∃ hb : unaryFamilyBasePoint p=b.val,
        ∃ D : CentripetalData (G := G) (A.fibre (unaryFamilyParameter η b)),
        ∃ E : CentripetalData (G := G) (P.fibre (unaryFamilyParameter η b)),
          D.coordinate=j ∧ ApertureRestrictionData D E ∧
          p.2 ∘ Fin.natAdd r ∈ D.activeTags.carrier ∧
          (ρ p.2).val=vfValue (E.coefficient*E.extendedFocus (Fin.tail p.1,p.2 ∘ Fin.natAdd r))) :
    ∀ p ∈ Q.carrier,p.2 ∈ U.carrier → ∀ x : VF M,
      (ρ p.2).val < vfValue (p.1 j.succ-x) →
        (Function.update p.1 j.succ x,p.2) ∈ Q.carrier := by
  intro p hp hu x hClose
  obtain ⟨b,hb,D,E,hCoord,hCompat,hActive,hCut⟩ := hLocal p hp hu
  have hpQ := hp
  rw [hQ] at hpQ
  have hpPi := (mem_unaryIndexedMixedFamily_at η P p b hb).mp hpQ.2
  have hOldClose : vfValue (E.coefficient*E.extendedFocus (Fin.tail p.1,p.2 ∘ Fin.natAdd r)) <
      vfValue ((Fin.tail p.1) E.coordinate-x) := by
    rw [hCompat.coordinate,hCoord,← hCut]
    exact hClose
  have hNewPi := E.coordinate_cutoff_stable (Fin.tail p.1,p.2 ∘ Fin.natAdd r) hpPi
    ((hCompat.active_iff hpPi).mpr hActive) x hOldClose
  rw [hCompat.coordinate,hCoord] at hNewPi
  have hLocalRV := D.tagged (Fin.tail p.1,p.2 ∘ Fin.natAdd r) (hCompat.subset hpPi)
    (Function.update (Fin.tail p.1) j x,p.2 ∘ Fin.natAdd r) (hCompat.subset hNewPi) rfl
  have hRV : tupleRV M p.1=tupleRV M (Function.update p.1 j.succ x) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change rv M (p.1 0)=rv M (Function.update p.1 j.succ x 0)
      rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    · have hk := congrFun hLocalRV k
      change rv M ((Fin.tail p.1) k)=rv M (Function.update (Fin.tail p.1) j x k) at hk
      exact hk.trans (congrArg (rv M) (congrFun (unaryIndexedTail_update p j x) k).symm)
  have hNewW : (Function.update p.1 j.succ x,p.2) ∈ W.carrier :=
    rvPullback_mem_of_sameRV hW hpQ.1 hRV rfl
  rw [hQ]
  refine ⟨hNewW,(mem_unaryIndexedMixedFamily_at η P _ b ((unaryIndexedBasePoint_update p j x).trans hb)).mpr ?_⟩
  rw [unaryIndexedTail_update]
  exact hNewPi

end DiamondIntegral.Section6
