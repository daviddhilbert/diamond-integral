import «section 6».CoordinateFibreTemplates
import «section 6».DoublyBoundedPullbackInvariance

/-! Complete RV-data constancy turns prepared coordinate fibres into
a joint RV-pullback. Equality concerns their entire leading-term sets
at every retained old-label tuple, not chosen representatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def coordinateFibreRVData (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (a : VF M) (u : Fin r → RVInfinity M) : Set (Fin n → RVInfinity M) :=
  tupleRV M '' vfFibre ((headFibreTemplate A).fibre (fun _ => a.val)).carrier u

theorem joint_rvPullback_of_coordinate_data
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hFibres : ∀ a : VF M,IsRVPullback ((headFibreTemplate A).fibre (fun _ => a.val)).carrier)
    (hData : ∀ a b : VF M,rv M a=rv M b → ∀ u,coordinateFibreRVData A a u=coordinateFibreRVData A b u) :
    IsRVPullback A.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  have hpSlice : (Fin.tail p.1,p.2) ∈ ((headFibreTemplate A).fibre (fun _ => (p.1 0).val)).carrier := by
    apply (mem_headFibreTemplate_iff A (p.1 0) _).mpr
    have he : Fin.cons (p.1 0) (Fin.tail p.1)=p.1 := funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    simpa only [he,Prod.mk.eta] using hp
  have hHead : rv M (p.1 0)=rv M (q.1 0) := congrFun hVF 0
  have hRow : tupleRV M (Fin.tail p.1) ∈ coordinateFibreRVData A (q.1 0) p.2 := by
    rw [← hData (p.1 0) (q.1 0) hHead p.2]
    exact ⟨Fin.tail p.1,hpSlice,rfl⟩
  obtain ⟨x,hx,hxRV⟩ := hRow
  have hqSlice : (Fin.tail q.1,q.2) ∈ ((headFibreTemplate A).fibre (fun _ => (q.1 0).val)).carrier :=
    rvPullback_mem_of_sameRV (hFibres (q.1 0)) hx
      (hxRV.trans (funext (fun i => congrFun hVF i.succ))) hRV
  have h := (mem_headFibreTemplate_iff A (q.1 0) _).mp hqSlice
  have he : Fin.cons (q.1 0) (Fin.tail q.1)=q.1 := funext (fun i => Fin.cases rfl (fun _ => rfl) i)
  simpa only [he,Prod.mk.eta] using h

end DiamondIntegral.Section6
