import «section 6».ReindexedCentripetalMaps
import «section 6».RVLabelRefinementGeometry

/-! Regularization and a VF-coordinate change commute after selecting
the corresponding new leading-term tags. This is an exact fibre identity
and does not insert an arbitrary RV reordering as a special operation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def regularizedVFPermutationLabels (e : Fin n ≃ Fin n) : Fin (n+r) → Fin (n+r) :=
  Fin.addCases (fun i => Fin.castAdd r (e.symm i)) (Fin.natAdd n)

theorem regularizedVFPermutationLabels_old (e : Fin n ≃ Fin n) (v : Fin (n+r) → RVInfinity M) :
    (v ∘ regularizedVFPermutationLabels e) ∘ Fin.natAdd n=v ∘ Fin.natAdd n := by
  funext i
  simp only [regularizedVFPermutationLabels,Function.comp_apply,Fin.addCases_right]

theorem regularizedVFPermutationLabels_new (e : Fin n ≃ Fin n) (v : Fin (n+r) → RVInfinity M) :
    (v ∘ regularizedVFPermutationLabels e) ∘ Fin.castAdd r=(v ∘ Fin.castAdd r) ∘ e.symm := by
  funext i
  simp only [regularizedVFPermutationLabels,Function.comp_apply,Fin.addCases_left]

theorem reindexed_regularization_fibres
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (v : Fin (n+r) → RVInfinity M) :
    vfFibre (regularizeMap (reindexedVFSet A e)).image.carrier v=
      vfFibre (reindexedVFSet (regularizeMap A).image e).carrier (v ∘ regularizedVFPermutationLabels e) := by
  rw [regularization_carrier]
  ext a
  rw [regularized_fibre]
  change ((a,v ∘ Fin.natAdd n) ∈ (reindexedVFSet A e).carrier ∧ tupleRV M a=v ∘ Fin.castAdd r) ↔
    (a,v ∘ regularizedVFPermutationLabels e) ∈ (reindexedVFSet (regularizeMap A).image e).carrier
  rw [mem_reindexedVFSet (regularizeMap A).image e (a,v ∘ regularizedVFPermutationLabels e),regularization_carrier]
  change (_ ∧ _) ↔ (a ∘ e.symm) ∈ vfFibre (regularize '' A.carrier) (v ∘ regularizedVFPermutationLabels e)
  rw [regularized_fibre,regularizedVFPermutationLabels_old,regularizedVFPermutationLabels_new]
  apply and_congr (mem_reindexedVFSet A e (a,v ∘ Fin.natAdd n))
  constructor
  · intro h
    funext i
    have hi := congrFun h (e.symm i)
    exact hi
  · intro h
    funext i
    have hi := congrFun h (e i)
    change rv M (a (e.symm (e i)))=v (Fin.castAdd r (e.symm (e i))) at hi
    change rv M (a i)=v (Fin.castAdd r i)
    simpa only [Equiv.symm_apply_apply] using hi

end DiamondIntegral.Section6
