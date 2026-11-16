import «section 6».UniformRVInverseObstacles

/-! Any definable label bijection between actual finite-volume objects
with nonzero structural coordinates is an RV isomorphism. Both finite
volume-image conditions follow from the actual finite volume fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvIsoOfFiniteVolumeNonzero {U V : RVObject (M := M) S n}
    (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v i, (V.value v i).val ≠ iRVZero) : U ≅ V where
  hom := {
    map := F
    volumetric u := by simp [rvWeight,hU u,hV (F u)]
    finite_volume_images t := by
      let t' : DefSet.univ (rawRVSpace (M := M) n) S := ⟨t,Set.mem_univ _⟩
      apply ((hUF t').image (fun u : U.domain => V.value (F u))).subset
      rintro s ⟨u,hu,he⟩
      exact ⟨u,Subtype.ext hu,he⟩ }
  inv := {
    map := F.inverse hF
    volumetric v := by simp [rvWeight,hV v,hU (F.inverse hF v)]
    finite_volume_images t := by
      let t' : DefSet.univ (rawRVSpace (M := M) n) S := ⟨t,Set.mem_univ _⟩
      apply ((hVF t').image (fun v : V.domain => U.value (F.inverse hF v))).subset
      rintro s ⟨v,hv,he⟩
      exact ⟨v,Subtype.ext hv,he⟩ }
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro u; exact Map.inverse_apply F hF u
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro v; exact Map.apply_inverse F hF v

end DiamondIntegral.Section6
