import IntegrationSection5.MixedUnaryPreparations
import IntegrationSection5.VFPermutation
import IntegrationSection5.SharedRVProductComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}

theorem mixed_projection_swap (D : Set (Point (M := M) 2 m)) (i : Fin 2) :
    mixedUnaryProjectionSet {p | vfPermutation (Equiv.swap 0 1) p ∈ D} i =
      mixedUnaryProjectionSet D ((Equiv.swap 0 1) i) := by
  have hInv (p : Point (M := M) 2 m) : vfPermutation (Equiv.swap 0 1) (vfPermutation (Equiv.swap 0 1) p) = p := by
    simpa only [Equiv.symm_swap] using vfPermutation_inverse (Equiv.swap (0 : Fin 2) 1) p
  have hProj (p : Point (M := M) 2 m) (j : Fin 2) :
      activeUnaryProjection j id (vfPermutation (Equiv.swap 0 1) p) = activeUnaryProjection ((Equiv.swap 0 1) j) id p := rfl
  ext q
  constructor
  · rintro ⟨p,hp,hpq⟩
    refine ⟨vfPermutation (Equiv.swap 0 1) p,hp,?_⟩
    rw [hProj,Equiv.swap_apply_self]
    exact hpq
  · rintro ⟨p,hp,hpq⟩
    refine ⟨vfPermutation (Equiv.swap 0 1) p,?_,?_⟩
    · change vfPermutation (Equiv.swap 0 1) (vfPermutation (Equiv.swap 0 1) p) ∈ D
      rwa [hInv]
    · exact (hProj p i).trans hpq

namespace MixedUnaryPreparations
variable {D : Set (Point (M := M) 2 m)}
def swap (P : MixedUnaryPreparations (G := G) D) :
    MixedUnaryPreparations (G := G) {p | vfPermutation (Equiv.swap 0 1) p ∈ D} where
  codes := P.codes
  real_contains := P.real_contains
  source := vfPermutationImage P.source (Equiv.swap 0 1)
  source_eq := by
    ext p
    rw [vfPermutationImage_mem_mixed,P.source_eq,Equiv.symm_swap]
    rfl
  sourceD := P.sourceE
  sourceE := P.sourceD
  sourceD_eq := P.sourceE_eq.trans (by simpa only [Equiv.swap_apply_left] using (mixed_projection_swap D 0).symm)
  sourceE_eq := P.sourceD_eq.trans (by simpa only [Equiv.swap_apply_right] using (mixed_projection_swap D 1).symm)
  arityD := P.arityE
  arityE := P.arityD
  targetD := P.targetE
  targetE := P.targetD
  specialD := P.specialE
  specialE := P.specialD
  gammaD := P.gammaE
  gammaE := P.gammaD
  pullbackD := P.pullbackE
  pullbackE := P.pullbackD
end MixedUnaryPreparations
end IntegrationInACVF.Section5
