import «section 6».RVVolumeChanges
import «section 6».PiecewiseMapReplacement

/-! Extend an actual coordinate change on one definable label piece by
the old volume elsewhere. Each extended step is still relatively unary,
has finite volume, and retains double bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvGlobalVolumeChange (U : RVObject (M := M) S n)
    {D : DefSet (rawRVSpace (M := M) U.arity) S}
    (θ : Map D (DefSet.univ (rawRVSpace (M := M) n) S)) : RVObject (M := M) S n :=
  RVObject.withVolume U (replaceMapOn θ U.volume)

theorem rvGlobalVolumeChange_nonzero (U : RVObject (M := M) S n)
    {D : DefSet (rawRVSpace (M := M) U.arity) S}
    (θ : Map D (DefSet.univ (rawRVSpace (M := M) n) S))
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (hθ : ∀ u k, ((θ u).val k).val ≠ iRVZero) (u : U.domain) (k : Fin n) :
    ((rvGlobalVolumeChange U θ).value u k).val ≠ iRVZero := by
  change (((replaceMapOn θ U.volume) u).val k).val ≠ iRVZero
  by_cases hu : u.val ∈ D.carrier
  · rw [replaceMapOn_of_mem θ U.volume u hu]
    exact hθ _ k
  · rw [replaceMapOn_of_not_mem θ U.volume u hu]
    exact hU u k

def rvGlobalVolumeChangeIso (U : RVObject (M := M) S n)
    {D : DefSet (rawRVSpace (M := M) U.arity) S}
    (θ : Map D (DefSet.univ (rawRVSpace (M := M) n) S))
    (hUF : U.volume.FiniteFibres) (hθF : θ.FiniteFibres)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (hθ : ∀ u k, ((θ u).val k).val ≠ iRVZero) : U ≅ rvGlobalVolumeChange U θ :=
  rvIsoOfFiniteVolumeNonzero (Map.id U.domain) Function.bijective_id hUF
    (replaceMapOn_finiteFibres θ U.volume hθF hUF) hU (rvGlobalVolumeChange_nonzero U θ hU hθ)

theorem rvGlobalVolumeChangeIso_unary (U : RVObject (M := M) S n)
    {D : DefSet (rawRVSpace (M := M) U.arity) S} (hD : D.carrier ⊆ U.domain.carrier)
    (θ : Map D (DefSet.univ (rawRVSpace (M := M) n) S))
    (hUF : U.volume.FiniteFibres) (hθF : θ.FiniteFibres)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (hθ : ∀ u k, ((θ u).val k).val ≠ iRVZero) (i : Fin n)
    (hUnary : ∀ (u : D) k, k ≠ i → (θ u).val k = U.value ⟨u.val,hD u.property⟩ k) :
    RVUnaryRelativeAt (rvGlobalVolumeChangeIso U θ hUF hθF hU hθ).hom.map i := by
  intro u k hk
  change ((replaceMapOn θ U.volume u).val k) = U.value u k
  by_cases hu : u.val ∈ D.carrier
  · rw [replaceMapOn_of_mem θ U.volume u hu]
    exact hUnary ⟨u.val,hu⟩ k hk
  · rw [replaceMapOn_of_not_mem θ U.volume u hu]
    rfl

theorem rvGlobalVolumeChange_doublyBounded (U : RVObject (M := M) S n)
    {D : DefSet (rawRVSpace (M := M) U.arity) S}
    (θ : Map D (DefSet.univ (rawRVSpace (M := M) n) S))
    (hU : RVObjectDoublyBounded U) (hθ : RVValueDoublyBounded (Set.range (fun u : D => (θ u).val))) :
    RVObjectDoublyBounded (rvGlobalVolumeChange U θ) := by
  refine ⟨hU.1,?_⟩
  obtain ⟨γ,hγ⟩ := hU.2
  obtain ⟨δ,hδ⟩ := hθ
  let ε := max γ δ
  have hγlo : (ε⁻¹).val ≤ (γ⁻¹).val := show ε⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have hδlo : (ε⁻¹).val ≤ (δ⁻¹).val := show ε⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  refine ⟨ε,?_⟩
  rintro t ⟨u,rfl⟩ k
  change (ε⁻¹).val ≤ Values.vrv ((replaceMapOn θ U.volume u).val k) ∧
    Values.vrv ((replaceMapOn θ U.volume u).val k) ≤ ε.val
  by_cases hu : u.val ∈ D.carrier
  · rw [replaceMapOn_of_mem θ U.volume u hu]
    have h := hδ (θ ⟨u.val,hu⟩).val ⟨⟨u.val,hu⟩,rfl⟩ k
    exact ⟨hδlo.trans h.1,h.2.trans (show δ.val ≤ ε.val from le_max_right _ _)⟩
  · rw [replaceMapOn_of_not_mem θ U.volume u hu]
    have h := hγ (U.value u) ⟨u,rfl⟩ k
    exact ⟨hγlo.trans h.1,h.2.trans (show γ.val ≤ ε.val from le_max_left _ _)⟩

end DiamondIntegral.Section6
