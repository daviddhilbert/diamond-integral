import «section 6».FiniteRVCoordinateReplacement
import Section4.RVIsoTools

/-! The finite-label, or RV-dimension-zero, case of 6.29 in every positive
degree. Actual coordinate replacements supply all intermediate RV
objects and prove their finite-volume conditions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem lemma_6_29_finite_labels (hn : 0 < n) {U V : RVObject (M := M) S n}
    (e : U ≅ V) (hFin : U.domain.carrier.Finite)
    (hU : ∀ u j, (U.value u j).val ≠ iRVZero) (hV : ∀ v j, (V.value v j).val ≠ iRVZero) :
    ∃ T : RVUnaryChain S n U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume := by
  let Δ := V.volume.comp e.hom.map
  let P₀ := rvPartialReplacement U Δ ∅
  let P₁ := rvPartialReplacement U Δ Finset.univ
  have hΔ (u : U.domain) (j : Fin n) : ((Δ u).val j).val ≠ iRVZero := hV (e.hom.map u) j
  have hf : Function.Bijective e.hom.map := by
    constructor
    · intro u v he
      have h := congrArg e.inv.map he
      rwa [rvIso_inv_apply,rvIso_inv_apply] at h
    · intro v
      exact ⟨e.inv.map v,rvIso_apply_inv e v⟩
  have hVFin : V.domain.carrier.Finite := by
    letI : Finite U.domain := hFin.to_subtype
    apply (Set.finite_range (fun u : U.domain => (e.hom.map u).val)).subset
    intro v hv
    exact ⟨e.inv.map ⟨v,hv⟩,congrArg Subtype.val (rvIso_apply_inv e ⟨v,hv⟩)⟩
  let a : U ≅ P₀ := rvIsoOfVolumePreservingBijection (Map.id U.domain) Function.bijective_id (fun u => by
    funext j
    change (rvPartialReplacement U Δ ∅).value u j = U.value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.notMem_empty,if_false])
  let b : P₁ ≅ V := rvIsoOfVolumePreservingBijection e.hom.map hf (fun u => by
    funext j
    change V.value (e.hom.map u) j = (rvPartialReplacement U Δ Finset.univ).value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.mem_univ,if_true]
    rfl)
  let i : Fin n := ⟨0,hn⟩
  have ha : RVUnaryRelativeAt a.hom.map i := by
    intro u j hj
    change (rvPartialReplacement U Δ ∅).value u j = U.value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.notMem_empty,if_false]
  have hb : RVUnaryRelativeAt b.hom.map i := by
    intro u j hj
    change V.value (e.hom.map u) j = (rvPartialReplacement U Δ Finset.univ).value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.mem_univ,if_true]
    rfl
  obtain ⟨T,hT,hTF⟩ := exists_finite_rv_replacement_chain U Δ Finset.univ hFin hU hΔ
  let H : RVUnaryChain S n P₁ V := .step i b hb (.identity V)
  let K : RVUnaryChain S n U P₁ := .step i a ha T
  refine ⟨K.comp H,?_,K.comp_finiteVolume H ?_ ?_⟩
  · apply Map.ext
    intro u
    rw [RVUnaryChain.comp_map]
    change e.hom.map (T.iso.hom.map u) = e.hom.map u
    rw [hT]
  · exact ⟨Map.finiteFibres_of_finite U.volume hFin,hTF⟩
  · exact ⟨rvPartialReplacement_finiteVolume U Δ Finset.univ hFin,
      Map.finiteFibres_of_finite V.volume hVFin⟩

end DiamondIntegral.Section6
