import «section 6».FiniteMeasuredCoordinateReplacement

/-! The actual measured relatively unary factorization for finite label
objects in every positive degree. Every intermediate Gamma form is
constructed and its balance equation is proved pointwise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem lemma_6_29_measured_finite_labels (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) {U V : MeasuredRVObject (M := M) S n}
    (e : MeasuredRVIso U V) (hFin : U.object.domain.carrier.Finite) :
    ∃ T : MeasuredRVUnaryChain S n U V, T.iso.iso.hom.map = e.iso.hom.map := by
  let Δ := V.object.volume.comp e.iso.hom.map
  let P₀ := measuredPartialReplacement hc e ∅ hFin
  let P₁ := measuredPartialReplacement hc e Finset.univ hFin
  have hf : Function.Bijective e.iso.hom.map := by
    constructor
    · intro u v he
      have h := congrArg e.iso.inv.map he
      rwa [rvIso_inv_apply,rvIso_inv_apply] at h
    · intro v
      exact ⟨e.iso.inv.map v,rvIso_apply_inv e.iso v⟩
  let a : U.object ≅ P₀.object := rvIsoOfVolumePreservingBijection
    (Map.id U.object.domain) Function.bijective_id (fun u => by
      funext j
      change (rvPartialReplacement U.object Δ ∅).value u j = U.object.value u j
      rw [rvPartialReplacement_value]
      simp only [Finset.notMem_empty,if_false])
  let b : P₁.object ≅ V.object := rvIsoOfVolumePreservingBijection e.iso.hom.map hf (fun u => by
    funext j
    change V.object.value (e.iso.hom.map u) j = (rvPartialReplacement U.object Δ Finset.univ).value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.mem_univ,if_true]
    rfl)
  let a₀ : MeasuredRVIso U P₀ := ⟨a,fun u => (measuredPartialReplacement_totalWeight hc e ∅ hFin u).symm⟩
  let b₀ : MeasuredRVIso P₁ V := ⟨b,fun u =>
    (measuredPartialReplacement_totalWeight hc e Finset.univ hFin u).trans (e.balance u)⟩
  let i : Fin n := ⟨0,hn⟩
  have ha : RVUnaryRelativeAt a₀.iso.hom.map i := by
    intro u j hj
    change (rvPartialReplacement U.object Δ ∅).value u j = U.object.value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.notMem_empty,if_false]
  have hb : RVUnaryRelativeAt b₀.iso.hom.map i := by
    intro u j hj
    change V.object.value (e.iso.hom.map u) j = (rvPartialReplacement U.object Δ Finset.univ).value u j
    rw [rvPartialReplacement_value]
    simp only [Finset.mem_univ,if_true]
    rfl
  obtain ⟨T,hT⟩ := exists_finite_measured_replacement_chain hc e Finset.univ hFin
  let H : MeasuredRVUnaryChain S n P₁ V := .step i b₀ hb (.identity V)
  let K : MeasuredRVUnaryChain S n U P₁ := .step i a₀ ha T
  refine ⟨K.comp H,?_⟩
  apply Map.ext
  intro u
  rw [MeasuredRVUnaryChain.comp_map]
  change e.iso.hom.map (T.iso.iso.hom.map u) = e.iso.hom.map u
  rw [hT]

end DiamondIntegral.Section6
