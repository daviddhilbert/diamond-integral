import «section 6».FiniteRVIsomorphisms

/-! Replace an arbitrary finite set of structural volume coordinates
on a finite original-label domain. Every intermediate volume is an actual
definable map, has finite fibres, and retains nonzero coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvPartialReplacement (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n)) :
    RVObject (M := M) S n where
  arity := U.arity
  domain := U.domain
  volume := rvTupleAssembleMap U.domain n (fun j =>
    (rvTupleSelectMap S (fun _ : Fin 1 => j)).comp (if j ∈ I then Δ else U.volume))

theorem rvPartialReplacement_value (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n))
    (u : U.domain) (j : Fin n) :
    (rvPartialReplacement U Δ I).value u j = if j ∈ I then (Δ u).val j else U.value u j := by
  change (rvTupleAssembleMap U.domain n _ u).val j = _
  rw [rvTupleAssembleMap_value]
  by_cases hj : j ∈ I
  · simp only [if_pos hj]
    rfl
  · simp only [if_neg hj]
    rfl

theorem rvPartialReplacement_nonzero (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n))
    (hU : ∀ u j, (U.value u j).val ≠ iRVZero) (hΔ : ∀ u j, ((Δ u).val j).val ≠ iRVZero)
    (u : U.domain) (j : Fin n) : ((rvPartialReplacement U Δ I).value u j).val ≠ iRVZero := by
  rw [rvPartialReplacement_value]
  split_ifs
  · exact hΔ u j
  · exact hU u j

theorem rvPartialReplacement_finiteVolume (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n))
    (hFin : U.domain.carrier.Finite) : (rvPartialReplacement U Δ I).volume.FiniteFibres :=
  Map.finiteFibres_of_finite _ hFin

def rvPartialReplacementStep (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n)) (i : Fin n)
    (hFin : U.domain.carrier.Finite) (hU : ∀ u j, (U.value u j).val ≠ iRVZero)
    (hΔ : ∀ u j, ((Δ u).val j).val ≠ iRVZero) :
    rvPartialReplacement U Δ I ≅ rvPartialReplacement U Δ (insert i I) :=
  rvIsoOfFiniteNonzeroDomains (Map.id U.domain) Function.bijective_id hFin hFin
    (rvPartialReplacement_nonzero U Δ I hU hΔ) (rvPartialReplacement_nonzero U Δ (insert i I) hU hΔ)

theorem rvPartialReplacementStep_unary (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n)) (i : Fin n)
    (hFin : U.domain.carrier.Finite) (hU : ∀ u j, (U.value u j).val ≠ iRVZero)
    (hΔ : ∀ u j, ((Δ u).val j).val ≠ iRVZero) :
    RVUnaryRelativeAt (rvPartialReplacementStep U Δ I i hFin hU hΔ).hom.map i := by
  intro u j hj
  change (rvPartialReplacement U Δ (insert i I)).value u j = (rvPartialReplacement U Δ I).value u j
  rw [rvPartialReplacement_value,rvPartialReplacement_value]
  simp only [Finset.mem_insert,hj,false_or]

theorem exists_finite_rv_replacement_chain (U : RVObject (M := M) S n)
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) (I : Finset (Fin n))
    (hFin : U.domain.carrier.Finite) (hU : ∀ u j, (U.value u j).val ≠ iRVZero)
    (hΔ : ∀ u j, ((Δ u).val j).val ≠ iRVZero) :
    ∃ T : RVUnaryChain S n (rvPartialReplacement U Δ ∅) (rvPartialReplacement U Δ I),
      (∀ u, T.iso.hom.map u = u) ∧ T.finiteVolume := by
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨.identity _,fun _ => rfl,rvPartialReplacement_finiteVolume U Δ ∅ hFin⟩
  | @insert i I hi ih =>
    obtain ⟨T,hT,hTF⟩ := ih
    let H : RVUnaryChain S n (rvPartialReplacement U Δ I) (rvPartialReplacement U Δ (insert i I)) :=
      .step i (rvPartialReplacementStep U Δ I i hFin hU hΔ)
        (rvPartialReplacementStep_unary U Δ I i hFin hU hΔ) (.identity _)
    refine ⟨T.comp H,fun u => ?_,T.comp_finiteVolume H hTF ?_⟩
    · rw [RVUnaryChain.comp_map,hT]
      rfl
    · exact ⟨rvPartialReplacement_finiteVolume U Δ I hFin,
        rvPartialReplacement_finiteVolume U Δ (insert i I) hFin⟩

end DiamondIntegral.Section6
