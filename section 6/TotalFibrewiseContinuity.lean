import «section 6».RVFunctionFamilyGraphs
import «section 2».FibrewiseContinuity

/-! A canonical finite exceptional set in the first VF coordinate of a
total definable function whose remaining-coordinate fibers are continuous.
The exception is the actual projection of the discontinuity locus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem total_vfPairMapGraph_definable
    (f : (Fin (n+1) → VF M) → Fin 1 → VF M) (hf : S.Definable LRV (vfGraph f)) :
    S.Definable LRV (vfPairMapGraph Set.univ (fun p => f (vfPairHomeomorph n p))) := by
  let idx : Fin (n+1) ⊕ Fin 1 → (Fin 1 ⊕ Fin n) ⊕ Fin 1 :=
    Sum.elim (Fin.cases (.inl (.inl 0)) (fun i => .inl (.inr i))) Sum.inr
  have h := hf.preimage_comp idx
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,_,he⟩
    refine ⟨vfPairHomeomorph n p,?_⟩
    funext j
    cases j with
    | inl j =>
      refine Fin.cases ?_ (fun i => ?_) j
      · exact congrFun he (.inl (.inl 0))
      · exact congrFun he (.inl (.inr i))
    | inr j => exact congrFun he (.inr j)
  · rintro ⟨x,hx⟩
    let p := (vfPairHomeomorph (M := M) n).symm x
    refine ⟨p,Set.mem_univ _,?_⟩
    funext j
    cases j with
    | inl j =>
      cases j with
      | inl j => fin_cases j; exact congrFun hx (.inl 0)
      | inr j => exact congrFun hx (.inl j.succ)
    | inr j =>
      simpa only [p,Homeomorph.apply_symm_apply,Function.comp_apply,idx,Sum.elim_inr]
        using congrFun hx (.inr j)

def firstCoordinateDiscontinuities (f : (Fin (n+1) → VF M) → Fin 1 → VF M) :
    Set (Fin 1 → VF M) := {a | ∃ x, x 0 = a 0 ∧ ¬ ContinuousAt f x}

theorem firstCoordinateDiscontinuities_finite
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin (n+1) → VF M) → Fin 1 → VF M) (hf : S.Definable LRV (vfGraph f))
    (hFibres : ∀ a : VF M, Continuous (fun b : Fin n → VF M => f (Fin.cons a b))) :
    (firstCoordinateDiscontinuities f).Finite := by
  let e := vfPairHomeomorph (M := M) n
  let F := fun p : (Fin 1 → VF M) × (Fin n → VF M) => f (e p)
  obtain ⟨E,hEsub,hEF,hEdef,hCont⟩ := proposition_2_55 h00 hc hκ hs hv Set.univ (vf_univ_definable S)
    Set.univ (fun _ _ => ⟨Set.mem_univ _,Set.mem_univ _⟩) F (total_vfPairMapGraph_definable f hf)
    (fun a _ => (hFibres (a 0)).continuousOn)
  apply hEF.subset
  rintro a ⟨x,hxa,hbad⟩
  by_contra haE
  let p := e.symm x
  have hpa : p.1 = a := by
    funext i
    fin_cases i
    exact hxa
  have hpE : p.1 ∉ E := by rw [hpa]; exact haE
  have hOpen : IsOpen {q : (Fin 1 → VF M) × (Fin n → VF M) | q.1 ∉ E} :=
    hEF.isClosed.isOpen_compl.preimage continuous_fst
  have hNhds : {q : (Fin 1 → VF M) × (Fin n → VF M) | q ∈ Set.univ ∧ q.1 ∉ E} ∈ 𝓝 p := by
    simpa only [Set.mem_univ,true_and] using hOpen.mem_nhds hpE
  have hJoint : ContinuousAt F p := hCont.continuousAt hNhds
  have hComp : ContinuousAt (F ∘ e.symm) x :=
    ContinuousAt.comp (f := e.symm) (x := x) hJoint e.symm.continuous.continuousAt
  apply hbad
  convert hComp using 1
  funext y
  exact congrArg f (e.apply_symm_apply y).symm

end DiamondIntegral.Section6
