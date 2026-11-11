import «section 2».FibreChartGraphs
import «section 2».UniformFibreClosure
import «section 2».ProjectiveFibreGraphs

/-! The two affine closure families in Proposition 2.55 are preimages
of the same intrinsic projective fibre closure. Their uniform formulas
retain the original real base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2

theorem ProjectiveLine.reciprocalChart_eq_finite_iff {K : Type*} [Field K] (y x : K) :
    reciprocalChart y = finite x ↔ y ≠ 0 ∧ y⁻¹ = x := by
  classical
  constructor
  · intro h
    have hy : y ≠ 0 := by
      intro he
      have hp := congrArg ProjectiveLine.point h
      simp [reciprocalChart,he,infinity,finite] at hp
    exact ⟨hy,finite_injective (by simpa only [reciprocalChart,ite_eq_right hy] using h)⟩
  · rintro ⟨hy,hx⟩
    simp only [reciprocalChart,ite_eq_right hy,hx]

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem finiteProjectiveTuple_injective :
    Function.Injective (finiteProjectiveTuple (M := M) (n := n)) := by
  intro x y he
  exact funext (fun i => ProjectiveLine.finite_injective (congrFun he i))

def projectiveFibreGraph (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M) (a : Fin 1 → VF M) :
    Set ((Fin n → VF M) × (Fin 1 → ProjectiveLine (VF M))) :=
  {p | (a,p.1) ∈ A ∧ p.2 = finiteProjectiveTuple (f (a,p.1))}

noncomputable def projectiveFibreChart (atInfinity : Bool) (z : Fin (n+1) → VF M) :
    (Fin n → VF M) × (Fin 1 → ProjectiveLine (VF M)) :=
  (Fin.tail z,if atInfinity then projectiveTupleChart (fun _ : Fin 1 => (none : LimitPoint M))
    (fun _ : Fin 1 => z 0) else finiteProjectiveTuple (fun _ : Fin 1 => z 0))

theorem projectiveFibreChart_affine_preimage
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M) (a : Fin 1 → VF M) :
    (projectiveFibreChart false) ⁻¹' projectiveFibreGraph A f a = affineFibreGraph A f a := by
  ext z
  change (_ ∧ finiteProjectiveTuple (fun _ : Fin 1 => z 0) = finiteProjectiveTuple (f (a,Fin.tail z))) ↔
    _ ∧ (fun _ : Fin 1 => z 0) = f (a,Fin.tail z)
  exact and_congr_right (fun _ => finiteProjectiveTuple_injective.eq_iff)

theorem projectiveFibreChart_reciprocal_preimage
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M) (a : Fin 1 → VF M) :
    (projectiveFibreChart true) ⁻¹' projectiveFibreGraph A f a = reciprocalFibreGraph A f a := by
  ext z
  constructor
  · rintro ⟨ha,he⟩
    have hi : ProjectiveLine.reciprocalChart (z 0) = ProjectiveLine.finite (f (a,Fin.tail z) 0) :=
      congrFun he 0
    obtain ⟨hz,hzi⟩ := (ProjectiveLine.reciprocalChart_eq_finite_iff _ _).mp hi
    refine ⟨ha,hz,?_⟩
    funext i
    fin_cases i
    exact hzi
  · rintro ⟨ha,hz,he⟩
    refine ⟨ha,?_⟩
    funext i
    fin_cases i
    exact (ProjectiveLine.reciprocalChart_eq_finite_iff _ _).mpr ⟨hz,congrFun he 0⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem projectiveFibreChart_isOpenEmbedding (atInfinity : Bool) :
    IsOpenEmbedding (projectiveFibreChart (M := M) (n := n) atInfinity) := by
  let e := (vfPairHomeomorph (M := M) n).symm.trans
    (Homeomorph.prodComm (Fin 1 → VF M) (Fin n → VF M))
  cases atInfinity with
  | false =>
    have hf : IsOpenEmbedding (finiteProjectiveTuple (M := M) (n := 1)) :=
      IsOpenEmbedding.piMap (fun _ => ProjectiveLine.isOpenEmbedding_finite)
    exact (IsOpenEmbedding.id.prodMap hf).comp e.isOpenEmbedding
  | true =>
    exact (IsOpenEmbedding.id.prodMap
      (projectiveTupleChart_isOpenEmbedding (fun _ : Fin 1 => (none : LimitPoint M)))).comp e.isOpenEmbedding

theorem projectiveFibreChart_join (atInfinity : Bool) (y : Fin 1 → VF M) (x : Fin n → VF M) :
    projectiveFibreChart atInfinity (vfPairHomeomorph n (y,x)) =
      (x,if atInfinity then projectiveTupleChart (fun _ : Fin 1 => (none : LimitPoint M)) y
        else finiteProjectiveTuple y) := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i
    cases atInfinity <;> rfl

theorem projectiveFibreChart_preimage_closure
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M) (a : Fin 1 → VF M)
    (atInfinity : Bool) :
    (projectiveFibreChart atInfinity) ⁻¹' closure (projectiveFibreGraph A f a) =
      closure (if atInfinity then reciprocalFibreGraph A f a else affineFibreGraph A f a) := by
  have h := projectiveFibreChart_isOpenEmbedding (M := M) (n := n) atInfinity
  rw [h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous]
  cases atInfinity with
  | false => rw [projectiveFibreChart_affine_preimage]; rfl
  | true => rw [projectiveFibreChart_reciprocal_preimage]; rfl

theorem projectiveFibreChart_closure_graph_definable {S : Set M}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f)) (atInfinity : Bool) :
    S.Definable LRV (vfCorrespondenceGraph I
      (fun a => (projectiveFibreChart atInfinity) ⁻¹' closure (projectiveFibreGraph A f a))) := by
  have he : (fun a => (projectiveFibreChart atInfinity) ⁻¹' closure (projectiveFibreGraph A f a)) =
      (fun a => closure (if atInfinity then reciprocalFibreGraph A f a else affineFibreGraph A f a)) :=
    funext (fun a => projectiveFibreChart_preimage_closure A f a atInfinity)
  rw [he]
  cases atInfinity with
  | false =>
    exact vf_fibreClosure_graph_definable hv I hI (affineFibreGraph A f)
      (affineFibreGraph_definable I A hAI f hf)
  | true =>
    exact vf_fibreClosure_graph_definable hv I hI (reciprocalFibreGraph A f)
      (reciprocalFibreGraph_definable I A hAI f hf)

end DiamondIntegral.Section2
