import «section 5».NativeFiniteRVRowObjects
import «section 5».RESBijectionPromotion
import IntegrationSection6.GammaFiniteTupleBounds

/-! Actual native RV label maps have full original-base append graphs
and a uniform finite reverse-fibre bound, without adding label parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

def nativeRVLabelGraph (U : GammaGroundRVObject hc B k) : Set (Fin (U.arity+k) → M) :=
  {w | ∃ u : U.domain, w = Fin.append (rvValues u.val) (rvValues (U.volume u).val)}

theorem nativeRVLabelGraph_definable (U : GammaGroundRVObject hc B k) :
    DefinableOverBase B (Fin.append (fun _ : Fin U.arity => .rv) (fun _ : Fin k => .rv)) (nativeRVLabelGraph U) := by
  let π : Fin (k+U.arity) → Fin (U.arity+k) := join k U.arity (Fin.castAdd k) (Fin.natAdd U.arity)
  have hπ (x : Fin U.arity → M) (y : Fin k → M) : Fin.append x y ∘ π = join k U.arity x y := by
    rw [comp_join]
    simp only [Function.comp_def,Fin.append_left,Fin.append_right]
  have h := (Section3RVCodeBridge.joinedGraph_definable U.volume).preimage_real
    (Fin.append (fun _ : Fin U.arity => .rv) (fun _ : Fin k => .rv)) π
  convert h using 1
  ext w
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨⟨u,hπ _ _⟩,?_⟩
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,sortEval,iRV,rvValues] using (u.val i).property
    · simpa only [Fin.append_right,sortEval,iRV,rvValues] using ((U.volume u).val i).property
  · rintro ⟨⟨u,hu⟩,_⟩
    refine ⟨u,?_⟩
    have hx (i : Fin U.arity) : w (Fin.castAdd k i) = rvValues u.val i := by
      have hh := congrFun hu (headIndex k U.arity i)
      simpa only [Function.comp_apply,π,join_head] using hh
    have hy (i : Fin k) : w (Fin.natAdd U.arity i) = rvValues (U.volume u).val i := by
      have hh := congrFun hu (tailIndex k U.arity i)
      simpa only [Function.comp_apply,π,join_tail] using hh
    funext j
    exact Fin.addCases (fun i => (hx i).trans (Fin.append_left _ _ i).symm)
      (fun i => (hy i).trans (Fin.append_right _ _ i).symm) j

theorem nativeRVLabelGraph_append_iff (U : GammaGroundRVObject hc B k)
    (x : Fin U.arity → M) (y : Fin k → M) :
    Fin.append x y ∈ nativeRVLabelGraph U ↔
      ∃ u : U.domain, rvValues u.val = x ∧ rvValues (U.volume u).val = y := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,funext (fun i => ?_),funext (fun i => ?_)⟩
    · have hi := congrFun hu (Fin.castAdd k i)
      simpa only [Fin.append_left] using hi.symm
    · have hi := congrFun hu (Fin.natAdd U.arity i)
      simpa only [Fin.append_right] using hi.symm
  · rintro ⟨u,hx,hy⟩
    exact ⟨u,(congrArg₂ Fin.append hx hy).symm⟩

theorem nativeRVLabelGraph_fibre_finite (U : GammaGroundRVObject hc B k) (y : Fin k → M) :
    {x | Fin.append x y ∈ nativeRVLabelGraph U}.Finite := by
  apply (rawMap_finite U.volume U.finite y).subset
  intro x hx
  obtain ⟨u,hux,huy⟩ := (nativeRVLabelGraph_append_iff U x y).mp hx
  refine ⟨⟨u.val,u.property,hux⟩,?_⟩
  rw [←hux,rawMap_apply]
  exact huy

theorem nativeRVLabelGraph_reverse_definable (U : GammaGroundRVObject hc B k) :
    DefinableOverBase B (Fin.append (fun _ : Fin k => .rv) (fun _ : Fin U.arity => .rv))
      {w | Fin.append (w ∘ Fin.natAdd k) (w ∘ Fin.castAdd U.arity) ∈ nativeRVLabelGraph U} := by
  let σ : Fin (U.arity+k) → Fin (k+U.arity) := Fin.addCases (Fin.natAdd k) (Fin.castAdd U.arity)
  have hσ (w : Fin (k+U.arity) → M) : w ∘ σ = Fin.append (w ∘ Fin.natAdd k) (w ∘ Fin.castAdd U.arity) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [σ,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
  have h := (nativeRVLabelGraph_definable U).preimage_real
    (Fin.append (fun _ : Fin k => .rv) (fun _ : Fin U.arity => .rv)) σ
  convert h using 1
  ext w
  change (Fin.append (w ∘ Fin.natAdd k) (w ∘ Fin.castAdd U.arity) ∈ nativeRVLabelGraph U) ↔
    (w ∘ σ ∈ nativeRVLabelGraph U ∧ w ∈ sortedUniverse
      (Fin.append (fun _ : Fin k => .rv) (fun _ : Fin U.arity => .rv)))
  rw [hσ]
  constructor
  · intro hw
    refine ⟨hw,?_⟩
    have hp := (nativeRVLabelGraph_definable U).proper _ hw
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,Fin.append_right,Function.comp_apply] using hp (Fin.natAdd U.arity i)
    · simpa only [Fin.append_left,Fin.append_right,Function.comp_apply] using hp (Fin.castAdd k i)
  · exact And.left

theorem nativeRVLabelGraph_uniform_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (U : GammaGroundRVObject hc B k) :
    ∃ N : ℕ, ∀ y : Fin k → M, (∀ j, sortEval SortTag.rv (y j)) →
      {x | Fin.append x y ∈ nativeRVLabelGraph U}.Finite ∧
      {x | Fin.append x y ∈ nativeRVLabelGraph U}.ncard ≤ N := by
  let A : Set (Fin k → M) := sortedUniverse (fun _ : Fin k => .rv)
  have hA : DefinableOverBase B (fun _ : Fin k => .rv) A :=
    real_definableOverBase B _ _ (sortedUniverse_definable B.real _)
  let R : Set ((Fin k → M) × (Fin U.arity → M)) := {q | Fin.append q.2 q.1 ∈ nativeRVLabelGraph U}
  exact gamma_uniform_finite_tuple_rows hκ hs hr hγ _ _ A hA R
    (nativeRVLabelGraph_reverse_definable U) (fun y _ => nativeRVLabelGraph_fibre_finite U y)

end DiamondIntegral.Section5
