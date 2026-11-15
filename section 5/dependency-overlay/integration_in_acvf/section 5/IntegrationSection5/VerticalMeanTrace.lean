import IntegrationSection5.UniformRelativeTrace
import IntegrationSection5.VerticalMeanFocusData

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

namespace UniformRelativeTrace
variable {a b c : ℕ} {X : DefSet (M := M) S n a} {Y Z : DefSet (M := M) S n b}
def castTarget (T : UniformRelativeTrace S n X Y) (h : Y = Z) : UniformRelativeTrace S n X Z := h ▸ T

theorem castTarget_val (T : UniformRelativeTrace S n X Y) (h : Y = Z) (x : X) :
    ((T.castTarget h).toMap x).val = (T.toMap x).val := by subst Z; rfl
end UniformRelativeTrace

def verticalMeanStepTrace (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k) :
    UniformRelativeTrace S (n+1) A (verticalMeanStepTarget R h00 d hd) := by
  let D := verticalMeanFocusData R h00 d hd hTag
  have he : D.image = Map.image (verticalMeanMap R h00 d hd) := by
    apply PresentedSet.eq_of_carrier_eq
    ext p
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,ha⟩
  exact (UniformRelativeTrace.focus D (.canonical 0 (.nil _))).castTarget
    (congrArg (fun B => coordinateCanonicalImage B 0) he)

theorem verticalMeanStepTrace_val (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k) (a : A) :
    ((verticalMeanStepTrace R h00 d hd hTag).toMap a).val = (verticalMeanStepMap R h00 d hd a).val := by
  unfold verticalMeanStepTrace
  rw [UniformRelativeTrace.castTarget_val]
  rfl

/-- The concrete finite centering algorithm retains its uniform focus/canonical trace. -/
theorem verticalRoots_centralize_trace (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S (n+1) m) (R : VerticalRootFamily A),
      HeadSaturated (carrier A) → (∃ k, Tagged (carrier A) 0 k) → R.Bound d →
      ∃ l, ∃ B : DefSet (M := M) S (n+1) l, ∃ f : Map A B,
        SpecialRelativeBoundary f 0 (some false) (some false) ∧
          HeadSaturated (carrier B) ∧ (∃ k, Tagged (carrier B) 0 k) ∧
          (∀ a : A, a.val ∈ carrier R.set → vfAt (f a).val 0 = 0) ∧
          ∃ T : UniformRelativeTrace S (n+1) A B, ∀ a : A, T.toMap a = f a := by
  induction d with
  | zero =>
    intro m A R hA hTag hd
    exact ⟨m,A,Map.id A,specialRelativeBoundary_id A 0 (some false),hA,hTag,
      (fun a ha => R.bound_zero hd a.val ha),.nil A,fun _ => rfl⟩
  | succ d ih =>
    intro m A R hA hTag hd
    obtain ⟨k,hk⟩ := hTag
    let f := verticalMeanStepMap R h00 (d+1) hd
    let Q := verticalMeanStepFamily R h00 (d+1) hd
    have hf := verticalMeanStep_boundary R h00 (d+1) hd hk
    have hSat := verticalMeanStep_headSaturated R h00 (d+1) hd hk hA
    have hTag' : ∃ k, Tagged (carrier (verticalMeanStepTarget R h00 (d+1) hd)) 0 k :=
      ⟨Fin.castAdd _ 0,coordinateCanonical_tagged _ 0⟩
    obtain ⟨l,B,g,hg,hB,hTagB,hz,T,hT⟩ := ih _ Q hSat hTag' (verticalMeanStep_bound R h00 d hd)
    refine ⟨l,B,Map.comp g f,specialRelativeBoundary_comp f g 0 hf hg,hB,hTagB,?_,
      (verticalMeanStepTrace R h00 (d+1) hd hk).append T,?_⟩
    · intro a ha
      exact hz (f a) ((R.mem_imageSet f _).mpr ⟨a,ha,rfl⟩)
    · intro a
      rw [UniformRelativeTrace.append_apply,hT]
      apply congrArg g
      exact Subtype.ext (verticalMeanStepTrace_val R h00 (d+1) hd hk a)

end IntegrationInACVF.Section5
