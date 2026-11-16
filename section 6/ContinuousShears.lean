import «section 6».NonzeroBranchTags

/-! Triangular shears are local homeomorphisms wherever their focus is
continuous. Transport in the changed coordinate preserves the erased
arguments, so no differentiability or inverse-function theorem is used. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem coordinateShear_erase (j : Fin n) (focus : (Fin n → VF M) → VF M) (a : Fin n → VF M) :
    Function.update (coordinateShear j focus a) j 0 = Function.update a j 0 := by
  classical
  funext i
  by_cases hi : i = j
  · subst i
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hi]
    exact coordinateShear_other j i hi focus a

theorem coordinateShear_neg_inverse (j : Fin n) (focus : (Fin n → VF M) → VF M) :
    Function.LeftInverse (coordinateShear j (fun a => -focus a)) (coordinateShear j focus) := by
  classical
  intro a
  funext i
  by_cases hi : i = j
  · subst i
    simp only [coordinateShear,Function.update_self,Function.update_idem]
    abel
  · rw [coordinateShear_other j i hi,coordinateShear_other j i hi]

theorem coordinateShear_neg_rightInverse (j : Fin n) (focus : (Fin n → VF M) → VF M) :
    Function.RightInverse (coordinateShear j (fun a => -focus a)) (coordinateShear j focus) := by
  intro a
  have h := coordinateShear_neg_inverse j (fun a => -focus a) a
  simpa only [coordinateShear,neg_neg] using h

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousAt_coordinateShear (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (a : Fin n → VF M) (hfocus : ContinuousAt (fun x => focus (Function.update x j 0)) a) :
    ContinuousAt (coordinateShear j focus) a := by
  classical
  apply continuousAt_pi.mpr
  intro i
  by_cases hi : i = j
  · subst i
    have h : ContinuousAt (fun x : Fin n → VF M => x j + focus (Function.update x j 0)) a := by
      convert (continuous_apply j).continuousAt.add hfocus using 1
    simpa only [coordinateShear,Function.update_self] using h
  · have h : ContinuousAt (fun x : Fin n → VF M => x i) a := (continuous_apply i).continuousAt
    simpa only [coordinateShear,Function.update_of_ne hi] using h

theorem continuousAt_erasedFocus_transport (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (a b : Fin n → VF M) (he : Function.update a j 0 = Function.update b j 0)
    (ha : ContinuousAt (fun x => focus (Function.update x j 0)) a) :
    ContinuousAt (fun x => focus (Function.update x j 0)) b := by
  classical
  let d := a j - b j
  let T := coordinateShear j (fun _ => d)
  have hT : ContinuousAt T b := continuousAt_coordinateShear j (fun _ => d) b continuousAt_const
  have hTb : T b = a := by
    funext i
    by_cases hi : i = j
    · subst i
      simp only [T,coordinateShear,Function.update_self,d]
      abel
    · have hei : a i = b i := by
        simpa only [Function.update_of_ne hi] using congrFun he i
      exact (coordinateShear_other j i hi (fun _ => d) b).trans hei.symm
  have ha' : ContinuousAt (fun x => focus (Function.update x j 0)) (T b) := hTb.symm ▸ ha
  have hcomp := ha'.comp hT
  convert hcomp using 1
  funext x
  exact congrArg focus (coordinateShear_erase j (fun _ => d) x).symm

theorem coordinateShear_image_isOpen (j : Fin n) (focus : (Fin n → VF M) → VF M)
    (D : Set (Fin n → VF M)) (hD : IsOpen D)
    (hfocus : ∀ a ∈ D, ContinuousAt (fun x => focus (Function.update x j 0)) a) :
    IsOpen (coordinateShear j focus '' D) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨a,ha,rfl⟩
  have hF := continuousAt_erasedFocus_transport j focus a (coordinateShear j focus a)
    (coordinateShear_erase j focus a).symm (hfocus a ha)
  have hInv : ContinuousAt (coordinateShear j (fun x => -focus x)) (coordinateShear j focus a) :=
    continuousAt_coordinateShear j (fun x => -focus x) _ hF.neg
  have hN : coordinateShear j (fun x => -focus x) ⁻¹' D ∈ 𝓝 (coordinateShear j focus a) :=
    hInv.preimage_mem_nhds ((coordinateShear_neg_inverse j focus a).symm ▸ hD.mem_nhds ha)
  exact Filter.mem_of_superset hN (fun x hx =>
    ⟨coordinateShear j (fun a => -focus a) x,hx,coordinateShear_neg_rightInverse j focus x⟩)

end DiamondIntegral.Section6
