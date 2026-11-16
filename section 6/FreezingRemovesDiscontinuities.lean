import «section 6».RVFocusContinuity
import «section 6».FreezingFocusContinuity

/-! FMT actually removes the finite first-coordinate continuity
exceptions. On each clopen frozen disc the first coordinate is constant;
off their finite union the original jointly continuous function remains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem familyFreeze_removes_discontinuities
    {ι Y : Type*} [Finite ι] [TopologicalSpace Y]
    (D : ι → Set (VF M)) (c : ι → VF M)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (hD : ∀ i, IsClopen (D i))
    (f : (Fin (n+1) → VF M) → Y)
    (hFibres : ∀ a : VF M, Continuous (fun b : Fin n → VF M => f (Fin.cons a b)))
    (hOutside : ∀ x, (∀ i, x 0 ∉ D i) → ContinuousAt f x) :
    Continuous (fun x : Fin (n+1) → VF M => f (Fin.cons (familyFreeze D c (x 0)) (Fin.tail x))) := by
  have htail : Continuous (Fin.tail : (Fin (n+1) → VF M) → Fin n → VF M) :=
    continuous_pi (fun i => continuous_apply i.succ)
  have hfirst : Continuous (fun y : Fin (n+1) → VF M => y 0) := continuous_apply 0
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : ∃ i, x 0 ∈ D i
  · obtain ⟨i,hi⟩ := hx
    have hn : {y : Fin (n+1) → VF M | y 0 ∈ D i} ∈ 𝓝 x :=
      ((hD i).isOpen.preimage hfirst).mem_nhds hi
    apply ((hFibres (c i)).comp htail).continuousAt.congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    rw [familyFreeze_inside D c hsep i (y 0) hy]
    rfl
  · have hxn : ∀ i, x 0 ∉ D i := not_exists.mp hx
    have hopen : IsOpen {a : VF M | ∀ i, a ∉ D i} := by
      convert (isOpen_iInter_of_finite (fun i => (hD i).isClosed.isOpen_compl)) using 1
      ext a
      simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_compl_iff]
    have hopen' : IsOpen {y : Fin (n+1) → VF M | ∀ i, y 0 ∉ D i} :=
      hopen.preimage hfirst
    have hn : {y : Fin (n+1) → VF M | ∀ i, y 0 ∉ D i} ∈ 𝓝 x := hopen'.mem_nhds hxn
    apply (hOutside x hxn).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    rw [familyFreeze_outside D c (y 0) hy,Fin.cons_self_tail]

theorem vfFamilyFreeze_removes_discontinuities
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) (c : A → VF M)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (f : (Fin (n+1) → VF M) → Fin 1 → VF M)
    (hFibres : ∀ a : VF M, Continuous (fun b : Fin n → VF M => f (Fin.cons a b)))
    (E : Set (Fin 1 → VF M)) (hEF : E.Finite)
    (hCover : ∀ a ∈ E, ∃ D : A, a 0 ∈ vfOpenBall D.val)
    (hCont : ContinuousOn f {x | (fun _ : Fin 1 => x 0) ∉ E}) :
    Continuous (fun x : Fin (n+1) → VF M =>
      f (Fin.cons (vfFamilyFreeze A c (x 0)) (Fin.tail x))) := by
  letI : Finite A := hA.to_subtype
  have hfirst : Continuous (fun y : Fin (n+1) → VF M => fun _ : Fin 1 => y 0) :=
    continuous_pi (fun _ => continuous_apply 0)
  have hOutside : ∀ x : Fin (n+1) → VF M,
      (∀ D : A, x 0 ∉ vfOpenBall D.val) → ContinuousAt f x := by
    intro x hx
    have hxE : (fun _ : Fin 1 => x 0) ∉ E := by
      intro he
      obtain ⟨D,hD⟩ := hCover (fun _ : Fin 1 => x 0) he
      exact hx D hD
    have hopen : IsOpen {y : Fin (n+1) → VF M | (fun _ : Fin 1 => y 0) ∉ E} :=
      hEF.isClosed.isOpen_compl.preimage hfirst
    exact hCont.continuousAt (hopen.mem_nhds hxE)
  have h := familyFreeze_removes_discontinuities
    (fun D : A => vfOpenBall D.val) c
    (fun D E x hx hE => hsep D E x.val hx hE)
    (fun D => vfOpenBall_clopen hv D.val) f hFibres hOutside
  convert h using 1
  funext x
  rw [vfFamilyFreeze_eq A c hsep]
  rfl

end DiamondIntegral.Section6.FMT
