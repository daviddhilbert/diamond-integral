import «section 2».UnaryLimits
import «section 2».SingletonLimitTopology
import «section 2».ScalarExtensions
import «section 2».ScalarTranslations

/-! The scalar form of the bounded singleton-limit step in 2.51. The
centre is replaced by its limit to obtain an actual continuous VF germ. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open scoped Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unaryScalarGraph_tuple_limit_graph (S : Set M) (f : VF M → VF M)
    (hf : S.Definable LRV (unaryScalarGraph f)) :
    S.Definable LRV (unaryLimitGraph Set.univ (fun x : Fin 1 → VF M => {fun _ : Fin 1 => f (x 0)})) := by
  let idx : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0,.inr 0]
  convert hf.preimage_comp idx using 1
  ext z
  constructor
  · rintro ⟨x,hx,y,hy,he⟩
    have hy' : y = (fun _ : Fin 1 => f (x 0)) := hy
    subst y
    exact ⟨x 0,congrFun he (.inl 0),congrFun he (.inr 0)⟩
  · rintro ⟨x,hx0,hx1⟩
    change x.val = z (.inl 0) at hx0
    change (f x).val = z (.inr 0) at hx1
    refine ⟨(fun _ => x),Set.mem_univ _,(fun _ => f x),Set.mem_singleton _,?_⟩
    funext j
    cases j with
    | inl j => fin_cases j; exact hx0
    | inr j => fin_cases j; exact hx1

theorem exists_scalar_continuous_limit
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VF M → VF M) (hf : S.Definable LRV (unaryScalarGraph f))
    (hbounded : ∃ γ : Gamma M, ∀ x : VF M, γ.val ≤ vfValue (f x)) :
    ∃ b : VF M, ContinuousAt (Function.update f 0 b) 0 ∧ S.Definable₁ LRV {b.val} := by
  let F (x : Fin 1 → VF M) : Fin 1 → VF M := fun _ => f (x 0)
  have hG := unaryScalarGraph_tuple_limit_graph S f hf
  have hbound : BoundedVFRange Set.univ (fun x => {F x}) := by
    obtain ⟨γ,hγ⟩ := hbounded
    refine ⟨γ,?_⟩
    intro x hx y hy j
    have he : y = F x := hy
    subst y
    exact hγ (x 0)
  have hacc : ∀ δ : Gamma M, ∃ x ∈ (Set.univ : Set (Fin 1 → VF M)) \ {0}, x ∈ vfBall 0 δ := by
    intro δ
    obtain ⟨x,hx,hx0⟩ := exists_ne_mem_vfBall (0 : Fin 1 → VF M) δ (by decide)
    exact ⟨x,⟨Set.mem_univ _,hx0⟩,hx⟩
  obtain ⟨b,hL,hb⟩ := exists_singleton_affine_limit hc hs hsmall Set.univ F hG hbound hacc
  have hcont := hL.1.continuousAt_update hv (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : Fin 1 → VF M))
  let ι (x : VF M) : Fin 1 → VF M := fun _ => x
  have hι : Continuous ι := continuous_pi (fun _ => continuous_id)
  have hι0 : ι (0 : VF M) = (0 : Fin 1 → VF M) := funext (fun _ => rfl)
  have hcomp := hcont.comp_of_eq (hι.continuousAt (x := (0 : VF M))) hι0
  have ht : ContinuousAt (fun x : VF M => Function.update F 0 b (ι x) 0) 0 :=
    (continuous_apply 0).continuousAt.comp hcomp
  have he : (fun x : VF M => Function.update F 0 b (ι x) 0) = Function.update f 0 (b 0) := by
    funext x
    by_cases hx : x = 0
    · subst x
      change Function.update F 0 b (0 : Fin 1 → VF M) 0 = Function.update f 0 (b 0) 0
      simp only [Function.update_self]
    · have hi : ι x ≠ (0 : Fin 1 → VF M) := fun h => hx (congrFun h 0)
      simp only [Function.update_of_ne hx,Function.update_of_ne hi]
      rfl
  refine ⟨b 0,?_,?_⟩
  · simpa only [he] using ht
  · change S.Definable LRV {z : Fin 1 → M | z 0 = (b 0).val}
    convert hb using 1
    ext z
    constructor
    · intro hz
      refine ⟨b,Set.mem_singleton _,?_⟩
      funext j
      fin_cases j
      exact hz.symm
    · rintro ⟨w,hw,he⟩
      have hw' : w = b := hw
      subst w
      exact (congrFun he 0).symm

theorem exists_scalar_continuous_limit_at
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VF M → VF M) (hf : S.Definable LRV (unaryScalarGraph f))
    (hbounded : ∃ γ : Gamma M, ∀ x : VF M, γ.val ≤ vfValue (f x))
    (a : VF M) (ha : a.val ∈ S) :
    ∃ b : VF M, ContinuousAt (Function.update f a b) a ∧ S.Definable₁ LRV {b.val} := by
  let g (x : VF M) := f (a+x)
  have hg := unaryScalarGraph_input_shift_definable S f hf a ha
  have hgb : ∃ γ : Gamma M, ∀ x : VF M, γ.val ≤ vfValue (g x) := by
    obtain ⟨γ,hγ⟩ := hbounded
    exact ⟨γ,fun x => hγ (a+x)⟩
  obtain ⟨b,hcont,hb⟩ := exists_scalar_continuous_limit hc hs hsmall hv g hg hgb
  have ht := hcont.comp_of_eq
    ((continuous_id.sub continuous_const).continuousAt : ContinuousAt (fun x : VF M => x-a) a)
    (sub_self a)
  have he : (fun x : VF M => Function.update g 0 b (x-a)) = Function.update f a b := by
    funext x
    by_cases hx : x = a
    · subst x
      simp only [sub_self,Function.update_self]
    · have hxa : x-a ≠ 0 := sub_ne_zero.mpr hx
      simp only [Function.update_of_ne hx,Function.update_of_ne hxa]
      have hax : a+(x-a) = x := by abel
      exact congrArg f hax
  refine ⟨b,?_,hb⟩
  change ContinuousAt (fun x : VF M => Function.update g 0 b (x-a)) a at ht
  rwa [he] at ht

end DiamondIntegral.Section2
