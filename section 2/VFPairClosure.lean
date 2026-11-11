import «section 2».CorrespondenceSets
import Mathlib.Topology.Homeomorph.Defs

/-! Same-base closure for a unary VF base times a VF tuple. This bridges
the actual product topology to the released raw VF closure formulas. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def vfPairValues (p : (Fin 1 → VF M) × (Fin n → VF M)) : Fin 1 ⊕ Fin n → M :=
  Sum.elim (vfValues p.1) (vfValues p.2)

noncomputable def vfPairHomeomorph (n : ℕ) :
    ((Fin 1 → VF M) × (Fin n → VF M)) ≃ₜ (Fin (n+1) → VF M) where
  toFun p := Fin.cons (p.1 0) p.2
  invFun x := ((fun _ => x 0),Fin.tail x)
  left_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · rfl
  right_inv x := by
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  continuous_toFun := by
    apply continuous_pi
    intro i
    change Continuous (fun p : (Fin 1 → VF M) × (Fin n → VF M) =>
      Fin.cons (α := fun _ : Fin (n+1) => VF M) (p.1 0) p.2 i)
    refine Fin.cases (motive := fun j => Continuous
      (fun p : (Fin 1 → VF M) × (Fin n → VF M) =>
        Fin.cons (α := fun _ : Fin (n+1) => VF M) (p.1 0) p.2 j)) ?_ (fun j => ?_) i
    · exact (continuous_apply (0 : Fin 1)).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_pi (fun _ => continuous_apply 0)).prodMk
      (continuous_pi (fun j => continuous_apply j.succ))

theorem vf_closure_definable {S : Set M}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) :
    S.Definable LRV (vfValues '' closure A) := by
  have he : {x : Fin n → VF M | vfValues x ∈ vfValues '' A} = A := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      exact vfValues_injective he ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  have h := vfRawClosure_definable hA
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (mem_vfRawClosure_iff hv (vfValues '' A) x).mpr (he.symm ▸ hx)
  · intro hz
    let x : Fin n → VF M := fun i => ⟨z i,hz.1 i⟩
    have hx := (mem_vfRawClosure_iff hv (vfValues '' A) x).mp hz
    exact ⟨x,he ▸ hx,rfl⟩

theorem vfPair_join_definable {S : Set M}
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hA : S.Definable LRV (vfPairValues '' A)) :
    S.Definable LRV (vfValues '' (vfPairHomeomorph n '' A)) := by
  let π : Fin 1 ⊕ Fin n → Fin (n+1) := Sum.elim (fun _ => 0) Fin.succ
  have h := hA.preimage_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
    refine ⟨p,hp,?_⟩
    funext i
    cases i with
    | inl i => fin_cases i; rfl
    | inr i => rfl
  · rintro ⟨p,hp,he⟩
    refine ⟨vfPairHomeomorph n p,⟨p,hp,rfl⟩,?_⟩
    funext i
    refine Fin.cases (congrFun he (.inl 0)) (fun j => congrFun he (.inr j)) i

theorem vfPair_definable_of_joined {S : Set M}
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hA : S.Definable LRV (vfValues '' (vfPairHomeomorph n '' A))) :
    S.Definable LRV (vfPairValues '' A) := by
  let π : Fin (n+1) → Fin 1 ⊕ Fin n := Fin.cases (.inl 0) Sum.inr
  have h := hA.preimage_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨vfPairHomeomorph n p,⟨p,hp,rfl⟩,?_⟩
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  · rintro ⟨_,⟨p,hp,rfl⟩,he⟩
    refine ⟨p,hp,?_⟩
    funext i
    cases i with
    | inl i => fin_cases i; exact congrFun he 0
    | inr i => exact congrFun he i.succ

theorem vfPair_closure_definable {S : Set M}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (hA : S.Definable LRV (vfPairValues '' A)) :
    S.Definable LRV (vfPairValues '' closure A) := by
  have h := vf_closure_definable hv (vfPairHomeomorph n '' A) (vfPair_join_definable A hA)
  rw [← (vfPairHomeomorph n).image_closure A] at h
  exact vfPair_definable_of_joined (closure A) h

end DiamondIntegral.Section2
