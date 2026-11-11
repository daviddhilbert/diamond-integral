import «section 2».CorrespondenceSets
import Section8.VFDefinableTopology

/-! Uniform same-base definability of closure in each VF fibre. The base
coordinates stay as free variables throughout the raw neighbourhood formula. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n : ℕ}

def vfRawFibreClosure (D : Set (Fin k → M)) (R : Set (Fin k ⊕ Fin n → M)) :
    Set (Fin k ⊕ Fin n → M) :=
  {z | z ∘ Sum.inl ∈ D ∧ z ∘ Sum.inr ∈ vfRawClosure {x | Sum.elim (z ∘ Sum.inl) x ∈ R}}

theorem vfRawFibreClosure_definable {S : Set M}
    (D : Set (Fin k → M)) (hD : S.Definable LRV D)
    (R : Set (Fin k ⊕ Fin n → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (vfRawFibreClosure D R) := by
  let Z := Fin k ⊕ Fin n
  let W := Z ⊕ Fin 1
  let X := W ⊕ Fin n
  let row : Fin k ⊕ Fin n → X := Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  let box : (Fin n ⊕ Fin n) ⊕ Fin 1 → X :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) Sum.inr) (Sum.inl ∘ Sum.inr)
  have hHit := ((hR.preimage_comp row).inter
    ((uniformBallRelation_definable S n).preimage_comp box)).exists_of_finite
  have hsort := ((definableAt_sort S .vf).raw_definable).preimage_comp (Sum.inr : Fin 1 → W)
  have hzero : S.DefinableFun LRV (fun _ : W → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hne := ((Set.DefinableFun.proj LRV (i := (Sum.inr 0 : W))).ofPred_eq hzero).compl
  have hBad := (hsort.inter (hne.inter hHit.compl)).exists_of_finite
  have h := (hD.preimage_comp Sum.inl).inter
    (((vfRawUniverse_definable S n).preimage_comp Sum.inr).inter hBad.compl)
  convert h using 1
  ext z
  have hrow (t : Fin 1 → M) (x : Fin n → M) :
      Sum.elim (Sum.elim z t) x ∘ row = Sum.elim (z ∘ Sum.inl) x := by
    funext j
    cases j <;> rfl
  have hbox (t : Fin 1 → M) (x : Fin n → M) :
      Sum.elim (Sum.elim z t) x ∘ box = Sum.elim (Sum.elim (z ∘ Sum.inr) x) t := by
    funext j
    cases j with
    | inl j => cases j <;> rfl
    | inr j => rfl
  constructor
  · intro hz
    refine ⟨hz.1,hz.2.1,?_⟩
    rintro ⟨t,ht,ht0,hno⟩
    obtain ⟨x,hx,hxb⟩ := hz.2.2 (t 0) ht ht0
    apply hno
    refine ⟨x,?_,?_⟩
    · change Sum.elim (Sum.elim z t) x ∘ row ∈ R
      rw [hrow]
      exact hx
    · change Sum.elim (Sum.elim z t) x ∘ box ∈ uniformBallRelation n
      rw [hbox]
      exact hxb
  · rintro ⟨hz,hs,hno⟩
    refine ⟨hz,hs,fun r hr hr0 => ?_⟩
    by_contra hn
    apply hno
    refine ⟨![r],hr,hr0,?_⟩
    rintro ⟨x,hx,hxb⟩
    apply hn
    change Sum.elim (Sum.elim z ![r]) x ∘ row ∈ R at hx
    change Sum.elim (Sum.elim z ![r]) x ∘ box ∈ uniformBallRelation n at hxb
    rw [hrow] at hx
    rw [hbox] at hxb
    exact ⟨x,hx,hxb⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfRawFibreClosure_at
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : Set (Fin k → VF M)) (F : (Fin k → VF M) → Set (Fin n → VF M))
    (a : Fin k → VF M) (b : Fin n → VF M) :
    Sum.elim (vfValues a) (vfValues b) ∈ vfRawFibreClosure (vfValues '' D) (vfCorrespondenceGraph D F) ↔
      a ∈ D ∧ b ∈ closure (F a) := by
  have hdom : vfValues a ∈ vfValues '' D ↔ a ∈ D := by
    constructor
    · rintro ⟨c,hc,he⟩
      exact vfValues_injective he ▸ hc
    · exact fun ha => ⟨a,ha,rfl⟩
  change (vfValues a ∈ vfValues '' D ∧ vfValues b ∈
    vfRawClosure {x | Sum.elim (vfValues a) x ∈ vfCorrespondenceGraph D F}) ↔ _
  rw [hdom]
  apply and_congr_right
  intro ha
  rw [mem_vfRawClosure_iff hv]
  have he : {x : Fin n → VF M | vfValues x ∈
      {z | Sum.elim (vfValues a) z ∈ vfCorrespondenceGraph D F}} = F a := by
    ext x
    change Sum.elim (vfValues a) (vfValues x) ∈ vfCorrespondenceGraph D F ↔ x ∈ F a
    rw [vfCorrespondenceGraph_at,and_iff_right ha]
  rw [he]

theorem vf_fibreClosure_graph_definable {S : Set M}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : Set (Fin k → VF M)) (hD : S.Definable LRV (vfValues '' D))
    (F : (Fin k → VF M) → Set (Fin n → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph D F)) :
    S.Definable LRV (vfCorrespondenceGraph D (fun a => closure (F a))) := by
  have h := vfRawFibreClosure_definable (vfValues '' D) hD (vfCorrespondenceGraph D F) hF
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact (vfRawFibreClosure_at hv D F a b).mpr ⟨ha,hb⟩
  · intro hz
    obtain ⟨a,ha,he⟩ := hz.1
    let b : Fin n → VF M := fun i => ⟨z (.inr i),hz.2.1 i⟩
    have hez : Sum.elim (vfValues a) (vfValues b) = z := by
      funext i
      cases i with
      | inl i => exact congrFun he i
      | inr i => rfl
    have hmem := (vfRawFibreClosure_at hv D F a b).mp (by rw [hez]; exact hz)
    exact ⟨a,ha,b,hmem.2,hez⟩

end DiamondIntegral.Section2
