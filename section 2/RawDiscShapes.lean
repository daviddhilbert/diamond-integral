import «section 2».RawOpenPolydiscs
import «section 2».OpenDiscGeometry

/-! A uniform first-order condition saying that a unary fibre is empty,
a point, or an open disc. Improper open presentations represent only the
empty set and are excluded automatically whenever the fibre is nonempty. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {α : Type} [Finite α]

theorem raw_iff_definable {S : Set M} {U V : Set (α → M)}
    (hU : S.Definable LRV U) (hV : S.Definable LRV V) :
    S.Definable LRV {z | z ∈ U ↔ z ∈ V} := by
  convert (hU.inter hV).union (hU.compl.inter hV.compl) using 1
  ext z
  simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
  tauto

def rawPointImageCodes (Q : (α → M) → Set M) : Set (α → M) :=
  {d | ∃ c : Fin 1 → M, ∀ y : Fin 1 → M, y 0 ∈ Q d ↔ y 0 = c 0}

def rawOpenImageCodes (Q : (α → M) → Set M) : Set (α → M) :=
  {d | ∃ q : Fin 2 → M, ∀ y : Fin 1 → M, y 0 ∈ Q d ↔ y 0 ∈ OpenBallCodes.rawBall q}

def rawDiscShapeCodes (Q : (α → M) → Set M) : Set (α → M) :=
  rawPointImageCodes Q ∪ rawOpenImageCodes Q

theorem rawPointImageCodes_definable (S : Set M) (Q : (α → M) → Set M)
    (hQ : S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ Q (z ∘ Sum.inl)}) :
    S.Definable LRV (rawPointImageCodes Q) := by
  let idx : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hR := hQ.preimage_comp idx
  have hE := (Set.DefinableFun.proj LRV (A := S) (i := (Sum.inr 0 : (α ⊕ Fin 1) ⊕ Fin 1))).ofPred_eq
    (Set.DefinableFun.proj LRV (i := (.inl (.inr 0) : (α ⊕ Fin 1) ⊕ Fin 1)))
  convert (raw_iff_definable hR hE).forall_of_finite.exists_of_finite using 1
  ext d
  rfl

theorem rawOpenImageCodes_definable (S : Set M) (Q : (α → M) → Set M)
    (hQ : S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ Q (z ∘ Sum.inl)}) :
    S.Definable LRV (rawOpenImageCodes Q) := by
  let idx : α ⊕ Fin 1 → (α ⊕ Fin 2) ⊕ Fin 1 :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hR := hQ.preimage_comp idx
  let ballidx : Fin 3 → (α ⊕ Fin 2) ⊕ Fin 1 := ![.inl (.inr 0),.inl (.inr 1),.inr 0]
  have hB := (OpenBallCodes.membership_raw_definable S).preimage_comp ballidx
  convert (raw_iff_definable hR hB).forall_of_finite.exists_of_finite using 1
  ext d
  change (∃ q, ∀ y, _) ↔ (∃ q, ∀ y, _)
  apply exists_congr
  intro q
  apply forall_congr'
  intro y
  have he : Fin.init (Sum.elim (Sum.elim d q) y ∘ ballidx) = q := by
    funext i
    fin_cases i <;> rfl
  simp only [Set.mem_ofPred_eq,Set.mem_preimage]
  rw [he]
  rfl

theorem rawDiscShapeCodes_definable (S : Set M) (Q : (α → M) → Set M)
    (hQ : S.Definable LRV {z : α ⊕ Fin 1 → M | z (.inr 0) ∈ Q (z ∘ Sum.inl)}) :
    S.Definable LRV (rawDiscShapeCodes Q) :=
  (rawPointImageCodes_definable S Q hQ).union (rawOpenImageCodes_definable S Q hQ)

variable [hM : M ⊨ Axioms.ACVF]

theorem rawDiscShapeCodes_nonempty (Q : (α → M) → Set M) (d : α → M)
    (hd : d ∈ rawDiscShapeCodes Q) (hne : (Q d).Nonempty) :
    (∃ c : M, Q d = {c}) ∨ IsOpenDisc (Q d) := by
  rcases hd with ⟨c,hc⟩ | ⟨q,hq⟩
  · left
    exact ⟨c 0,Set.ext (fun y => hc (fun _ => y))⟩
  · right
    have he : Q d = OpenBallCodes.rawBall q := Set.ext (fun y => hq (fun _ => y))
    obtain ⟨x,hx⟩ := hne
    have hp : OpenBallCodes.Proper q := (he ▸ hx).1
    obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hG
    let a : VF M := ⟨q 0,hp.1 0⟩
    let r : VF M := ⟨q 1,hp.1 1⟩
    have hr : r ≠ 0 := fun h => hp.2 (congrArg Subtype.val h)
    apply (isOpenDisc_iff_points v hv (Q d)).mpr
    refine ⟨fun y hy => (he ▸ hy).2.1,a,r,hr,?_⟩
    rw [he]
    exact OpenBallCodes.ball_eq_open v hv q hp

theorem rawDiscShapeCodes_of_shape (Q : (α → M) → Set M) (d : α → M)
    (hshape : (Q d).Nonempty → (Q d).Subsingleton ∨ IsOpenDisc (Q d)) :
    d ∈ rawDiscShapeCodes Q := by
  classical
  by_cases hne : (Q d).Nonempty
  · rcases hshape hne with hsmall | hopen
    · obtain ⟨c,hc⟩ := hne
      left
      refine ⟨fun _ => c,?_⟩
      intro y
      exact ⟨fun hy => hsmall hy hc,fun hy => hy ▸ hc⟩
    · obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
      letI := hG
      obtain ⟨hs,a,r,hr,he⟩ := (isOpenDisc_iff_points v hv (Q d)).mp hopen
      let q : Fin 2 → M := ![a.val,r.val]
      have hp : OpenBallCodes.Proper q :=
        ⟨by intro i; fin_cases i; exact a.property; exact r.property,
          fun h => hr (Subtype.ext h)⟩
      have hpoints : {x : VF M | x.val ∈ Q d} = {x : VF M | x.val ∈ OpenBallCodes.rawBall q} :=
        he.trans (OpenBallCodes.ball_eq_open v hv q hp).symm
      have hset : Q d = OpenBallCodes.rawBall q := by
        ext x
        constructor
        · intro hx
          exact (Set.ext_iff.mp hpoints (⟨x,hs hx⟩ : VF M)).mp hx
        · intro hx
          exact (Set.ext_iff.mp hpoints (⟨x,hx.2.1⟩ : VF M)).mpr hx
      right
      exact ⟨q,fun _ => Set.ext_iff.mp hset _⟩
  · right
    refine ⟨![iVFZero,iVFZero],?_⟩
    intro y
    constructor
    · intro hy
      exact (hne ⟨y 0,hy⟩).elim
    · intro hy
      exact (hy.1.2 rfl).elim

end DiamondIntegral.Section2
