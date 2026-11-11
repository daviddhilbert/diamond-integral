import «section 2».RawTaggedPolydiscs

/-! The good-polydisc condition is first-order uniformly in every finite
parameter tuple, before any DC presentation is specialized. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n : ℕ} {α : Type} [Finite α]

def parametricTaggedImage (F : (α → M) → Set ((Fin n → M) × M))
    (w : (α ⊕ Fin (n+n)) ⊕ Fin 1 → M) : Set M :=
  rawTaggedPolydiscImage (F (w ∘ Sum.inl ∘ Sum.inl))
    (Sum.elim (w ∘ Sum.inl ∘ Sum.inr) (w ∘ Sum.inr))

def parametricTagRow (F : (α → M) → Set ((Fin n → M) × M))
    (w : (α ⊕ Fin (n+n)) ⊕ Fin 1 → M) : Set (Fin n → M) :=
  rawPolydiscTagRow (F (w ∘ Sum.inl ∘ Sum.inl))
    (Sum.elim (w ∘ Sum.inl ∘ Sum.inr) (w ∘ Sum.inr))

theorem parametricTagRow_definable (S : Set M)
    (F : (α → M) → Set ((Fin n → M) × M))
    (hF : S.Definable LRV {z : α ⊕ Fin (n+1) → M |
      (Fin.init (z ∘ Sum.inr),z (.inr (Fin.last n))) ∈ F (z ∘ Sum.inl)}) :
    S.Definable LRV {z : ((α ⊕ Fin (n+n)) ⊕ Fin 1) ⊕ Fin n → M |
      z ∘ Sum.inr ∈ parametricTagRow F (z ∘ Sum.inl)} := by
  let Z := (((α ⊕ Fin (n+n)) ⊕ Fin 1) ⊕ Fin n) ⊕ Fin 1
  let idx : α ⊕ Fin (n+1) → Z :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl)
      (Fin.lastCases (.inr 0) (fun i => .inl (.inr i)))
  have h := (hF.preimage_comp idx).inter
    (raw_rv_eq_definable S (.inr 0 : Z) (.inl (.inl (.inr 0))))
  convert h.exists_of_finite using 1
  ext z
  have hinit (y : Fin 1 → M) : Fin.init ((Sum.elim z y ∘ idx) ∘ Sum.inr) = z ∘ Sum.inr := by
    funext i
    simp only [Fin.init,idx,Function.comp_apply,Sum.elim_inr,Fin.lastCases_castSucc,Sum.elim_inl]
  change (∃ y : M, _) ↔ (∃ y : Fin 1 → M, _)
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨fun _ => y,?_⟩
    change (Fin.init ((Sum.elim z (fun _ => y) ∘ idx) ∘ Sum.inr),
      (Sum.elim z (fun _ => y) ∘ idx) (.inr (Fin.last n))) ∈
      F ((Sum.elim z (fun _ => y) ∘ idx) ∘ Sum.inl) ∧ iRv y = z (.inl (.inr 0))
    rw [hinit]
    simpa only [idx,Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fin.lastCases_last] using hy
  · rintro ⟨y,hy⟩
    refine ⟨y 0,?_⟩
    change (Fin.init ((Sum.elim z y ∘ idx) ∘ Sum.inr),
      (Sum.elim z y ∘ idx) (.inr (Fin.last n))) ∈
      F ((Sum.elim z y ∘ idx) ∘ Sum.inl) ∧ iRv (y 0) = z (.inl (.inr 0)) at hy
    rw [hinit] at hy
    simpa only [idx,Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fin.lastCases_last] using hy

theorem parametricTaggedImage_definable [hM : M ⊨ Axioms.ACVF] (S : Set M)
    (F : (α → M) → Set ((Fin n → M) × M))
    (hF : S.Definable LRV {z : α ⊕ Fin (n+1) → M |
      (Fin.init (z ∘ Sum.inr),z (.inr (Fin.last n))) ∈ F (z ∘ Sum.inl)}) :
    S.Definable LRV {z : ((α ⊕ Fin (n+n)) ⊕ Fin 1) ⊕ Fin 1 → M |
      z (.inr 0) ∈ parametricTaggedImage F (z ∘ Sum.inl)} := by
  let Z := (((α ⊕ Fin (n+n)) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin n
  let idx : α ⊕ Fin (n+1) → Z :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl)
      (Fin.lastCases (.inl (.inr 0)) Sum.inr)
  let ridx : Fin (n+n) ⊕ Fin n → Z :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr) Sum.inr
  have h := ((rawOpenPolydisc_membership_definable S n).preimage_comp ridx).inter
    ((hF.preimage_comp idx).inter
      (raw_rv_eq_definable S (.inl (.inr 0) : Z) (.inl (.inl (.inr 0)))))
  convert h.exists_of_finite using 1
  ext z
  change (∃ x ∈ rawOpenPolydisc (z ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr),
    (x,z (.inr 0)) ∈ F (z ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) ∧
    iRv (z (.inr 0)) = z (.inl (.inr 0))) ↔ (∃ x, _)
  apply exists_congr
  intro x
  have hinit : Fin.init ((Sum.elim z x ∘ idx) ∘ Sum.inr) = x := by
    funext i
    simp only [Fin.init,idx,Function.comp_apply,Sum.elim_inr,Fin.lastCases_castSucc]
  change (_ ∧ _ ∧ _) ↔ (_ ∧
    (Fin.init ((Sum.elim z x ∘ idx) ∘ Sum.inr),(Sum.elim z x ∘ idx) (.inr (Fin.last n))) ∈
      F ((Sum.elim z x ∘ idx) ∘ Sum.inl) ∧ _)
  rw [hinit]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,idx,ridx,Function.comp_def,
    Sum.elim_inl,Sum.elim_inr,Fin.lastCases_last]
  rfl

theorem parametricGoodTaggedPolydiscCodes_definable [hM : M ⊨ Axioms.ACVF]
    (S : Set M) (F : (α → M) → Set ((Fin n → M) × M))
    (hF : S.Definable LRV {z : α ⊕ Fin (n+1) → M |
      (Fin.init (z ∘ Sum.inr),z (.inr (Fin.last n))) ∈ F (z ∘ Sum.inl)}) :
    S.Definable LRV {z : α ⊕ Fin (n+n) → M |
      z ∘ Sum.inr ∈ rawGoodTaggedPolydiscCodes (F (z ∘ Sum.inl))} := by
  let K := (α ⊕ Fin (n+n)) ⊕ Fin 1
  let ridx : Fin (n+n) ⊕ Fin n → K ⊕ Fin n :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) Sum.inr
  have hR := (rawOpenPolydisc_membership_definable S n).preimage_comp ridx
  have hrow := parametricTagRow_definable S F hF
  have hsub := (hR.himp hrow).forall_of_finite
  have hI := parametricTaggedImage_definable S F hF
  have hcommon := (hI.exists_of_finite.himp hsub).forall_of_finite
  have hshape := (rawDiscShapeCodes_definable S (parametricTaggedImage F) hI).forall_of_finite
  convert hcommon.inter hshape using 1
  ext z
  change ((∀ t, (rawTaggedPolydiscImage (F (z ∘ Sum.inl)) (Sum.elim (z ∘ Sum.inr) t)).Nonempty → _) ∧ _) ↔ _
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_himp_iff,Set.mem_preimage,
    parametricTaggedImage,parametricTagRow,Function.comp_def,ridx,Sum.elim_inl,Sum.elim_inr]
  constructor
  · rintro ⟨hcommon,hshape⟩
    refine ⟨?_,hshape⟩
    intro t ht x hx
    obtain ⟨y,hy⟩ := ht
    exact hcommon t ⟨y 0,hy⟩ hx
  · rintro ⟨hcommon,hshape⟩
    refine ⟨?_,hshape⟩
    intro t ht x hx
    obtain ⟨y,hy⟩ := ht
    exact hcommon t ⟨fun _ => y,hy⟩ x hx

end DiamondIntegral.Section2
