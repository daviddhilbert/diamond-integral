import «section 2».RawDiscShapes

/-! The uniform good-polydisc predicate in Corollary 2.30. Quantifying over
all RV tags avoids enumerating their finite set. Tags absent from every row
have empty image; tags present in one row must be present in every row. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n : ℕ}

def rawTaggedPolydiscImage (F : Set ((Fin n → M) × M))
    (w : Fin (n+n) ⊕ Fin 1 → M) : Set M :=
  {y | ∃ x ∈ rawOpenPolydisc (w ∘ Sum.inl), (x,y) ∈ F ∧ iRv y = w (.inr 0)}

def rawPolydiscTagRow (F : Set ((Fin n → M) × M))
    (w : Fin (n+n) ⊕ Fin 1 → M) : Set (Fin n → M) :=
  {x | ∃ y, (x,y) ∈ F ∧ iRv y = w (.inr 0)}

def rawGoodTaggedPolydiscCodes (F : Set ((Fin n → M) × M)) : Set (Fin (n+n) → M) :=
  {d | (∀ t : Fin 1 → M,
      (rawTaggedPolydiscImage F (Sum.elim d t)).Nonempty →
        rawOpenPolydisc d ⊆ rawPolydiscTagRow F (Sum.elim d t)) ∧
    ∀ t : Fin 1 → M, Sum.elim d t ∈ rawDiscShapeCodes (rawTaggedPolydiscImage F)}

theorem raw_rv_eq_definable (S : Set M) {α : Type} (i j : α) :
    S.Definable LRV {z : α → M | iRv (z i) = z j} := by
  have hrv : S.DefinableFun LRV (fun z : α → M => iRv (z i)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : α → M => ![z i]) from by
        intro k
        fin_cases k
        exact Set.DefinableFun.proj LRV)
  exact hrv.ofPred_eq (Set.DefinableFun.proj LRV)

theorem rawPolydiscTagRow_definable (S : Set M) (F : Set ((Fin n → M) × M))
    (hF : S.Definable LRV {z : Fin (n+1) → M | (Fin.init z,z (Fin.last n)) ∈ F}) :
    S.Definable LRV {z : (Fin (n+n) ⊕ Fin 1) ⊕ Fin n → M |
      z ∘ Sum.inr ∈ rawPolydiscTagRow F (z ∘ Sum.inl)} := by
  let Z := ((Fin (n+n) ⊕ Fin 1) ⊕ Fin n) ⊕ Fin 1
  let idx : Fin (n+1) → Z := Fin.lastCases (.inr 0) (fun i => .inl (.inr i))
  have h := (hF.preimage_comp idx).inter
    (raw_rv_eq_definable S (.inr 0 : Z) (.inl (.inl (.inr 0))))
  convert h.exists_of_finite using 1
  ext z
  have hinit (y : Fin 1 → M) : Fin.init (Sum.elim z y ∘ idx) = z ∘ Sum.inr := by
    funext i
    change Sum.elim z y (idx i.castSucc) = z (.inr i)
    simp only [idx,Fin.lastCases_castSucc,Sum.elim_inl]
  change (∃ y : M, _) ↔ (∃ y : Fin 1 → M, _)
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨fun _ => y,?_⟩
    change (Fin.init (Sum.elim z (fun _ => y) ∘ idx),(Sum.elim z (fun _ => y) ∘ idx) (Fin.last n)) ∈ F ∧
      iRv y = z (.inl (.inr 0))
    rw [hinit]
    simpa only [idx,Function.comp_apply,Fin.lastCases_last,Sum.elim_inr] using hy
  · rintro ⟨y,hy⟩
    refine ⟨y 0,?_⟩
    change (Fin.init (Sum.elim z y ∘ idx),(Sum.elim z y ∘ idx) (Fin.last n)) ∈ F ∧
      iRv (y 0) = z (.inl (.inr 0)) at hy
    rw [hinit] at hy
    simpa only [idx,Function.comp_apply,Fin.lastCases_last,Sum.elim_inr] using hy

theorem rawTaggedPolydiscImage_definable [hM : M ⊨ Axioms.ACVF]
    (S : Set M) (F : Set ((Fin n → M) × M))
    (hF : S.Definable LRV {z : Fin (n+1) → M | (Fin.init z,z (Fin.last n)) ∈ F}) :
    S.Definable LRV {z : (Fin (n+n) ⊕ Fin 1) ⊕ Fin 1 → M |
      z (.inr 0) ∈ rawTaggedPolydiscImage F (z ∘ Sum.inl)} := by
  let Z := ((Fin (n+n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin n
  let idx : Fin (n+1) → Z := Fin.lastCases (.inl (.inr 0)) Sum.inr
  let ridx : Fin (n+n) ⊕ Fin n → Z :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  have h := ((rawOpenPolydisc_membership_definable S n).preimage_comp ridx).inter
    ((hF.preimage_comp idx).inter
      (raw_rv_eq_definable S (.inl (.inr 0) : Z) (.inl (.inl (.inr 0)))))
  convert h.exists_of_finite using 1
  ext z
  change (∃ x ∈ rawOpenPolydisc ((z ∘ Sum.inl) ∘ Sum.inl),
    (x,z (.inr 0)) ∈ F ∧ iRv (z (.inr 0)) = z (.inl (.inr 0))) ↔ (∃ x, _)
  apply exists_congr
  intro x
  have hinit : Fin.init (Sum.elim z x ∘ idx) = x := by
    funext i
    change Sum.elim z x (idx i.castSucc) = x i
    simp only [idx,Fin.lastCases_castSucc,Sum.elim_inr]
  change (x ∈ rawOpenPolydisc ((z ∘ Sum.inl) ∘ Sum.inl) ∧
    (x,z (.inr 0)) ∈ F ∧ iRv (z (.inr 0)) = z (.inl (.inr 0))) ↔
    (x ∈ rawOpenPolydisc ((z ∘ Sum.inl) ∘ Sum.inl) ∧
    (Fin.init (Sum.elim z x ∘ idx),(Sum.elim z x ∘ idx) (Fin.last n)) ∈ F ∧
      iRv (z (.inr 0)) = z (.inl (.inr 0)))
  rw [hinit]
  simp only [idx,Function.comp_apply,Fin.lastCases_last,Sum.elim_inl]

theorem rawGoodTaggedPolydiscCodes_definable [hM : M ⊨ Axioms.ACVF]
    (S : Set M) (F : Set ((Fin n → M) × M))
    (hF : S.Definable LRV {z : Fin (n+1) → M | (Fin.init z,z (Fin.last n)) ∈ F}) :
    S.Definable LRV (rawGoodTaggedPolydiscCodes F) := by
  let K := Fin (n+n) ⊕ Fin 1
  let ridx : Fin (n+n) ⊕ Fin n → K ⊕ Fin n :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hR := (rawOpenPolydisc_membership_definable S n).preimage_comp ridx
  have hrow := rawPolydiscTagRow_definable S F hF
  have hsub := (hR.himp hrow).forall_of_finite
  have hI := rawTaggedPolydiscImage_definable S F hF
  have htag := hI.exists_of_finite
  have hcommon := (htag.himp hsub).forall_of_finite
  have hshape := (rawDiscShapeCodes_definable S (rawTaggedPolydiscImage F) hI).forall_of_finite
  convert hcommon.inter hshape using 1
  ext d
  simp only [rawGoodTaggedPolydiscCodes,Set.mem_ofPred_eq,Set.mem_inter_iff,
    Set.mem_himp_iff,Set.mem_preimage,ridx,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
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

theorem rawGoodTaggedPolydiscCodes_rows (F : Set ((Fin n → M) × M))
    (d : Fin (n+n) → M) (hd : d ∈ rawGoodTaggedPolydiscCodes F) :
    ∀ x ∈ rawOpenPolydisc d, ∀ z ∈ rawOpenPolydisc d,
      iRv '' {y | (x,y) ∈ F} = iRv '' {y | (z,y) ∈ F} := by
  have hstep (x z : Fin n → M) (hx : x ∈ rawOpenPolydisc d)
      (hz : z ∈ rawOpenPolydisc d) (t : M) :
      t ∈ iRv '' {y | (x,y) ∈ F} → t ∈ iRv '' {y | (z,y) ∈ F} := by
    rintro ⟨y,hy,hyt⟩
    have hne : (rawTaggedPolydiscImage F (Sum.elim d (fun _ : Fin 1 => t))).Nonempty :=
      ⟨y,x,hx,hy,hyt⟩
    exact hd.1 (fun _ => t) hne hz
  intro x hx z hz
  ext t
  exact ⟨hstep x z hx hz t,hstep z x hz hx t⟩

end DiamondIntegral.Section2
