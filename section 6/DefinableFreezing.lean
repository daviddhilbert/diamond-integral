import «section 6».FiniteFreezing

/-! The simultaneous freezing map has a full real graph over the
original base. Ball codes are quantified, never named as parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rawFamilyFreeze (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M) (x : M) : M :=
  familyFreeze (fun D : A => OpenBallCodes.underlying D.val) (fun D => (c D).val) x

theorem rawFamilyFreeze_definable
    (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (hcdef : S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (c D).val))) :
    S.DefinableFun LRV (fun z : Fin 1 → M => rawFamilyFreeze A c (z 0)) := by
  let J := Option (Fin 1)
  let src (w : J ⊕ Fin 2 → M) : Fin 3 → M := Fin.snoc (w ∘ Sum.inr) (w (.inl (some 0)))
  let dst (w : J ⊕ Fin 2 → M) : Fin 3 → M := Fin.snoc (w ∘ Sum.inr) (w (.inl none))
  have hsrc : S.DefinableMap LRV src := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [src,Fin.snoc_last] using
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl (some 0) : J ⊕ Fin 2)))
    · simpa only [src,Fin.snoc_castSucc,Function.comp_apply] using
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inr j : J ⊕ Fin 2)))
  have hdst : S.DefinableMap LRV dst := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [dst,Fin.snoc_last] using
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl none : J ⊕ Fin 2)))
    · simpa only [dst,Fin.snoc_castSucc,Function.comp_apply] using
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inr j : J ⊕ Fin 2)))
  have hmem := (OpenBallCodes.membership_raw_definable S).preimage_map hsrc
  have hactive := (hmem.inter (hcdef.preimage_map hdst)).exists_of_finite
  have hany := (hmem.inter (hAdef.preimage_comp (Sum.inr : Fin 2 → J ⊕ Fin 2))).exists_of_finite
  have heq : S.Definable LRV {w : J → M | w (some 0) = w none} :=
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (some 0 : J))).ofPred_eq
      (Set.DefinableFun.proj LRV)
  have hActiveEq (w : J → M) :
      w ∈ {w | ∃ q : Fin 2 → M, Sum.elim w q ∈
        (src ⁻¹' {z | z (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init z)}) ∩
        (dst ⁻¹' OpenBallCodes.quotientCenterGraph A (fun D => (c D).val))} ↔
      ∃ D : A, w (some 0) ∈ OpenBallCodes.underlying D.val ∧ (c D).val = w none := by
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_preimage,src,dst,
      Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fin.snoc_last,Fin.init_snoc]
    change (∃ q : Fin 2 → M, w (some 0) ∈ OpenBallCodes.rawBall q ∧
      Fin.snoc q (w none) ∈ OpenBallCodes.quotientCenterGraph A (fun D => (c D).val)) ↔ _
    constructor
    · rintro ⟨q,hx,u,hu,D,hD,hc⟩
      have huq : u.val = q := hu.trans (by funext i; fin_cases i <;> rfl)
      have hball : OpenBallCodes.rawBall q = OpenBallCodes.underlying D.val := by
        rw [← huq]
        exact congrArg OpenBallCodes.underlying hD
      exact ⟨D,hball ▸ hx,hc⟩
    · rintro ⟨D,hx,hc⟩
      obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
      have hball := congrArg OpenBallCodes.underlying hq
      change OpenBallCodes.rawBall q.val = OpenBallCodes.underlying D.val at hball
      have hxq : w (some 0) ∈ OpenBallCodes.rawBall q.val := by rw [hball]; exact hx
      exact ⟨q.val,hxq,q,(by funext i; fin_cases i <;> rfl),D,hq,hc⟩
  have hAnyEq (w : J → M) :
      w ∈ {w | ∃ q : Fin 2 → M, Sum.elim w q ∈
        (src ⁻¹' {z | z (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init z)}) ∩
        ((fun z : J ⊕ Fin 2 → M => z ∘ Sum.inr) ⁻¹' OpenBallCodes.pullback A)} ↔
      ∃ D : A, w (some 0) ∈ OpenBallCodes.underlying D.val := by
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_preimage,src,
      Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fin.snoc_last,Fin.init_snoc]
    change (∃ q : Fin 2 → M, w (some 0) ∈ OpenBallCodes.rawBall q ∧ q ∈ OpenBallCodes.pullback A) ↔ _
    constructor
    · rintro ⟨q,hx,hq,hqA⟩
      exact ⟨⟨Quotient.mk _ (⟨q,hq⟩ : OpenBallCodes.Code M),hqA⟩,hx⟩
    · rintro ⟨D,hx⟩
      obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
      have hball := congrArg OpenBallCodes.underlying hq
      change OpenBallCodes.rawBall q.val = OpenBallCodes.underlying D.val at hball
      have hxq : w (some 0) ∈ OpenBallCodes.rawBall q.val := by rw [hball]; exact hx
      exact ⟨q.val,hxq,q.property,hq.symm ▸ D.property⟩
  change S.Definable LRV (Function.tupleGraph (fun z : Fin 1 → M => rawFamilyFreeze A c (z 0)))
  convert hactive.union (hany.compl.inter heq) using 1
  ext w
  change rawFamilyFreeze A c (w (some 0)) = w none ↔ _
  rw [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,hActiveEq,hAnyEq]
  constructor
  · intro hf
    by_cases hx : ∃ D : A, w (some 0) ∈ OpenBallCodes.underlying D.val
    · obtain ⟨D,hD⟩ := hx
      exact Or.inl ⟨D,hD,(familyFreeze_inside _ _ hsep D _ hD).symm.trans hf⟩
    · refine Or.inr ⟨hx,?_⟩
      exact (familyFreeze_outside _ _ _ (not_exists.mp hx)).symm.trans hf
  · rintro (⟨D,hD,hc⟩ | ⟨hx,he⟩)
    · exact (familyFreeze_inside _ _ hsep D _ hD).trans hc
    · exact (familyFreeze_outside _ _ _ (not_exists.mp hx)).trans he

theorem rawFamilyFreeze_isVF (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (x : M) (hx : iVF x) : iVF (rawFamilyFreeze A c x) := by
  by_cases h : ∃ D : A, x ∈ OpenBallCodes.underlying D.val
  · unfold rawFamilyFreeze familyFreeze
    rw [dite_eq_left h]
    exact (c h.choose).property
  · simpa only [rawFamilyFreeze,familyFreeze,dite_eq_right h] using hx

def vfFamilyFreeze (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M) (x : VF M) : VF M :=
  ⟨rawFamilyFreeze A c x.val,rawFamilyFreeze_isVF A c x.val x.property⟩

theorem vfFamilyFreeze_eq (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E) (x : VF M) :
    vfFamilyFreeze A c x = familyFreeze
      (fun D : A => {y : VF M | y.val ∈ OpenBallCodes.underlying D.val}) c x := by
  let D (B : A) : Set (VF M) := {y | y.val ∈ OpenBallCodes.underlying B.val}
  have hsepVF : ∀ B E : A, ∀ y : VF M, y ∈ D B → y ∈ D E → B = E :=
    fun B E y hy hE => hsep B E y.val hy hE
  apply Subtype.ext
  change rawFamilyFreeze A c x.val = (familyFreeze D c x).val
  by_cases h : ∃ D : A, x.val ∈ OpenBallCodes.underlying D.val
  · obtain ⟨B,hB⟩ := h
    exact (familyFreeze_inside _ (fun B => (c B).val) hsep B x.val hB).trans
      (congrArg Subtype.val (familyFreeze_inside D c hsepVF B x hB)).symm
  · exact (familyFreeze_outside _ (fun B => (c B).val) x.val (not_exists.mp h)).trans
      (congrArg Subtype.val (familyFreeze_outside D c x (not_exists.mp h))).symm

end DiamondIntegral.Section6.FMT
