import «section 2».OpenDiscValue
import «section 2».RawDiscShapes

/-! A first-order equality test for finite disc presentations. The code
contains a VF centre and a nonzero RV code for the actual Gamma radius.
Equality compares the entire underlying discs, allowing every presentation.
This supplies parameter promotion without adding chosen centres to a base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open scoped Classical

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem closedDiscCode_mem_iff_value (a x : VF M) (γ : Gamma M) :
    x.val ∈ BallImaginaries.underlying (closedDiscCode a γ.val) ↔ γ.val ≤ vfValue (x-a) := by
  obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  let r := radiusRepresentative γ.val
  have hr : vfValue r = γ.val := radiusRepresentative_value _
  change x ∈ discPoints (closedDiscCode a γ.val) ↔ _
  rw [← hr,closedDiscCode_points v hv a r]
  change v (x-a) ≤ v r ↔ Values.vrv (rv M r) ≤ Values.vrv (rv M (x-a))
  rw [Values.vrv_le_iff]
  exact (hv (x-a) r).symm

def finiteDiscRawProper (q : Fin (n+n) → M) : Prop :=
  (∀ i, iVF (q (Fin.castAdd n i))) ∧ ∀ i, GammaParameters.NonzeroRV (q (Fin.natAdd n i))

def finiteDiscRawMember (closed : Fin n → Bool) (q : Fin (n+n) → M) (i : Fin n) (x : M) : Prop :=
  finiteDiscRawProper q ∧ iVF x ∧
    if closed i then
      iLe (q (Fin.natAdd n i)) (iRv (iVFAdd x (iVFNeg (q (Fin.castAdd n i)))))
    else ¬ iLe (iRv (iVFAdd x (iVFNeg (q (Fin.castAdd n i))))) (q (Fin.natAdd n i))

noncomputable def finiteDiscRawCentres (q : Fin (n+n) → M) : Fin n → VF M :=
  fun i => if h : iVF (q (Fin.castAdd n i)) then ⟨q (Fin.castAdd n i),h⟩ else 0

noncomputable def finiteDiscRawNames (closed : Fin n → Bool) (q : Fin (n+n) → M) : Fin n → DC (M := M) :=
  finitePolydiscNames closed (finiteDiscRawCentres q) (fun i => GammaParameters.codeValue (q (Fin.natAdd n i)))

theorem finiteDiscRawMember_iff (closed : Fin n → Bool) (q : Fin (n+n) → M)
    (hq : finiteDiscRawProper q) (i : Fin n) (x : M) :
    finiteDiscRawMember closed q i x ↔ x ∈ BallImaginaries.underlying (finiteDiscRawNames closed q i) := by
  classical
  by_cases hx : iVF x
  · let a := finiteDiscRawCentres q i
    let b : VF M := ⟨x,hx⟩
    let γ : Gamma M := GammaParameters.codeValue (q (Fin.natAdd n i))
    have ha : a.val = q (Fin.castAdd n i) := by simp only [a,finiteDiscRawCentres,dite_eq_left (hq.1 i)]
    have hγ : γ.val = Values.vrv (⟨q (Fin.natAdd n i),(hq.2 i).1⟩ : RVInfinity M) := by
      dsimp only [γ]
      rw [GammaParameters.codeValue,dite_eq_left (hq.2 i)]
      rfl
    have hdiff : iRv (iVFAdd x (iVFNeg (q (Fin.castAdd n i)))) = (rv M (b-a)).val := by
      rw [← ha]
      rfl
    cases hi : closed i with
    | false =>
      change (finiteDiscRawProper q ∧ iVF x ∧ if closed i then _ else _) ↔ _
      simp only [hq,hx,hi,Bool.false_eq_true,ite_false,true_and,finiteDiscRawNames,
        finitePolydiscNames,hi,Bool.false_eq_true,ite_false]
      change (¬ iLe (iRv (iVFAdd x (iVFNeg (q (Fin.castAdd n i))))) (q (Fin.natAdd n i))) ↔
        b.val ∈ BallImaginaries.underlying (openDiscCode a γ)
      rw [openDiscCode_mem_iff_value,hdiff,← Values.vrv_le_iff (rv M (b-a))
        (⟨q (Fin.natAdd n i),(hq.2 i).1⟩ : RVInfinity M),not_le,← hγ]
      rfl
    | true =>
      change (finiteDiscRawProper q ∧ iVF x ∧ if closed i then _ else _) ↔ _
      simp only [hq,hx,hi,ite_true,true_and,finiteDiscRawNames,finitePolydiscNames,hi,ite_true]
      change iLe (q (Fin.natAdd n i)) (iRv (iVFAdd x (iVFNeg (q (Fin.castAdd n i))))) ↔
        b.val ∈ BallImaginaries.underlying (closedDiscCode a γ.val)
      rw [closedDiscCode_mem_iff_value,hdiff,← Values.vrv_le_iff
        (⟨q (Fin.natAdd n i),(hq.2 i).1⟩ : RVInfinity M) (rv M (b-a)),← hγ]
      rfl
  · exact ⟨fun h => (hx h.2.1).elim,fun h => (hx (disc_underlying_subset_vf _ h)).elim⟩

theorem finiteDiscRawProper_definable (S : Set M) (n : ℕ) :
    S.Definable LRV {q : Fin (n+n) → M | finiteDiscRawProper q} := by
  have hVF := (vfRawUniverse_definable S n).preimage_comp (Fin.castAdd n)
  have hNZ := Set.definable_iInter_of_finite (fun i : Fin n =>
    (GammaParameters.nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => Fin.natAdd n i))
  convert hVF.inter hNZ using 1
  ext q
  simp only [finiteDiscRawProper,vfRawUniverse,Set.mem_inter_iff,Set.mem_preimage,
    Set.mem_iInter,Set.mem_ofPred_eq,Function.comp_apply]

theorem finiteDiscRawMember_definable (S : Set M) (closed : Fin n → Bool) (i : Fin n) :
    S.Definable LRV {z : Fin (n+n) ⊕ Fin 1 → M | finiteDiscRawMember closed (z ∘ Sum.inl) i (z (.inr 0))} := by
  let Z := Fin (n+n) ⊕ Fin 1
  let d (z : Z → M) := iRv (iVFAdd (z (.inr 0)) (iVFNeg (z (.inl (Fin.castAdd n i)))))
  have hn : S.DefinableFun LRV (fun z : Z → M => iVFNeg (z (.inl (Fin.castAdd n i)))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
      (by intro j; fin_cases j; exact Set.DefinableFun.proj LRV)
  have hd : S.DefinableFun LRV (fun z : Z → M => iVFAdd (z (.inr 0)) (iVFNeg (z (.inl (Fin.castAdd n i))))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
      (by intro j; fin_cases j; exact Set.DefinableFun.proj LRV; exact hn)
  have hr : S.DefinableFun LRV d :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (by intro j; fin_cases j; exact hd)
  have hleft := (finiteDiscRawProper_definable S n).preimage_comp (Sum.inl : Fin (n+n) → Z)
  have hx := ((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : Z))
  have hcmp : S.Definable LRV {z : Z → M | if closed i then iLe (z (.inl (Fin.natAdd n i))) (d z)
      else ¬ iLe (d z) (z (.inl (Fin.natAdd n i)))} := by
    cases hi : closed i with
    | false =>
      convert ((GammaParameters.raw_le_definable S).preimage_map
        (show S.DefinableMap LRV (fun z : Z → M => ![d z,z (.inl (Fin.natAdd n i))]) from by
          intro j; fin_cases j; exact hr; exact Set.DefinableFun.proj LRV)).compl using 1
      ext z
      simp only [hi,Bool.false_eq_true,ite_false,Set.mem_compl_iff,Set.mem_preimage,Set.mem_ofPred_eq]
      rfl
    | true =>
      convert (GammaParameters.raw_le_definable S).preimage_map
        (show S.DefinableMap LRV (fun z : Z → M => ![z (.inl (Fin.natAdd n i)),d z]) from by
          intro j; fin_cases j; exact Set.DefinableFun.proj LRV; exact hr) using 1
      ext z
      simp only [hi,ite_true,Set.mem_preimage,Set.mem_ofPred_eq]
      rfl
  exact hleft.inter (hx.inter hcmp)

def finiteDiscRawEq (closed : Fin n → Bool) (q r : Fin (n+n) → M) : Prop :=
  finiteDiscRawProper q ∧ finiteDiscRawProper r ∧
    ∀ i x, finiteDiscRawMember closed q i x ↔ finiteDiscRawMember closed r i x

theorem finiteDiscRawEq_iff (closed : Fin n → Bool) (q r : Fin (n+n) → M)
    (hq : finiteDiscRawProper q) (hr : finiteDiscRawProper r) :
    finiteDiscRawEq closed q r ↔ finiteDiscRawNames closed q = finiteDiscRawNames closed r := by
  constructor
  · intro h
    funext i
    apply BallImaginaries.underlying_injective
    exact Set.ext (fun x => (finiteDiscRawMember_iff closed q hq i x).symm.trans
      ((h.2.2 i x).trans (finiteDiscRawMember_iff closed r hr i x)))
  · intro he
    refine ⟨hq,hr,fun i x => ?_⟩
    rw [finiteDiscRawMember_iff closed q hq,finiteDiscRawMember_iff closed r hr,he]

theorem finiteDiscRawEq_definable (S : Set M) (closed : Fin n → Bool) :
    S.Definable LRV {z : Fin (n+n) ⊕ Fin (n+n) → M | finiteDiscRawEq closed (z ∘ Sum.inl) (z ∘ Sum.inr)} := by
  let Z := Fin (n+n) ⊕ Fin (n+n)
  have h (i : Fin n) : S.Definable LRV {z : Z → M | ∀ x : Fin 1 → M,
      finiteDiscRawMember closed (z ∘ Sum.inl) i (x 0) ↔
        finiteDiscRawMember closed (z ∘ Sum.inr) i (x 0)} := by
    let l : Fin (n+n) ⊕ Fin 1 → Z ⊕ Fin 1 := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
    let r : Fin (n+n) ⊕ Fin 1 → Z ⊕ Fin 1 := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
    exact (raw_iff_definable ((finiteDiscRawMember_definable S closed i).preimage_comp l)
      ((finiteDiscRawMember_definable S closed i).preimage_comp r)).forall_of_finite
  convert (((finiteDiscRawProper_definable S n).preimage_comp Sum.inl).inter
    ((finiteDiscRawProper_definable S n).preimage_comp Sum.inr)).inter
      (Set.definable_iInter_of_finite h) using 1
  ext z
  simp only [finiteDiscRawEq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_iInter,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hq,hr,he⟩
    exact ⟨⟨hq,hr⟩,fun i x => he i (x 0)⟩
  · rintro ⟨⟨hq,hr⟩,he⟩
    exact ⟨hq,hr,fun i x => he i (fun _ => x)⟩

end DiamondIntegral.Section2
