import «section 7».ElementaryBlowups

/-! Definition 7.2 (`defn:blowup:coa`) on objects: a class-level blowup of
length one is realised by literal disjoint subobjects of a given object.

Statement (`step_iff_objects`). For objects `V`, `W` of `μRV^db[1+k]`,
`Step [V] [W]` holds exactly when there are aperture data `D i = (U_i, j_i, τ_i)`
(`i < n`), pairwise disjoint definable subsets `C_i ⊆ V`, measured isomorphisms
`F_i : U_i → C_i` onto the subobjects `C_i = (C_i, g ↾ C_i, σ ↾ C_i)`, and
`[W] = [V ∖ C] + Σ [U_i^♭]` with `C = ⋃ C_i`. The literal object form
(`step_iff_blowup`): `W ≅ (V ∖ C) ⊎ ⊎ᵢ U_i^♭` (`Blowup V W`), with the
iterated tagged coproduct `sumObj`. This is GAP-REPAIRS item 2 ("the
object-level converse").

Route. The direction from objects to classes splits `V` along `C` and `C`
along its disjoint pieces (`cls_eq_cpiece_add_sum`). The converse realises a
class decomposition `[V] = z + Σ p_i` by literal pieces (`exists_pieces`):
by induction on `n`, `BoundedClasses.exists_split` cuts off a definable piece of
class `p_0` (the image of the first summand under an isomorphism of `V` with a
coproduct), and the remaining pieces are found inside its complement, so they
are disjoint from it. The pieces of the complement are pieces of `V` with the
same domain, coordinates and volume (`sameIso`). -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.BlowupObjects
open DiamondIntegral.Section4
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}

/-! ### Finite unions -/

omit [LRV.Structure M] hM in
theorem iUnion_fin_succ {α : Type*} {n : ℕ} (C : Fin (n + 1) → Set α) :
    ⋃ i, C i = C 0 ∪ ⋃ i : Fin n, C i.succ := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]

/-- Finite unions of definable sets are definable. -/
theorem iUnion_definable {a : ℕ} : ∀ {n : ℕ} (C : Fin n → Set (Fin a → M))
    (_ : ∀ i, DefinableOverBase B (fun _ : Fin a => .rv) (C i)),
    DefinableOverBase B (fun _ : Fin a => .rv) (⋃ i, C i)
  | 0, C, _ => by
    rw [Set.iUnion_of_empty]
    exact DefinableOverBase.empty B _
  | n + 1, C, hC => by
    rw [iUnion_fin_succ]
    exact (hC 0).union (iUnion_definable (fun i => C i.succ) (fun i => hC i.succ))

omit [LRV.Structure M] hM in
theorem pairwise_disjoint_cons {α : Type*} {n : ℕ} (C : Fin (n + 1) → Set α)
    (h0 : ∀ i : Fin n, Disjoint (C 0) (C i.succ)) (hs : Pairwise fun i j : Fin n => Disjoint (C i.succ) (C j.succ)) :
    Pairwise fun i j => Disjoint (C i) (C j) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ j => exact h0 j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact (h0 i).symm
    | succ j => exact hs fun h => hij (congrArg Fin.succ h)

/-! ### Iterated tagged coproducts -/

/-- The iterated tagged coproduct `⊎ᵢ f i` of finitely many objects. -/
def sumObj {m : ℕ} : {n : ℕ} → (Fin n → Obj B m) → Obj B m
  | 0, _ => emptyObj B m
  | _ + 1, f => coprod (f 0) (sumObj fun i => f i.succ)

theorem cls_sumObj {m : ℕ} : ∀ {n : ℕ} (f : Fin n → Obj B m), cls (sumObj f) = ∑ i, cls (f i)
  | 0, _ => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  | n + 1, f => by
    rw [Fin.sum_univ_succ, ← cls_sumObj (fun i => f i.succ)]
    rfl

/-! ### Pieces along disjoint definable sets -/

section Pieces
variable {m : ℕ}

/-- The complement of the empty union is the whole object. -/
theorem cls_cpiece_empty (V : Obj B m) (C : Fin 0 → Set (Fin V.arity → M))
    (hU : DefinableOverBase B (fun _ : Fin V.arity => .rv) (⋃ i, C i)) :
    cls (cpiece V (⋃ i, C i) hU) = cls V := by
  apply cls_eq_of_iso
  refine sameIso (outside (ofChart V.toChart) _ hU) (ofChart V.toChart) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  change V.domain \ (⋃ i, C i) = V.domain
  rw [Set.iUnion_of_empty, Set.sdiff_empty]

/-- An object is the sum of its pieces along finitely many pairwise disjoint
definable sets and of the complement of their union. -/
theorem cls_eq_cpiece_add_sum : ∀ {n : ℕ} (V : Obj B m) (C : Fin n → Set (Fin V.arity → M))
    (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i)),
    (Pairwise fun i j => Disjoint (C i) (C j)) →
      cls V = cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) + ∑ i, cls (piece V (C i) (hC i))
  | 0, V, C, hC, _ => by
    rw [cls_cpiece_empty, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | n + 1, V, C, hC, hd => by
    have h1 := cls_partition V (C 0) (hC 0)
    have h2 := cls_eq_cpiece_add_sum (cpiece V (C 0) (hC 0)) (fun i => C i.succ) (fun i => hC i.succ)
      (fun i j hij => hd fun h => hij (Fin.succ_injective _ h))
    have h3 : cls (cpiece (cpiece V (C 0) (hC 0)) (⋃ i : Fin n, C i.succ) (iUnion_definable (fun i => C i.succ)
        (fun i => hC i.succ))) = cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) := by
      apply cls_eq_of_iso
      refine sameIso (outside (ofChart (cpiece V (C 0) (hC 0)).toChart) _ _) (outside (ofChart V.toChart) _ _)
        ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      change (V.domain \ C 0) \ (⋃ i : Fin n, C i.succ) = V.domain \ ⋃ i, C i
      rw [iUnion_fin_succ C, Set.sdiff_sdiff]
    have h4 : ∀ i : Fin n, cls (piece (cpiece V (C 0) (hC 0)) (C i.succ) (hC i.succ)) =
        cls (piece V (C i.succ) (hC i.succ)) := by
      intro i
      apply cls_eq_of_iso
      refine sameIso (inside (ofChart (cpiece V (C 0) (hC 0)).toChart) _ _) (inside (ofChart V.toChart) _ _)
        ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      change (V.domain \ C 0) ∩ C i.succ = V.domain ∩ C i.succ
      ext u
      constructor
      · rintro ⟨⟨hv, _⟩, hc⟩
        exact ⟨hv, hc⟩
      · rintro ⟨hv, hc⟩
        exact ⟨⟨hv, fun h0 => Set.disjoint_left.mp (hd (Fin.succ_ne_zero i).symm) h0 hc⟩, hc⟩
    rw [h1, h2, h3, Fin.sum_univ_succ]
    simp only [h4]
    abel

/-- A class decomposition `[V] = z + Σ p_i` is realised by literal pieces of `V`
along pairwise disjoint definable subsets, with complement of class `z`. -/
theorem exists_pieces : ∀ {n : ℕ} (V : Obj B m) (z : Cls B m) (p : Fin n → Cls B m),
    cls V = z + ∑ i, p i →
      ∃ (C : Fin n → Set (Fin V.arity → M)) (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i)),
        (∀ i, C i ⊆ V.domain) ∧ (Pairwise fun i j => Disjoint (C i) (C j)) ∧
        (∀ i, cls (piece V (C i) (hC i)) = p i) ∧
        cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) = z
  | 0, V, z, p, h => by
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [cls_cpiece_empty, h, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | n + 1, V, z, p, h => by
    have h' : cls V = p 0 + (z + ∑ i : Fin n, p i.succ) := by
      rw [h, Fin.sum_univ_succ]
      abel
    obtain ⟨I, hI, hpI, hcI⟩ := exists_split V (p 0) _ h'
    obtain ⟨C', hC', hsub', hd', hp', hz'⟩ := exists_pieces (cpiece V I hI) z (fun i => p i.succ) hcI
    obtain ⟨C, hC0, hCs⟩ : ∃ C : Fin (n + 1) → Set (Fin V.arity → M),
        C 0 = V.domain ∩ I ∧ ∀ i, C i.succ = C' i :=
      ⟨Fin.cons (V.domain ∩ I) C', Fin.cons_zero _ _, fun i => Fin.cons_succ _ _ i⟩
    have hsub'' : ∀ i, C' i ⊆ V.domain \ I := hsub'
    have hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i) := by
      intro i
      induction i using Fin.cases with
      | zero =>
        rw [hC0]
        exact V.domain_definable.inter hI
      | succ i =>
        rw [hCs]
        exact hC' i
    refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero =>
        rw [hC0]
        exact Set.inter_subset_left
      | succ i =>
        rw [hCs]
        exact fun u hu => (hsub'' i hu).1
    · apply pairwise_disjoint_cons
      · intro i
        rw [hC0, hCs]
        exact Set.disjoint_left.mpr fun u hu hu' => (hsub'' i hu').2 hu.2
      · intro i j hij
        rw [hCs, hCs]
        exact hd' hij
    · intro i
      induction i using Fin.cases with
      | zero =>
        rw [← hpI]
        apply cls_eq_of_iso
        refine sameIso (inside (ofChart V.toChart) _ _) (inside (ofChart V.toChart) _ _) ?_
          (fun _ _ => rfl) (fun _ _ => rfl)
        change V.domain ∩ C 0 = V.domain ∩ I
        rw [hC0, ← Set.inter_assoc, Set.inter_self]
      | succ i =>
        rw [← hp' i]
        apply cls_eq_of_iso
        refine sameIso (inside (ofChart V.toChart) _ _) (inside (ofChart (cpiece V I hI).toChart) _ _) ?_
          (fun _ _ => rfl) (fun _ _ => rfl)
        change V.domain ∩ C i.succ = (V.domain \ I) ∩ C' i
        rw [hCs]
        ext u
        constructor
        · rintro ⟨_, hc⟩
          exact ⟨hsub'' i hc, hc⟩
        · rintro ⟨hv, hc⟩
          exact ⟨hv.1, hc⟩
    · rw [← hz']
      apply cls_eq_of_iso
      refine sameIso (outside (ofChart V.toChart) _ _) (outside (ofChart (cpiece V I hI).toChart) _ _) ?_
        (fun _ _ => rfl) (fun _ _ => rfl)
      change V.domain \ (⋃ i, C i) = (V.domain \ I) \ ⋃ i, C' i
      rw [iUnion_fin_succ C, hC0]
      simp only [hCs]
      ext u
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
      tauto

end Pieces

/-! ### Blowups of length one on objects -/

variable {k : ℕ}

/-- Definition 7.2 on objects: `W` is isomorphic to the annular blowup
`(V ∖ C) ⊎ ⊎ᵢ U_i^♭` of `V` via measured isomorphisms `F_i : U_i → C_i` onto
pairwise disjoint definable subobjects `C_i` of `V`, where `U_i^♭` is the
elementary blowup of the aperture datum `D i` and `C = ⋃ C_i`. -/
def Blowup (V W : Obj B (1 + k)) : Prop :=
  ∃ (n : ℕ) (D : Fin n → AnnularDatum B k) (C : Fin n → Set (Fin V.arity → M))
    (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i)),
    (∀ i, C i ⊆ V.domain) ∧ (Pairwise fun i j => Disjoint (C i) (C j)) ∧
    (∀ i, Nonempty (Iso (D i).source.toChart (piece V (C i) (hC i)).toChart)) ∧
    Nonempty (Iso W.toChart
      (coprod (cpiece V (⋃ i, C i) (iUnion_definable C hC)) (sumObj fun i => (D i).annularObject)).toChart)

/-- The object-level data of Definition 7.2 give a blowup of length one on
classes. -/
theorem step_of_objects {V W : Obj B (1 + k)} {n : ℕ} (D : Fin n → AnnularDatum B k)
    (C : Fin n → Set (Fin V.arity → M)) (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j))
    (F : ∀ i, Nonempty (Iso (D i).source.toChart (piece V (C i) (hC i)).toChart))
    (hW : cls W = cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) + ∑ i, cls (D i).annularObject) :
    Step (cls V) (cls W) := by
  refine ⟨n, D, cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)), ?_, hW⟩
  rw [cls_eq_cpiece_add_sum V C hC hd]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨Fi⟩ := F i
  exact (cls_eq_of_iso Fi).symm

/-- **The object-level converse of Definition 7.2** (GAP-REPAIRS 2): a blowup of
length one on classes of a given object `V` is realised by measured
isomorphisms `F_i : U_i → C_i` onto literal pairwise disjoint definable
subobjects `C_i` of `V`. -/
theorem objects_of_step {V W : Obj B (1 + k)} (h : Step (cls V) (cls W)) :
    ∃ (n : ℕ) (D : Fin n → AnnularDatum B k) (C : Fin n → Set (Fin V.arity → M))
      (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i)),
      (∀ i, C i ⊆ V.domain) ∧ (Pairwise fun i j => Disjoint (C i) (C j)) ∧
      (∀ i, Nonempty (Iso (D i).source.toChart (piece V (C i) (hC i)).toChart)) ∧
      cls W = cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) + ∑ i, cls (D i).annularObject := by
  obtain ⟨n, D, z, hV, hW⟩ := h
  obtain ⟨C, hC, hsub, hd, hp, hz⟩ := exists_pieces V z (fun i => cls (D i).source) hV
  exact ⟨n, D, C, hC, hsub, hd, fun i => cls_eq_iff.mp (hp i).symm, by rw [hW, hz]⟩

/-- **Definition 7.2, class level versus object level.** For objects `V`, `W`
of `μRV^db[1+k]`, `Step [V] [W]` holds exactly when there are aperture data
`D i = (U_i, j_i, τ_i)`, pairwise disjoint definable subsets `C_i ⊆ V`, measured
isomorphisms `F_i : U_i → C_i` onto the subobjects `C_i`, and
`[W] = [V ∖ C] + Σᵢ [U_i^♭]`. -/
theorem step_iff_objects (V W : Obj B (1 + k)) :
    Step (cls V) (cls W) ↔
      ∃ (n : ℕ) (D : Fin n → AnnularDatum B k) (C : Fin n → Set (Fin V.arity → M))
        (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i)),
        (∀ i, C i ⊆ V.domain) ∧ (Pairwise fun i j => Disjoint (C i) (C j)) ∧
        (∀ i, Nonempty (Iso (D i).source.toChart (piece V (C i) (hC i)).toChart)) ∧
        cls W = cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) + ∑ i, cls (D i).annularObject :=
  ⟨objects_of_step, fun ⟨_, D, C, hC, _, hd, F, hW⟩ => step_of_objects D C hC hd F hW⟩

theorem cls_blowupObject (V : Obj B (1 + k)) {n : ℕ} (D : Fin n → AnnularDatum B k)
    (C : Fin n → Set (Fin V.arity → M)) (hC : ∀ i, DefinableOverBase B (fun _ : Fin V.arity => .rv) (C i)) :
    cls (coprod (cpiece V (⋃ i, C i) (iUnion_definable C hC)) (sumObj fun i => (D i).annularObject)) =
      cls (cpiece V (⋃ i, C i) (iUnion_definable C hC)) + ∑ i, cls (D i).annularObject := by
  rw [cls_coprod, cls_sumObj]

/-- An object-level blowup of length one (Definition 7.2) gives a blowup step
on classes. -/
theorem Blowup.step {V W : Obj B (1 + k)} (h : Blowup V W) : Step (cls V) (cls W) := by
  obtain ⟨n, D, C, hC, hsub, hd, F, ⟨G⟩⟩ := h
  exact step_of_objects D C hC hd F ((cls_eq_of_iso G).trans (cls_blowupObject V D C hC))

/-- **Definition 7.2 on objects and on classes agree.** `Step [V] [W]` holds
exactly when `W ≅ (V ∖ C) ⊎ ⊎ᵢ U_i^♭` for measured isomorphisms
`F_i : U_i → C_i` onto literal pairwise disjoint definable subobjects `C_i` of
`V`. -/
theorem step_iff_blowup (V W : Obj B (1 + k)) : Step (cls V) (cls W) ↔ Blowup V W := by
  refine ⟨fun h => ?_, Blowup.step⟩
  obtain ⟨n, D, C, hC, hsub, hd, F, hW⟩ := objects_of_step h
  exact ⟨n, D, C, hC, hsub, hd, F, cls_eq_iff.mp (hW.trans (cls_blowupObject V D C hC).symm)⟩

end DiamondIntegral.Section7.BlowupObjects
