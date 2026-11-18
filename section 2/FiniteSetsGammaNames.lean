import «section 2».GammaStableEmbedding
import «section 2».FiniteSets
import Section3.GammaSpecialization
import Section3.GammaProjection
import Section3.GammaBaseVFAlgebraicity
import Section3.AclModelGeometry

/-! Lemma 2.12 (`finite:VF:project:RV`) over a base with Γ names.

A finite VF set definable over a real base `S` together with finitely many Γ
names is definable over `S` alone (`finite_named_real_definable`), so the real
Lemma 2.12 applies (`lemma_2_12_gammaNames`).

Proof. Every coordinate is algebraic over `S` (named Γ elements add no VF
algebraicity), so the set lies in a finite `S`-definable set `Z`. For an
automorphism `σ` over `S`, the codes of the names and their images under `σ`
have the same ℤ-type over the values of a small substructure inside
`acl(S)`: those values are fixed by `σ`, because `σ` permutes every finite
`S`-definable set of conjugates order-preservingly
(`aut_fixes_acl_values`). The tuple step of stable embeddedness gives an
automorphism `τ` fixing `Z` pointwise and moving the image codes back to codes
of the same names; code invariance of the defining relation then shows that
the set is `σ`-invariant. A finite invariant subset of `Z` is definable over
`S` by strong homogeneity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2.GammaStable
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
set_option linter.unusedSectionVars false

/-! ### The normalized structure is the canonical one -/

omit hM in
/-- On a canonical structure, normalization changes nothing. -/
theorem normalize_eq (hc : CanonicalStructure.IsCanonical (M := M)) :
    CanonicalStructure.normalize (M := M) = sM := by
  have hf : @Structure.funMap LRV M (CanonicalStructure.normalize (M := M)) = @Structure.funMap LRV M sM := by
    funext n f xs
    change (if ∀ i, sortEval (Fn.argSort f i) (xs i) then Structure.funMap (L := LRV) f xs
      else CanonicalStructure.sortZero (Fn.resSort f)) = _
    split_ifs with h
    · rfl
    · exact (hc.1 f xs h).symm
  have hr : @Structure.RelMap LRV M (CanonicalStructure.normalize (M := M)) = @Structure.RelMap LRV M sM := by
    funext n r xs
    apply propext
    cases r with
    | memVF => exact Iff.rfl
    | memRV => exact Iff.rfl
    | memUnits => exact Iff.rfl
    | rvLe =>
      change ((∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs) ↔ _
      refine ⟨fun h => h.2,fun h => ⟨?_,h⟩⟩
      by_contra hn
      exact hc.2 xs hn h
  calc CanonicalStructure.normalize (M := M) =
        ⟨@Structure.funMap LRV M (CanonicalStructure.normalize (M := M)),
          @Structure.RelMap LRV M (CanonicalStructure.normalize (M := M))⟩ := rfl
    _ = ⟨@Structure.funMap LRV M sM,@Structure.RelMap LRV M sM⟩ := by rw [hf,hr]
    _ = sM := rfl

/-! ### Automorphisms fix the values of `acl(S)` -/

/-- A strictly monotone self-map of a finite subset of a linear order is the identity on it. -/
theorem strictMono_mapsTo_fixed {α : Type*} [LinearOrder α] {f : α → α} (hf : StrictMono f)
    {V : Set α} (hV : V.Finite) (hmap : Set.MapsTo f V V) : ∀ v ∈ V, f v = v := by
  have hbij := (hV.injOn_iff_bijOn_of_mapsTo hmap).mp hf.injective.injOn
  by_contra hno
  push_neg at hno
  let B := {v | v ∈ V ∧ f v ≠ v}
  have hB : B.Finite := hV.subset (fun _ h => h.1)
  have hBne : B.Nonempty := by
    obtain ⟨v,hv,hfv⟩ := hno
    exact ⟨v,hv,hfv⟩
  obtain ⟨v₀,hv₀B,hmin⟩ := hB.exists_minimal hBne
  obtain ⟨hv₀,hfv₀⟩ := hv₀B
  have hmin' : ∀ w ∈ V, w < v₀ → f w = w := by
    intro w hw hwv
    by_contra hfw
    exact absurd (hmin ⟨hw,hfw⟩ hwv.le) (not_le.mpr hwv)
  rcases lt_or_gt_of_ne hfv₀ with hlt | hgt
  · have h1 := hmin' (f v₀) (hmap hv₀) hlt
    exact hfv₀ (hf.injective h1)
  · obtain ⟨w,hw,hwv⟩ := hbij.surjOn hv₀
    have hwne : w ≠ v₀ := by
      intro he
      rw [he] at hwv
      exact hfv₀ hwv
    rcases lt_or_gt_of_ne hwne with hwl | hwg
    · have := hmin' w hw hwl
      rw [this] at hwv
      exact hwne hwv
    · have := hf hwg
      rw [hwv] at this
      exact absurd hgt (not_lt.mpr this.le)

/-- An automorphism over `S` fixes the value of every RV element of `acl(S)`. -/
theorem aut_fixes_acl_values (σ : M ≃[LRV] M) (S : Set M) (hσ : ∀ x ∈ S, σ x = x)
    (c : RVS M) (hcS : c.val ∈ algebraicClosureSet S) : Values.vrv (autRV σ c) = Values.vrv c := by
  obtain ⟨F,hF,hFfin,hcF⟩ := algebraicAt_rv_of_mem_acl S c hcS
  have hFraw : S.Definable LRV {z : Fin 1 → M | z 0 ∈ F} := hF.1.raw_definable
  have hσF : ∀ x ∈ F, σ x ∈ F := by
    intro x hx
    have h := (aut_mem_definable_iff σ hσ hFraw ![x]).mpr hx
    exact h
  let F' : Set (RVS M) := {t | t.val ∈ F}
  have hF'fin : F'.Finite := hFfin.preimage Subtype.val_injective.injOn
  let V : Set (Values.GammaTop (M := M)) := Values.vrv '' F'
  let σΓ : Values.GammaTop (M := M) → Values.GammaTop (M := M) :=
    fun x => Values.vrv (autRV σ (Classical.choose (Values.vrv_surjective x)))
  have hσΓ (t : RVS M) : σΓ (Values.vrv t) = Values.vrv (autRV σ t) :=
    autRV_vrv_congr σ (Classical.choose_spec (Values.vrv_surjective (Values.vrv t)))
  have hmono : StrictMono σΓ := by
    intro x y hxy
    obtain ⟨tx,rfl⟩ := Values.vrv_surjective x
    obtain ⟨ty,rfl⟩ := Values.vrv_surjective y
    rw [hσΓ,hσΓ]
    exact lt_of_not_ge (fun h => absurd ((autRV_le_iff σ ty tx).mp h) (not_le.mpr hxy))
  have hmap : Set.MapsTo σΓ V V := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hσΓ]
    exact ⟨autRV σ t,hσF t.val ht,rfl⟩
  have hfix := strictMono_mapsTo_fixed hmono (hF'fin.image _) hmap (Values.vrv c) ⟨c,hcF,rfl⟩
  rwa [hσΓ] at hfix

/-! ### Types of tuples and automorphisms -/

theorem tupleAssignment_formula_definable (S : Set M) {n m : ℕ}
    (φ : LRV.BoundedFormula (S ⊕ Fin n) m) (p : Fin m → S ⊕ Fin n) :
    S.Definable LRV {x : Fin n → M | φ.Realize (Sum.elim Subtype.val x) (Sum.elim Subtype.val x ∘ p)} := by
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨φ.toFormula.relabel (Sum.elim id p),?_⟩
  ext x
  simp only [Set.mem_setOf_eq,Formula.realize_relabel,BoundedFormula.realize_toFormula]
  rfl

/-- Tuples with the same type over `S` are conjugate over `S`. -/
theorem exists_automorphism_of_same_tuple_type {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hh : StronglyHomogeneous M κ) (S : Set M) (hS : Cardinal.mk S < κ) {n : ℕ} (a z : Fin n → M)
    (htype : ∀ D : Set (Fin n → M), S.Definable LRV D → (a ∈ D ↔ z ∈ D)) :
    ∃ ρ : M ≃[LRV] M, (∀ x ∈ S, ρ x = x) ∧ ∀ i, ρ (a i) = z i := by
  have hpe : PartialElementary (Sum.elim (Subtype.val : S → M) a) (Sum.elim (Subtype.val : S → M) z) := by
    intro m φ p
    exact htype _ (tupleAssignment_formula_definable S φ p)
  have hsize : Cardinal.mk (S ⊕ Fin n) < κ := by
    simpa only [Cardinal.mk_sum,Cardinal.mk_fin,Cardinal.lift_id,Cardinal.lift_natCast] using
      Cardinal.add_lt_of_lt hκ hS (Cardinal.natCast_lt_aleph0.trans_le hκ)
  obtain ⟨ρ,hρ⟩ := hh (S ⊕ Fin n) _ _ hsize hpe
  exact ⟨ρ,fun x hx => hρ (.inl ⟨x,hx⟩),fun i => hρ (.inr i)⟩

/-- A finite set inside a finite `S`-definable set, invariant under every
automorphism over `S`, is definable over `S`. -/
theorem finite_invariant_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hh : StronglyHomogeneous M κ) (S : Set M) (hS : Cardinal.mk S < κ) {n : ℕ}
    (A Z : Set (Fin n → M)) (hZ : S.Definable LRV Z) (hZfin : Z.Finite) (hAZ : A ⊆ Z)
    (hinv : ∀ ρ : M ≃[LRV] M, (∀ x ∈ S, ρ x = x) → ∀ a ∈ A, (fun i => ρ (a i)) ∈ A) :
    S.Definable LRV A := by
  have hsep : ∀ a ∈ A, ∀ z ∈ Z \ A, ∃ D : Set (Fin n → M), S.Definable LRV D ∧ a ∈ D ∧ z ∉ D := by
    intro a ha z hz
    by_contra hno
    push_neg at hno
    have htype : ∀ D : Set (Fin n → M), S.Definable LRV D → (a ∈ D ↔ z ∈ D) := by
      intro D hD
      refine ⟨hno D hD,fun hzD => ?_⟩
      by_contra haD
      exact (hno Dᶜ hD.compl haD) hzD
    obtain ⟨ρ,hρS,hρ⟩ := exists_automorphism_of_same_tuple_type hκ hh S hS a z htype
    have hz' := hinv ρ hρS a ha
    rw [show (fun i => ρ (a i)) = z from funext hρ] at hz'
    exact hz.2 hz'
  choose! D hD using hsep
  have hAfin : A.Finite := hZfin.subset hAZ
  have hdiff : (Z \ A).Finite := hZfin.subset Set.diff_subset
  have he : A = Z ∩ ⋃ a ∈ hAfin.toFinset, ⋂ z ∈ hdiff.toFinset, D a z := by
    ext x
    constructor
    · intro hx
      refine ⟨hAZ hx,Set.mem_biUnion (hAfin.mem_toFinset.mpr hx) (Set.mem_iInter₂.mpr ?_)⟩
      intro z hz
      exact (hD x hx z (hdiff.mem_toFinset.mp hz)).2.1
    · rintro ⟨hxZ,hx⟩
      obtain ⟨a,ha,hxa⟩ := Set.mem_iUnion₂.mp hx
      by_contra hxA
      have := Set.mem_iInter₂.mp hxa x (hdiff.mem_toFinset.mpr ⟨hxZ,hxA⟩)
      exact (hD a (hAfin.mem_toFinset.mp ha) x ⟨hxZ,hxA⟩).2.2 this
  let D' : (Fin n → M) → (Fin n → M) → Set (Fin n → M) := fun a z =>
    if a ∈ A ∧ z ∈ Z \ A then D a z else ∅
  have hD'def (a z : Fin n → M) : S.Definable LRV (D' a z) := by
    by_cases h : a ∈ A ∧ z ∈ Z \ A
    · simp only [D',if_pos h]
      exact (hD a h.1 z h.2).1
    · simp only [D',if_neg h]
      exact Set.definable_empty
  have he' : (⋃ a ∈ hAfin.toFinset, ⋂ z ∈ hdiff.toFinset, D a z) =
      ⋃ a ∈ hAfin.toFinset, ⋂ z ∈ hdiff.toFinset, D' a z := by
    refine Set.iUnion₂_congr (fun a ha => Set.iInter₂_congr (fun z hz => ?_))
    simp only [D',if_pos (show a ∈ A ∧ z ∈ Z \ A from ⟨hAfin.mem_toFinset.mp ha,hdiff.mem_toFinset.mp hz⟩)]
  rw [he,he']
  exact hZ.inter (Set.definable_biUnion_finset
    (fun a => Set.definable_biInter_finset (fun z => hD'def a z) hdiff.toFinset) hAfin.toFinset)

/-- Automorphisms over `P` preserve sets definable over `P`, for any index type. -/
theorem aut_mem_definable_iff_any (σ : M ≃[LRV] M) {P : Set M} (hσ : ∀ x ∈ P, σ x = x)
    {α : Type} {D : Set (α → M)} (hD : P.Definable LRV D) (a : α → M) :
    (fun i => σ (a i)) ∈ D ↔ a ∈ D := by
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hD
  rw [hφ]
  have h := StrongHomClass.realize_formula σ φ (v := Sum.elim (Subtype.val : P → M) a)
  have hv : (σ ∘ Sum.elim (Subtype.val : P → M) a) = Sum.elim (Subtype.val : P → M) (fun i => σ (a i)) := by
    funext x
    cases x with
    | inl p => exact hσ p.val p.property
    | inr i => rfl
  rw [hv] at h
  exact h

/-! ### Finite VF sets definable with Γ names -/

/-- A finite VF set definable over a real base with Γ names is definable over
the real base. -/
theorem finite_named_real_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hh : StronglyHomogeneous M κ)
    (S : Set M) (hS : Cardinal.mk S < κ) (G : Set (Values.Gamma (M := M))) {n : ℕ}
    (A : Set (Fin n → M)) (hfin : A.Finite)
    (hA : GammaParameters.DefinableOverBase ⟨S,G⟩ (fun _ : Fin n => SortTag.vf) A) :
    SpecialTransformations.Section3.DefinableOver S (fun _ : Fin n => SortTag.vf) A := by
  obtain ⟨k,γ,_,R,hR⟩ := hA
  have hsort : ∀ x ∈ A, ∀ i, sortEval SortTag.vf (x i) := by
    rw [← hR]
    exact R.fibre_proper γ
  have hcar : S.Definable LRV {z : Fin k ⊕ Fin n → M | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R.carrier} := by
    have h := R.definable
    rwa [normalize_eq hc] at h
  -- Coordinates are algebraic over the real base.
  have halg : ∀ x ∈ A, ∀ i, ∃ s : Set M,
      SpecialTransformations.Section3.DefinableAt S .vf s ∧ s.Finite ∧ x i ∈ s := by
    intro x hx i
    let Ai : Set M := {y | ∃ x' ∈ A, x' i = y}
    have hAi : GammaParameters.DefinableAtBase ⟨S,G⟩ .vf Ai := by
      have h := (GammaParameters.DefinableOverBase.image_real ⟨k,γ,by assumption,R,hR⟩
        (fun _ : Fin 1 => i))
      have hset : {z : Fin 1 → M | z 0 ∈ Ai} = (fun x => x ∘ fun _ : Fin 1 => i) '' A := by
        ext z
        constructor
        · rintro ⟨x',hx',he⟩
          exact ⟨x',hx',funext (fun j => by fin_cases j; exact he)⟩
        · rintro ⟨x',hx',he⟩
          exact ⟨x',hx',(congrFun he 0)⟩
      change GammaParameters.DefinableOverBase ⟨S,G⟩ (fun _ : Fin 1 => SortTag.vf) {z | z 0 ∈ Ai}
      rw [hset]
      exact h
    have hAifin : Ai.Finite := (hfin.image (fun x' => x' i)).subset (by
      rintro y ⟨x',hx',rfl⟩
      exact ⟨x',hx',rfl⟩)
    let b : VFType (M := M) := ⟨x i,hsort x hx i⟩
    have hb : GammaParameters.AlgebraicAtBase ⟨S,G⟩ .vf b.val := ⟨Ai,hAi,hAifin,⟨x,hx,rfl⟩⟩
    exact (GammaParameters.algebraic_vf_iff_real ⟨S,G⟩ b).mp hb
  choose! s hs using halg
  -- The finite `S`-definable envelope `Z`.
  let Zi (i : Fin n) : Set M := ⋃ x ∈ hfin.toFinset, s x i
  have hZifin (i : Fin n) : (Zi i).Finite :=
    Set.Finite.biUnion hfin.toFinset.finite_toSet (fun x hx => (hs x (hfin.mem_toFinset.mp hx) i).2.1)
  have hZidef (i : Fin n) : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Zi i} := by
    let f : (Fin n → M) → Set (Fin 1 → M) := fun x => if x ∈ A then {z | z 0 ∈ s x i} else ∅
    have hf (x : Fin n → M) : S.Definable LRV (f x) := by
      by_cases hx : x ∈ A
      · simp only [f,if_pos hx]
        exact (hs x hx i).1.1.raw_definable
      · simp only [f,if_neg hx]
        exact Set.definable_empty
    have h := Set.definable_biUnion_finset hf hfin.toFinset
    convert h using 1
    ext z
    simp only [Zi,f,Set.mem_setOf_eq,Set.mem_iUnion,Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨x,hx,hz⟩
      exact ⟨x,hx,by rw [if_pos hx]; exact hz⟩
    · rintro ⟨x,hx,hz⟩
      rw [if_pos hx] at hz
      exact ⟨x,hx,hz⟩
  let Z : Set (Fin n → M) := {y | ∀ i, y i ∈ Zi i}
  have hZdef : S.Definable LRV Z := by
    have h := Set.definable_iInter_of_finite (fun i : Fin n => (hZidef i).preimage_comp (fun _ : Fin 1 => i))
    convert h using 1
    ext y
    simp only [Z,Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage,Function.comp_apply]
  have hZfin : Z.Finite := (Set.Finite.pi (t := Zi) (fun i => hZifin i)).subset (by
    intro y hy
    exact fun i _ => hy i)
  have hAZ : A ⊆ Z := fun x hx i =>
    Set.mem_biUnion (hfin.mem_toFinset.mpr hx) (hs x hx i).2.2
  have hZacl : ∀ y ∈ Z, ∀ i, y i ∈ algebraicClosureSet S := by
    intro y hy i
    obtain ⟨x,hx,hyx⟩ := Set.mem_iUnion₂.mp (hy i)
    have hxA := hfin.mem_toFinset.mp hx
    exact ⟨.vf,s x i,(hs x hxA i).1,(hs x hxA i).2.1,hyx⟩
  -- A small substructure inside `acl(S)` containing `S` and the coordinates of `Z`.
  let W : Set M := S ∪ {w | ∃ y ∈ Z, ∃ i, y i = w}
  have hWsmall : Cardinal.mk W < κ := by
    have hfinW : {w | ∃ y ∈ Z, ∃ i, y i = w}.Finite := by
      have : {w | ∃ y ∈ Z, ∃ i, y i = w} = ⋃ y ∈ hZfin.toFinset, Set.range y := by
        ext w
        simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_range,Set.Finite.mem_toFinset,exists_prop]
      rw [this]
      exact Set.Finite.biUnion hZfin.toFinset.finite_toSet (fun y _ => Set.finite_range y)
    exact (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hS
      (hfinW.lt_aleph0.trans hκ))
  let K := Substructure.closure LRV W
  have hKsmall : Cardinal.mk (K : Set M) < κ := closure_small hκ W hWsmall
  have hKacl : (K : Set M) ⊆ algebraicClosureSet S := by
    have hle : K ≤ algebraicClosureSubstructure hc S := by
      apply (Substructure.closure_le (L := LRV)).mpr
      rintro w (hw | ⟨y,hy,i,rfl⟩)
      · exact subset_algebraicClosureSet S hw
      · exact hZacl y hy i
    exact hle
  have hWK : W ⊆ (K : Set M) := Substructure.subset_closure
  -- Invariance under automorphisms over `S`.
  have hinv : ∀ σ : M ≃[LRV] M, (∀ x ∈ S, σ x = x) → ∀ b ∈ A, (fun i => σ (b i)) ∈ A := by
    intro σ hσ b hb
    let t := GammaParameters.representatives γ
    let T : Fin k → RVS M := fun i => (t i).val
    have hT0 (i : Fin k) : T i ≠ 0 := by
      intro h
      apply (t i).property
      have h' := congrArg Subtype.val h
      rwa [RVOperations.zero_val] at h'
    let T' : Fin k → RVS M := fun i => autRV σ (T i)
    have hType : CodeTupleTypeEq K T' T := by
      intro m c hcK hc0
      have hfixc : Values.vrv (autRV σ c) = Values.vrv c :=
        aut_fixes_acl_values σ S hσ c (hKacl hcK)
      change Values.vrv (∏ i, autRV σ (T i) ^ m i) ≤ Values.vrv c ↔ _
      rw [← autRV_prod]
      calc Values.vrv (autRV σ (∏ i, T i ^ m i)) ≤ Values.vrv c ↔
            Values.vrv (autRV σ (∏ i, T i ^ m i)) ≤ Values.vrv (autRV σ c) := by rw [hfixc]
        _ ↔ _ := autRV_le_iff σ _ c
    obtain ⟨τ,hτK,hτ⟩ := exists_automorphism_code_tuple hc hκ hh k K hKsmall T' T
      (fun i => autRV_ne_zero σ (hT0 i)) hT0 hType
    -- Carrier membership is preserved by automorphisms over `S`.
    have hpres (ρ : M ≃[LRV] M) (hρ : ∀ x ∈ S, ρ x = x) (u : Fin k → M) (y : Fin n → M)
        (hy : (u,y) ∈ R.carrier) : ((fun i => ρ (u i)),(fun i => ρ (y i))) ∈ R.carrier := by
      have h := (aut_mem_definable_iff_any ρ hρ hcar (Sum.elim u y)).mpr (by
        change (Sum.elim u y ∘ Sum.inl,Sum.elim u y ∘ Sum.inr) ∈ R.carrier
        rwa [Sum.elim_comp_inl,Sum.elim_comp_inr])
      change ((fun j => ρ (Sum.elim u y j)) ∘ Sum.inl,(fun j => ρ (Sum.elim u y j)) ∘ Sum.inr) ∈ R.carrier at h
      exact h
    have hb0 : (GammaParameters.rawTuple t,b) ∈ R.carrier := by
      have := (R.mem_fibre_iff t γ (GammaParameters.representatives_values γ) b).mp
      rw [hR] at this
      exact this hb
    have hτS : ∀ x ∈ S, τ x = x := fun x hx => hτK x (hWK (Or.inl hx))
    have h1 := hpres σ hσ _ b hb0
    have h2 := hpres τ hτS _ _ h1
    -- `τ` fixes `σ b`, whose coordinates lie in `Z`.
    have hσbZ : (fun i => σ (b i)) ∈ Z := (aut_mem_definable_iff σ hσ hZdef b).mpr (hAZ hb)
    have hτσb : (fun i => τ (σ (b i))) = (fun i => σ (b i)) :=
      funext (fun i => hτK _ (hWK (Or.inr ⟨_,hσbZ,i,rfl⟩)))
    rw [hτσb] at h2
    -- The new codes have the same values as the old ones.
    let u : Fin k → GammaParameters.Code (M := M) := fun i =>
      ⟨autRV τ (autRV σ (T i)),fun he => autRV_ne_zero τ (autRV_ne_zero σ (hT0 i))
        (Subtype.ext (he.trans RVOperations.zero_val.symm))⟩
    have hu : GammaParameters.values u = γ := by
      funext i
      apply Subtype.ext
      change Values.vrv (autRV τ (autRV σ (T i))) = (γ i).val
      rw [hτ i (autRV σ (T i)) rfl]
      have := congrArg Subtype.val (congrFun (GammaParameters.representatives_values γ) i)
      exact this
    have h3 : (GammaParameters.rawTuple u,fun i => σ (b i)) ∈ R.carrier := h2
    rw [← hR]
    exact (R.mem_fibre_iff u γ hu _).mpr h3
  have hraw : S.Definable LRV A :=
    finite_invariant_definable hκ.le hh S hS A Z hZdef hZfin hAZ hinv
  exact raw_definableOver_sorted hc S _ A hraw hsort

/-- Lemma 2.12 over a base with Γ names: a finite VF set definable over a real
base together with Γ names is in definable bijection with a set of nonzero RV
tuples, with image and graph definable over the same base. -/
theorem lemma_2_12_gammaNames (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hh : StronglyHomogeneous M κ)
    (S : Set M) (hS : Cardinal.mk S < κ) (G : Set (Values.Gamma (M := M))) {n : ℕ}
    (A : Set (Fin n → VF M)) (hfin : A.Finite)
    (hA : GammaParameters.DefinableOverBase ⟨S,G⟩ (fun _ => SortTag.vf) (FiniteCoding.values '' A)) :
    ∃ m : ℕ, ∃ U : Set (Fin m → M), ∃ e : A ≃ U,
      (∀ t ∈ U, ∀ j, iRV (t j) ∧ t j ≠ iRVZero) ∧
      GammaParameters.DefinableOverBase ⟨S,G⟩ (fun _ => SortTag.rv) U ∧
      GammaParameters.DefinableOverBase ⟨S,G⟩ FiniteCoding.graphSort
        (FiniteCoding.graph A (fun a => (e a).val)) := by
  have hreal := finite_named_real_definable hc hκ hh S hS G (FiniteCoding.values '' A) (hfin.image _) hA
  obtain ⟨m,U,e,hU,hUdef,hgraph⟩ := lemma_2_12 hc h00 S A hfin hreal
  exact ⟨m,U,e,hU,GammaParameters.real_definableOverBase ⟨S,G⟩ _ U hUdef,
    GammaParameters.real_definableOverBase ⟨S,G⟩ _ _ hgraph⟩

end DiamondIntegral.Section2.GammaStable
