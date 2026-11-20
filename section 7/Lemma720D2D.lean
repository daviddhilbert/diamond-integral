import «section 7».Lemma720Slope
import «section 3».IntegrationDiscToDisc

/-! Lemma 7.20, step 7: the disc-to-disc property off the locally constant locus.

* `mixedDefinable_iff`: Section 2's `MixedDefinable` over `⟨S, ∅⟩` is Section 6
  definability of the raw codes.
* `exists_d2d_pieces`: the map `(x, w) ↦ (ε(x, w), w ⌢ c₁(x, w))` is injective off the
  locus `L` of the constant-or-injective codes. Lemma 2.32 (`integration_lemma_2_32`,
  Yin's Proposition 3.19; not a Hrushovski–Kazhdan result) gives finitely many definable
  pieces on which it has the disc-to-disc property. Hence `ε(·, w)` maps open discs
  inside one piece with constant code to open discs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3ACVF

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem mixedValues_eq_mixedTuple {n r : ℕ} (q : Mixed M n r) :
    mixedValues q = mixedTuple q ∘ finSumFinEquiv := by
  funext i
  rcases i with i | i
  · change vfValues q.1 i = Fin.append (vfValues q.1) (rvValues q.2) (finSumFinEquiv (Sum.inl i))
    rw [finSumFinEquiv_apply_left, Fin.append_left]
  · change rvValues q.2 i = Fin.append (vfValues q.1) (rvValues q.2) (finSumFinEquiv (Sum.inr i))
    rw [finSumFinEquiv_apply_right, Fin.append_right]

theorem preimage_eq_image {n r : ℕ} (X : Set (Mixed M n r)) :
    (rawMixedSpace (M := M) n r).preimage X = mixedValues '' X := by
  ext z
  constructor
  · rintro ⟨hz, hX⟩
    exact ⟨_, hX, mixedValues_decode ⟨z, hz⟩⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨mixedValues_mem_domain q, ?_⟩
    rw [decode_mixedValues]
    exact hq

theorem mixedTuple_image_eq {n r : ℕ} (X : Set (Mixed M n r)) :
    mixedTuple '' X = (fun z : Fin (n + r) → M => z ∘ finSumFinEquiv) ⁻¹' (mixedValues '' X) := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, mixedValues_eq_mixedTuple q⟩
  · rintro ⟨q, hq, he⟩
    refine ⟨q, hq, ?_⟩
    rw [mixedValues_eq_mixedTuple] at he
    funext i
    have := congrFun he (finSumFinEquiv.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this

theorem mixedTuple_sorted {n r : ℕ} (q : Mixed M n r) (i : Fin (n + r)) :
    sortEval (mixedSort n r i) (mixedTuple q i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mixedSort, mixedTuple, Fin.append_left]
    exact (q.1 j).property
  · simp only [mixedSort, mixedTuple, Fin.append_right]
    exact (q.2 j).property

theorem mixedDefinable_iff (hc : CanonicalStructure.IsCanonical (M := M)) {n r : ℕ} (X : Set (Mixed M n r)) :
    MixedDefinable (⟨S, ∅⟩ : ParameterBase M) X ↔ (rawMixedSpace (M := M) n r).Definable S X := by
  unfold MixedDefinable
  change _ ↔ S.Definable LRV ((rawMixedSpace (M := M) n r).preimage X)
  rw [preimage_eq_image]
  constructor
  · intro hm
    have h1 := (GammaParameters.base_empty_iff S _ _).mp hm
    have h2 := ((definableOver_iff_normalized_raw S _ _).mp h1).1
    rw [canonical_normalize_eq hc] at h2
    have h' := h2.preimage_comp (finSumFinEquiv.symm : Fin (n + r) → Fin n ⊕ Fin r)
    have key : (mixedValues '' X : Set (Fin n ⊕ Fin r → M)) =
        (fun g => g ∘ (finSumFinEquiv.symm : Fin (n + r) → Fin n ⊕ Fin r)) ⁻¹' (mixedTuple '' X) := by
      rw [mixedTuple_image_eq]
      ext z
      simp only [Set.mem_preimage, Function.comp_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    change S.Definable LRV (mixedValues '' X : Set (Fin n ⊕ Fin r → M))
    rw [key]
    exact h'
  · intro h
    apply (GammaParameters.base_empty_iff S _ _).mpr
    apply (definableOver_iff_normalized_raw S _ _).mpr
    refine ⟨?_, ?_⟩
    · rw [canonical_normalize_eq hc, mixedTuple_image_eq]
      exact h.preimage_comp (finSumFinEquiv : Fin n ⊕ Fin r → Fin (n + r))
    · rintro z ⟨q, -, rfl⟩ i
      exact mixedTuple_sorted q i

theorem sorted_definable (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {m : ℕ}
    (sn : Fin m → SortTag) : S.Definable LRV (GammaParameters.sortedUniverse sn) := by
  have h := ((definableOver_iff_normalized_raw S sn _).mp (GammaParameters.sortedUniverse_definable S sn)).1
  rw [canonical_normalize_eq hc] at h
  exact h

/-- The first block of a code of a pair. -/
def blk₁ {n r k s : ℕ} (z : Fin ((n + r) + (k + s)) → M) : Fin n ⊕ Fin r → M :=
  fun i => z (Fin.castAdd (k + s) (finSumFinEquiv i))

/-- The second block of a code of a pair. -/
def blk₂ {n r k s : ℕ} (z : Fin ((n + r) + (k + s)) → M) : Fin k ⊕ Fin s → M :=
  fun j => z (Fin.natAdd (n + r) (finSumFinEquiv j))

theorem blk₁_append {n r k s : ℕ} (x : Mixed M n r) (y : Mixed M k s) :
    blk₁ (Fin.append (mixedTuple x) (mixedTuple y)) = mixedValues x := by
  funext i
  simp only [blk₁, Fin.append_left, mixedValues_eq_mixedTuple, Function.comp_apply]

theorem blk₂_append {n r k s : ℕ} (x : Mixed M n r) (y : Mixed M k s) :
    blk₂ (Fin.append (mixedTuple x) (mixedTuple y)) = mixedValues y := by
  funext i
  simp only [blk₂, Fin.append_right, mixedValues_eq_mixedTuple, Function.comp_apply]

/-- A sorted code is the code of a point. -/
theorem exists_point_of_sorted {n r : ℕ} (c : Fin (n + r) → M)
    (hc : c ∈ GammaParameters.sortedUniverse (mixedSort n r)) : ∃ x : Mixed M n r, mixedTuple x = c := by
  have hv (i : Fin n) : iVF (c (Fin.castAdd r i)) := by
    have := hc (Fin.castAdd r i)
    simp only [mixedSort, Fin.append_left] at this
    exact this
  have hr (j : Fin r) : iRV (c (Fin.natAdd n j)) := by
    have := hc (Fin.natAdd n j)
    simp only [mixedSort, Fin.append_right] at this
    exact this
  refine ⟨((fun i => ⟨c (Fin.castAdd r i), hv i⟩), (fun j => ⟨c (Fin.natAdd n j), hr j⟩)), ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mixedTuple, Fin.append_left]
    rfl
  · simp only [mixedTuple, Fin.append_right]
    rfl

theorem sorted_append {n r k s : ℕ} (z : Fin ((n + r) + (k + s)) → M)
    (hz : z ∈ GammaParameters.sortedUniverse (Fin.append (mixedSort n r) (mixedSort k s))) :
    ∃ x : Mixed M n r, ∃ y : Mixed M k s, Fin.append (mixedTuple x) (mixedTuple y) = z := by
  obtain ⟨x, hx⟩ := exists_point_of_sorted (fun i => z (Fin.castAdd (k + s) i)) (fun i => by
    have := hz (Fin.castAdd (k + s) i)
    simpa only [Fin.append_left] using this)
  obtain ⟨y, hy⟩ := exists_point_of_sorted (fun j => z (Fin.natAdd (n + r) j)) (fun j => by
    have := hz (Fin.natAdd (n + r) j)
    simpa only [Fin.append_right] using this)
  refine ⟨x, y, ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, hx]
  · rw [Fin.append_right, hy]

/-- `MixedMapDefinable` from a definable raw relation on the codes of pairs. -/
theorem mixedMapDefinable_of_raw (hc : CanonicalStructure.IsCanonical (M := M)) {n r k s : ℕ}
    (A : Set (Mixed M n r)) (f : Mixed M n r → Mixed M k s)
    (R : Set ((Fin n ⊕ Fin r) ⊕ (Fin k ⊕ Fin s) → M)) (hR : S.Definable LRV R)
    (hRiff : ∀ x y, Sum.elim (mixedValues x) (mixedValues y) ∈ R ↔ x ∈ A ∧ y = f x) :
    MixedMapDefinable (⟨S, ∅⟩ : ParameterBase M) A f := by
  unfold MixedMapDefinable
  apply (GammaParameters.base_empty_iff S _ _).mpr
  apply (definableOver_iff_normalized_raw S _ _).mpr
  refine ⟨?_, ?_⟩
  · rw [canonical_normalize_eq hc]
    let ψ (z : Fin ((n + r) + (k + s)) → M) : (Fin n ⊕ Fin r) ⊕ (Fin k ⊕ Fin s) → M :=
      Sum.elim (blk₁ z) (blk₂ z)
    have hψ : S.DefinableMap LRV ψ := by
      rintro (i | i) <;> exact Set.DefinableFun.proj LRV
    convert (sorted_definable hc S (Fin.append (mixedSort n r) (mixedSort k s))).inter
      (hR.preimage_map hψ) using 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left, Fin.append_left]; exact mixedTuple_sorted x j
        · rw [Fin.append_right, Fin.append_right]; exact mixedTuple_sorted (f x) j
      · change Sum.elim (blk₁ _) (blk₂ _) ∈ R
        rw [blk₁_append, blk₂_append]
        exact (hRiff x (f x)).mpr ⟨hx, rfl⟩
    · rintro ⟨hz, hR'⟩
      obtain ⟨x, y, rfl⟩ := sorted_append z hz
      change Sum.elim (blk₁ _) (blk₂ _) ∈ R at hR'
      rw [blk₁_append, blk₂_append] at hR'
      obtain ⟨hx, rfl⟩ := (hRiff x y).mp hR'
      exact ⟨x, hx, rfl⟩
  · rintro z ⟨x, -, rfl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left]; exact mixedTuple_sorted x j
    · rw [Fin.append_right, Fin.append_right]; exact mixedTuple_sorted (f x) j

/-- The image of a mixed set under a map with a definable raw relation is definable. -/
theorem image_definable_of_raw (hc : CanonicalStructure.IsCanonical (M := M)) {n r k s : ℕ}
    (A : Set (Mixed M n r)) (f : Mixed M n r → Mixed M k s)
    (R : Set ((Fin n ⊕ Fin r) ⊕ (Fin k ⊕ Fin s) → M)) (hR : S.Definable LRV R)
    (hRiff : ∀ x y, Sum.elim (mixedValues x) (mixedValues y) ∈ R ↔ x ∈ A ∧ y = f x) :
    (rawMixedSpace (M := M) k s).Definable S (f '' A) := by
  change S.Definable LRV ((rawMixedSpace (M := M) k s).preimage (f '' A))
  have hdom₁ := (rawMixedSpace (M := M) n r).domain_definable.mono (Set.empty_subset S)
  have hdom₂ := (rawMixedSpace (M := M) k s).domain_definable.mono (Set.empty_subset S)
  let X : Set ((Fin k ⊕ Fin s) ⊕ (Fin n ⊕ Fin r) → M) :=
    {w | w ∘ Sum.inr ∈ (rawMixedSpace (M := M) n r).domain ∧ Sum.elim (w ∘ Sum.inr) (w ∘ Sum.inl) ∈ R}
  have hX : S.Definable LRV X := by
    refine (hdom₁.preimage_comp Sum.inr).inter ?_
    have h := hR.preimage_comp (Sum.elim Sum.inr Sum.inl : (Fin n ⊕ Fin r) ⊕ (Fin k ⊕ Fin s) → _)
    simp only [Sum.comp_elim] at h
    exact h
  have hEx := definable_of_overBase hc (FullBaseAtomicity.OverBase.exists_block (overBase_of_definable hc hX))
  convert hdom₂.inter hEx using 1
  rw [preimage_eq_image]
  ext c
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨mixedValues_mem_domain _, mixedValues x, mixedValues_mem_domain x, ?_⟩
    exact (hRiff x (f x)).mpr ⟨hx, rfl⟩
  · rintro ⟨hc', d, hd, hR'⟩
    change Sum.elim d c ∈ R at hR'
    obtain ⟨y, rfl⟩ : ∃ y, mixedValues y = c := ⟨_, mixedValues_decode ⟨c, hc'⟩⟩
    obtain ⟨x, rfl⟩ : ∃ x, mixedValues x = d := ⟨_, mixedValues_decode ⟨d, hd⟩⟩
    obtain ⟨hx, rfl⟩ := (hRiff x y).mp hR'
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

section Pieces
variable {a : ℕ}

/-- The value of `ε` at a point of `B`, extended by `0`. -/
def εfun (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (q : Mixed M 1 a) : VF M :=
  if h : q ∈ B.carrier then (ε ⟨q, h⟩).val 0 else 0

theorem εfun_of_mem (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (q : B) : εfun B ε q.val = (ε q).val 0 := by
  rw [εfun, dif_pos q.property]

/-- The injective map off the locus. -/
def d2dMap {B : DefSet (rawMixedSpace (M := M) 1 a) S} {ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    (C : Codes B ε) (q : Mixed M 1 a) : Mixed M 1 (a + C.d₁) :=
  ((fun _ => εfun B ε q), Fin.append q.2 (C.c₁ q))

theorem fin_append_split {d : ℕ} (v : Fin (a + d) → RVInfinity M) :
    Fin.append (fun i => v (Fin.castAdd d i)) (fun j => v (Fin.natAdd a j)) = v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
  · rw [Fin.append_right]

theorem exists_d2d_pieces (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (C : Codes B ε) :
    ∃ k : ℕ, ∃ P : Fin k → DefSet (rawMixedSpace (M := M) 1 a) S,
      (∀ q, q ∈ B.carrier → q ∉ C.L.carrier → ∃ i, q ∈ (P i).carrier) ∧
      (∀ i q, q ∈ (P i).carrier → q ∈ B.carrier ∧ q ∉ C.L.carrier) ∧
      ∀ i (w : Fin a → RVInfinity M) (u : Fin C.d₁ → RVInfinity M) (E : Set (VF M)), IsOpenDiscVF E →
        (∀ x ∈ E, mkPoint x w ∈ (P i).carrier ∧ C.c₁ (mkPoint x w) = u) →
        IsOpenDiscVF ((fun x => εfun B ε (mkPoint x w)) '' E) := by
  let A' : Set (Mixed M 1 a) := B.carrier \ C.L.carrier
  have hA' : MixedDefinable (⟨S, ∅⟩ : ParameterBase M) A' :=
    (mixedDefinable_iff hc A').mpr (B.sdiff C.L).definable
  -- the raw relation of the map
  let R : Set ((Fin 1 ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin (a + C.d₁)) → M) :=
    {Z | Sum.elim (fun _ : Fin 1 => Z (.inl (.inl 0))) (fun j => Z (.inr (.inr j))) ∈ mixedValues '' C.rel₁.carrier ∧
      Sum.elim (Z ∘ Sum.inl) (fun _ : Fin 1 => Z (.inr (.inl 0))) ∈ rawGraph B ε ∧
      ∀ i : Fin a, Z (.inr (.inr (Fin.castAdd C.d₁ i))) = Z (.inl (.inr i))}
  have hR : S.Definable LRV R := by
    have h1 : S.Definable LRV (mixedValues '' C.rel₁.carrier) := by
      rw [← preimage_eq_image]; exact C.rel₁.definable
    have h1' := h1.preimage_comp
      (Sum.elim (fun _ : Fin 1 => (Sum.inl (Sum.inl 0) : (Fin 1 ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin (a + C.d₁))))
        (fun j => Sum.inr (Sum.inr j)))
    have h2 := (rawGraph_definable B ε).preimage_comp
      (Sum.elim Sum.inl (fun _ : Fin 1 => (Sum.inr (Sum.inl 0) : (Fin 1 ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin (a + C.d₁)))))
    have h3 : S.Definable LRV {Z : (Fin 1 ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin (a + C.d₁)) → M |
        ∀ i : Fin a, Z (.inr (.inr (Fin.castAdd C.d₁ i))) = Z (.inl (.inr i))} := by
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite fun i =>
        (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
    simp only [Sum.comp_elim] at h1' h2
    exact h1'.inter (h2.inter h3)
  have hRiff : ∀ x y, Sum.elim (mixedValues x) (mixedValues y) ∈ R ↔ x ∈ A' ∧ y = d2dMap C x := by
    intro x y
    have e1 : (Sum.elim (fun _ : Fin 1 => (Sum.elim (mixedValues x) (mixedValues y) : _ → M) (.inl (.inl 0)))
        (fun j => (Sum.elim (mixedValues x) (mixedValues y) : _ → M) (.inr (.inr j))) : Fin 1 ⊕ Fin (a + C.d₁) → M) =
        mixedValues ((x.1, y.2) : Mixed M 1 (a + C.d₁)) := by
      funext i
      rcases i with i | i
      · have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
      · rfl
    have e2 : (Sum.elim ((Sum.elim (mixedValues x) (mixedValues y) : _ → M) ∘ Sum.inl)
        (fun _ : Fin 1 => (Sum.elim (mixedValues x) (mixedValues y) : _ → M) (.inr (.inl 0))) :
          (Fin 1 ⊕ Fin a) ⊕ Fin 1 → M) = Sum.elim (mixedValues x) (vfValues y.1) := by
      funext i
      rcases i with i | i
      · rfl
      · have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
    change (_ ∈ mixedValues '' C.rel₁.carrier ∧ _ ∈ rawGraph B ε ∧ ∀ i : Fin a,
      (mixedValues y) (.inr (Fin.castAdd C.d₁ i)) = (mixedValues x) (.inr i)) ↔ _
    rw [e1, e2, mixedValues_injective.mem_set_image, mem_rawGraph_iff]
    have hsplit := fin_append_split y.2
    constructor
    · rintro ⟨h1, ⟨q, hq⟩, h3⟩
      have hq1 : mixedValues q.val = mixedValues x := congrArg (fun g => g ∘ Sum.inl) hq
      have hq2 : vfValues (ε q).val = vfValues y.1 := congrArg (fun g => g ∘ Sum.inr) hq
      have hqx : q.val = x := mixedValues_injective hq1
      have hw : (fun i => y.2 (Fin.castAdd C.d₁ i)) = x.2 := funext fun i => Subtype.ext (h3 i)
      rw [← hsplit, hw] at h1
      have h1' := (C.rel₁_iff x.1 x.2 (fun j => y.2 (Fin.natAdd a j))).mp h1
      have hxB : x ∈ B.carrier := h1'.1
      refine ⟨⟨hxB, h1'.2.1⟩, ?_⟩
      refine Prod.ext ?_ ?_
      · funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        change y.1 0 = εfun B ε x
        rw [εfun, dif_pos hxB]
        have hq' : q = ⟨x, hxB⟩ := Subtype.ext hqx
        rw [hq'] at hq2
        exact (congrFun (vfValues_injective hq2) 0).symm
      · change y.2 = Fin.append x.2 (C.c₁ x)
        rw [← hsplit, hw]
        congr 1
        exact h1'.2.2
    · rintro ⟨hx, rfl⟩
      refine ⟨?_, ⟨⟨x, hx.1⟩, ?_⟩, ?_⟩
      · exact (C.rel₁_iff x.1 x.2 (C.c₁ x)).mpr ⟨hx.1, hx.2, rfl⟩
      · funext i
        rcases i with i | i
        · rfl
        · have hi : i = 0 := Subsingleton.elim _ _
          subst hi
          change ((ε ⟨x, hx.1⟩).val 0).val = (εfun B ε x).val
          rw [εfun, dif_pos hx.1]
      · intro i
        change (Fin.append x.2 (C.c₁ x) (Fin.castAdd C.d₁ i)).val = (x.2 i).val
        rw [Fin.append_left]
  have hf : MixedMapDefinable (⟨S, ∅⟩ : ParameterBase M) A' (d2dMap C) :=
    mixedMapDefinable_of_raw hc A' _ R hR hRiff
  have hB' : MixedDefinable (⟨S, ∅⟩ : ParameterBase M) (d2dMap C '' A') :=
    (mixedDefinable_iff hc _).mpr (image_definable_of_raw hc A' _ R hR hRiff)
  have hinj : Set.InjOn (d2dMap C) A' := by
    intro q hq q' hq' he
    have hlab : q.2 = q'.2 := funext fun i => by
      have := congrFun (congrArg Prod.snd he) (Fin.castAdd C.d₁ i)
      simpa only [d2dMap, Fin.append_left] using this
    have hcode : C.c₁ q = C.c₁ q' := funext fun j => by
      have := congrFun (congrArg Prod.snd he) (Fin.natAdd a j)
      simpa only [d2dMap, Fin.append_right] using this
    have hε : ε ⟨q, hq.1⟩ = ε ⟨q', hq'.1⟩ := by
      have h0 := congrFun (congrArg Prod.fst he) 0
      change εfun B ε q = εfun B ε q' at h0
      rw [εfun, dif_pos hq.1, εfun, dif_pos hq'.1] at h0
      apply Subtype.ext
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact h0
    have := C.inj ⟨q, hq.1⟩ ⟨q', hq'.1⟩ hq.2 hq'.2 hlab hcode hε
    exact congrArg Subtype.val this
  obtain ⟨k, P, hcov, -, hP⟩ := DiamondIntegral.Section3.integration_lemma_2_32 hκ.le hs h00
    (⟨S, ∅⟩ : ParameterBase M) hΓ A' _ (d2dMap C) hA' hB' hf hinj.bijOn_image
  refine ⟨k, fun i => ⟨P i, (mixedDefinable_iff hc _).mp (hP i).1⟩, ?_, ?_, ?_⟩
  · intro q hqB hqL
    have : q ∈ ⋃ i, P i := by rw [hcov]; exact ⟨hqB, hqL⟩
    exact Set.mem_iUnion.mp this
  · intro i q hq
    have : q ∈ A' := by rw [← hcov]; exact Set.mem_iUnion.mpr ⟨i, hq⟩
    exact this
  · intro i w u E hE hEP
    have hconc := (hP i).2.2.1
    refine hconc w (Fin.append w u) E hE (fun x hx => ⟨(hEP x hx).1, ?_⟩)
    change Fin.append w (C.c₁ (mkPoint x w)) = Fin.append w u
    rw [(hEP x hx).2]

end Pieces

end DiamondIntegral.Section7.Lemma720
