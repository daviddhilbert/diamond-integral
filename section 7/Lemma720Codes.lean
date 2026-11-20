import «section 7».Lemma720Raw

/-! Lemma 7.20, step 5: constant-or-injective RV codes for a positioning map.

For a definable set `B ⊆ VF × RVᵃ` and a definable map `ε : B → VF`, the upstream
uniform constant-or-injective refinement (`FamilyPositionRefinement.constant_or_injective`,
a scalar-family result over a full base; no Hrushovski–Kazhdan input) gives:

* a definable subset `L ⊆ B` (the locally constant locus);
* RV codes `c₀` on `L` such that `ε` is constant on points of `L` with the same labels and
  the same code (`Codes.const`);
* RV codes `c₁` off `L` such that `ε` is injective on points off `L` with the same labels
  and the same code (`Codes.inj`);
* the graphs of the codes as definable unary relations (`rel₀`, `rel₁`), used for
  obstacles. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}

theorem exists_gamma_gt_one (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ∃ δ : Values.Gamma (M := M), 1 < δ := by
  obtain ⟨γ, δ, -, -, hne⟩ := hΓ
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨δ / γ, one_lt_div'.mpr h⟩
  · exact ⟨γ / δ, one_lt_div'.mpr h⟩

/-- The point of `B` over a raw label tuple and a raw VF element. -/
def mkPoint (x : VF M) (w : Fin a → RVInfinity M) : Mixed M 1 a := ((fun _ => x), w)

/-- The data of the constant-or-injective refinement of `ε` on `B`. -/
structure Codes (B : DefSet (rawMixedSpace (M := M) 1 a) S)
    (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) where
  d₀ : ℕ
  d₁ : ℕ
  L : DefSet (rawMixedSpace (M := M) 1 a) S
  L_sub : L.carrier ⊆ B.carrier
  c₀ : Mixed M 1 a → Fin d₀ → RVInfinity M
  c₁ : Mixed M 1 a → Fin d₁ → RVInfinity M
  rel₀ : DefSet (rawMixedSpace (M := M) 1 (a + d₀)) S
  rel₀_iff : ∀ (x : Fin 1 → VF M) (w : Fin a → RVInfinity M) (u : Fin d₀ → RVInfinity M),
    (x, Fin.append w u) ∈ rel₀.carrier ↔ (x, w) ∈ L.carrier ∧ u = c₀ (x, w)
  rel₁ : DefSet (rawMixedSpace (M := M) 1 (a + d₁)) S
  rel₁_iff : ∀ (x : Fin 1 → VF M) (w : Fin a → RVInfinity M) (u : Fin d₁ → RVInfinity M),
    (x, Fin.append w u) ∈ rel₁.carrier ↔ (x, w) ∈ B.carrier ∧ (x, w) ∉ L.carrier ∧ u = c₁ (x, w)
  const : ∀ q q' : B, q.val ∈ L.carrier → q'.val ∈ L.carrier → q.val.2 = q'.val.2 →
    c₀ q.val = c₀ q'.val → ε q = ε q'
  inj : ∀ q q' : B, q.val ∉ L.carrier → q'.val ∉ L.carrier → q.val.2 = q'.val.2 →
    c₁ q.val = c₁ q'.val → ε q = ε q' → q = q'


/-- A mixed set is definable when its points are cut out by a definable condition on
their raw codes. -/
theorem mixed_definable_of_codes {m : ℕ} (X : Set (Mixed M 1 m)) (R : Set (Fin 1 ⊕ Fin m → M))
    (hR : S.Definable LRV R) (hX : ∀ q, q ∈ X ↔ mixedValues q ∈ R) :
    (rawMixedSpace (M := M) 1 m).Definable S X := by
  change S.Definable LRV ((rawMixedSpace (M := M) 1 m).preimage X)
  convert ((rawMixedSpace (M := M) 1 m).domain_definable.mono (Set.empty_subset S)).inter hR using 1
  ext z
  constructor
  · rintro ⟨hz, hzX⟩
    refine ⟨hz, ?_⟩
    have h := (hX _).mp hzX
    rwa [mixedValues_decode] at h
  · rintro ⟨hz, hzR⟩
    refine ⟨hz, (hX _).mpr ?_⟩
    rwa [mixedValues_decode]

section Exists
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
  (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))

/-- The default RV value used outside the domains of the codes. -/
def rvCodeOf {d : ℕ} (e : Fin d → M) : Fin d → RVInfinity M :=
  fun i => if h : iRV (e i) then ⟨e i, h⟩ else rvZero M

theorem rvValues_rvCodeOf {d : ℕ} {e : Fin d → M} (he : ∀ i, iRV (e i)) :
    rvValues (rvCodeOf e) = e := by
  funext i
  simp only [rvValues, rvCodeOf, dif_pos (he i)]

include hc h00 hκ hs hsmall hΓ in
theorem exists_codes (B : DefSet (rawMixedSpace (M := M) 1 a) S)
    (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) : Nonempty (Codes B ε) := by
  obtain ⟨δ, hδ⟩ := exists_gamma_gt_one hΓ
  obtain ⟨d₀, e₀, d₁, e₁, h0, hconst, h1, hinj⟩ :=
    FamilyPositionRefinement.constant_or_injective hκ.le hs h00 (fullBase S) hsmall δ hδ
      (rawDom B) (rawDom_vf B) (rawFun B ε) (rawFun_vf B ε) (rawFun_graph B hc ε)
  let Lraw (p : Fin a → M) := LocalConstancySyntax.locus (rawDom B p) (rawFun B ε p)
  have hLsub (p : Fin a → M) : Lraw p ⊆ rawDom B p :=
    LocalConstancySyntax.subset (rawDom B p) (rawFun B ε p)
  have hR0 := definable_of_overBase hc h0.2
  have hR1 := definable_of_overBase hc h1.2
  -- the locus, as a mixed set
  let inL (q : Mixed M 1 a) : Prop := (q.1 0).val ∈ Lraw (rvValues q.2)
  have hLdef : (rawMixedSpace (M := M) 1 a).Definable S {q | inL q} := by
    have hex := definable_of_overBase hc (FullBaseAtomicity.OverBase.exists_block h0.2)
    let ψ (z : Fin 1 ⊕ Fin a → M) : Fin a ⊕ Fin 1 → M := Sum.elim (z ∘ Sum.inr) (fun _ => z (.inl 0))
    have hψ : S.DefinableMap LRV ψ := by
      rintro (i | i) <;> exact Set.DefinableFun.proj LRV
    refine mixed_definable_of_codes _ _ (hex.preimage_map hψ) ?_
    intro q
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro hq
      exact ⟨e₀ (rvValues q.2) (q.1 0).val, hq, rfl⟩
    · rintro ⟨e, he, -⟩
      exact he
  have hLB : ∀ q, inL q → q ∈ B.carrier := by
    intro q hq
    obtain ⟨q', hq'x, hq'p⟩ := hLsub _ hq
    have : q'.val = q := by
      refine Prod.ext ?_ ?_
      · funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact Subtype.ext hq'x
      · exact rvValues_injective hq'p
    rw [← this]
    exact q'.property
  let L : DefSet (rawMixedSpace (M := M) 1 a) S := ⟨{q | inL q}, hLdef⟩
  let c₀ (q : Mixed M 1 a) : Fin d₀ → RVInfinity M := rvCodeOf (e₀ (rvValues q.2) (q.1 0).val)
  let c₁ (q : Mixed M 1 a) : Fin d₁ → RVInfinity M := rvCodeOf (e₁ (rvValues q.2) (q.1 0).val)
  -- raw membership in the domain
  have hDom (q : B) : (q.val.1 0).val ∈ rawDom B (rvValues q.val.2) := ⟨q, rfl, rfl⟩
  have hεeq (q q' : B) (hlab : q.val.2 = q'.val.2)
      (hf : rawFun B ε (rvValues q.val.2) (q.val.1 0).val = rawFun B ε (rvValues q.val.2) (q'.val.1 0).val) :
      ε q = ε q' := by
    rw [rawFun_point] at hf
    rw [hlab, rawFun_point] at hf
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact Subtype.ext hf
  have hc0 (q : Mixed M 1 a) (hq : inL q) : rvValues (c₀ q) = e₀ (rvValues q.2) (q.1 0).val :=
    rvValues_rvCodeOf (fun i => h0.1 _ _ hq i)
  have hc1 (q : Mixed M 1 a) (hq : (q.1 0).val ∈ rawDom B (rvValues q.2) \ Lraw (rvValues q.2)) :
      rvValues (c₁ q) = e₁ (rvValues q.2) (q.1 0).val :=
    rvValues_rvCodeOf (fun i => h1.1 _ _ hq i)
  -- the code relations
  let left {d : ℕ} (q : Mixed M 1 (a + d)) : Mixed M 1 a := (q.1, fun i => q.2 (Fin.castAdd d i))
  let right {d : ℕ} (q : Mixed M 1 (a + d)) : Fin d → RVInfinity M := fun j => q.2 (Fin.natAdd a j)
  have hleft {d : ℕ} (x : Fin 1 → VF M) (w : Fin a → RVInfinity M) (u : Fin d → RVInfinity M) :
      left (x, Fin.append w u) = (x, w) := by
    simp only [left, Fin.append_left]
  have hright {d : ℕ} (x : Fin 1 → VF M) (w : Fin a → RVInfinity M) (u : Fin d → RVInfinity M) :
      right (x, Fin.append w u) = u := by
    funext j
    simp only [right, Fin.append_right]
  let φ {d : ℕ} (z : Fin 1 ⊕ Fin (a + d) → M) : (Fin a ⊕ Fin 1) ⊕ Fin d → M :=
    Sum.elim (Sum.elim (fun i => z (.inr (Fin.castAdd d i))) (fun _ => z (.inl 0)))
      (fun j => z (.inr (Fin.natAdd a j)))
  have hφ {d : ℕ} : S.DefinableMap LRV (φ (d := d)) := by
    rintro ((i | i) | i) <;> exact Set.DefinableFun.proj LRV
  have hz1 {d : ℕ} (q : Mixed M 1 (a + d)) :
      φ (mixedValues q) ∘ Sum.inl ∘ Sum.inl = rvValues (left q).2 := rfl
  have hz2 {d : ℕ} (q : Mixed M 1 (a + d)) :
      φ (mixedValues q) (.inl (.inr 0)) = ((left q).1 0).val := rfl
  have hz3 {d : ℕ} (q : Mixed M 1 (a + d)) :
      φ (mixedValues q) ∘ Sum.inr = rvValues (right q) := rfl
  have hrel0def : (rawMixedSpace (M := M) 1 (a + d₀)).Definable S
      {q | inL (left q) ∧ right q = c₀ (left q)} := by
    refine mixed_definable_of_codes _ _ (hR0.preimage_map hφ) ?_
    intro q
    change (inL (left q) ∧ right q = c₀ (left q)) ↔
      (φ (mixedValues q) (.inl (.inr 0)) ∈ Lraw (φ (mixedValues q) ∘ Sum.inl ∘ Sum.inl) ∧
        φ (mixedValues q) ∘ Sum.inr = e₀ (φ (mixedValues q) ∘ Sum.inl ∘ Sum.inl) (φ (mixedValues q) (.inl (.inr 0))))
    rw [hz1, hz2, hz3]
    constructor
    · rintro ⟨hq, hu⟩
      refine ⟨hq, ?_⟩
      rw [← hc0 _ hq, hu]
    · rintro ⟨hq, hu⟩
      refine ⟨hq, rvValues_injective ?_⟩
      rw [hc0 _ hq]
      exact hu
  have hrel1def : (rawMixedSpace (M := M) 1 (a + d₁)).Definable S
      {q | ((left q).1 0).val ∈ rawDom B (rvValues (left q).2) \ Lraw (rvValues (left q).2) ∧
        right q = c₁ (left q)} := by
    refine mixed_definable_of_codes _ _ (hR1.preimage_map hφ) ?_
    intro q
    change (((left q).1 0).val ∈ rawDom B (rvValues (left q).2) \ Lraw (rvValues (left q).2) ∧
        right q = c₁ (left q)) ↔
      (φ (mixedValues q) (.inl (.inr 0)) ∈ rawDom B (φ (mixedValues q) ∘ Sum.inl ∘ Sum.inl) \
          Lraw (φ (mixedValues q) ∘ Sum.inl ∘ Sum.inl) ∧
        φ (mixedValues q) ∘ Sum.inr = e₁ (φ (mixedValues q) ∘ Sum.inl ∘ Sum.inl) (φ (mixedValues q) (.inl (.inr 0))))
    rw [hz1, hz2, hz3]
    constructor
    · rintro ⟨hq, hu⟩
      refine ⟨hq, ?_⟩
      rw [← hc1 _ hq, hu]
    · rintro ⟨hq, hu⟩
      refine ⟨hq, rvValues_injective ?_⟩
      rw [hc1 _ hq]
      exact hu
  have hdomB (q : Mixed M 1 a) : (q.1 0).val ∈ rawDom B (rvValues q.2) ↔ q ∈ B.carrier := by
    constructor
    · rintro ⟨q', hq'x, hq'p⟩
      have : q'.val = q := by
        refine Prod.ext ?_ ?_
        · funext i
          have hi : i = 0 := Subsingleton.elim _ _
          subst hi
          exact Subtype.ext hq'x
        · exact rvValues_injective hq'p
      rw [← this]
      exact q'.property
    · intro hq
      exact ⟨⟨q, hq⟩, rfl, rfl⟩
  refine ⟨{
    d₀ := d₀, d₁ := d₁, L := L, L_sub := fun q hq => hLB q hq, c₀ := c₀, c₁ := c₁
    rel₀ := ⟨_, hrel0def⟩
    rel₀_iff := fun x w u => by
      change inL (left (x, Fin.append w u)) ∧ right (x, Fin.append w u) = c₀ (left (x, Fin.append w u)) ↔ _
      rw [hleft, hright]
      rfl
    rel₁ := ⟨_, hrel1def⟩
    rel₁_iff := fun x w u => by
      change ((left (x, Fin.append w u)).1 0).val ∈ rawDom B (rvValues (left (x, Fin.append w u)).2) \
          Lraw (rvValues (left (x, Fin.append w u)).2) ∧
          right (x, Fin.append w u) = c₁ (left (x, Fin.append w u)) ↔ _
      rw [hleft, hright, Set.mem_diff, hdomB]
      exact and_assoc
    const := fun q q' hq hq' hlab hcode => by
      apply hεeq q q' hlab
      have hq'' : (q'.val.1 0).val ∈ Lraw (rvValues q.val.2) := by rw [hlab]; exact hq'
      apply hconst _ _ hq _ hq''
      have e1 : rvValues (c₀ q.val) = e₀ (rvValues q.val.2) (q.val.1 0).val := hc0 _ hq
      have e2 : rvValues (c₀ q'.val) = e₀ (rvValues q'.val.2) (q'.val.1 0).val := hc0 _ hq'
      rw [← e1, hcode, e2, hlab]
    inj := fun q q' hq hq' hlab hcode hε => by
      have hx : (q.val.1 0).val ∈ rawDom B (rvValues q.val.2) \ Lraw (rvValues q.val.2) := ⟨hDom q, hq⟩
      have hx' : (q'.val.1 0).val ∈ rawDom B (rvValues q'.val.2) \ Lraw (rvValues q'.val.2) := ⟨hDom q', hq'⟩
      have hx'' : (q'.val.1 0).val ∈ rawDom B (rvValues q.val.2) \ Lraw (rvValues q.val.2) := by
        rw [hlab]; exact hx'
      have hf : rawFun B ε (rvValues q.val.2) (q.val.1 0).val =
          rawFun B ε (rvValues q.val.2) (q'.val.1 0).val := by
        rw [rawFun_point]
        conv_rhs => rw [hlab, rawFun_point]
        rw [hε]
      have he : e₁ (rvValues q.val.2) (q.val.1 0).val = e₁ (rvValues q.val.2) (q'.val.1 0).val := by
        have e1 : rvValues (c₁ q.val) = e₁ (rvValues q.val.2) (q.val.1 0).val := hc1 _ hx
        have e2 : rvValues (c₁ q'.val) = e₁ (rvValues q'.val.2) (q'.val.1 0).val := hc1 _ hx'
        rw [← e1, hcode, e2, hlab]
      have hraw := hinj _ _ hx _ hx'' hf he
      exact point_unique B ⟨hraw, rfl⟩ ⟨rfl, congrArg rvValues hlab.symm⟩ |>.symm ▸ rfl }⟩

end Exists

end DiamondIntegral.Section7.Lemma720
