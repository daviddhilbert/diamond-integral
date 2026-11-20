import «section 7».BalancedShearStages
import «section 7».ChainStages
import «section 7».SetBaseMatching
import «section 7».FirstStage

/-! Lemma 6.38 in the balanced case of Lemma 7.21 (referee R132), and the
opposite orientation of a balanced family.

Let `X ⊆ VF² × RV^q` satisfy the input of the balanced translation
(`BalancedShearStages.BalancedShearInput`): its nonempty cells `X_u` are
balanced with positioning function `ε(u, ·)` and paradigms `t₁(u)`, `t(u)`
(Definition 7.17), the graphs of `ε` and `t` are definable, and `X` is proper
invariant, VF-doubly bounded and tagged. Suppose also that the graph of `t₁` is
definable.

* **Transpose.** If `ε` is balanced in `A` with paradigms `t₁`, `t₂`, then
  `ε⁻¹` is balanced in the transpose `Aᵀ` with paradigms `t₂`, `t₁`
  (`balanced_transpose`): the fibre of `Aᵀ` over `y` is `t₁^♯ + ε⁻¹(y)`, and
  `ε(Aᵀ_y) = y - t₂^♯`. The inverse of an `rv`-affine bijection with slope `s`
  is `rv`-affine with slope `s⁻¹`, and the preimage of an open subdisc is the
  intersection of two open discs about a common point, hence an open disc. The
  membership arguments use that an open disc containing `a` and a point at
  distance `ρ` from `a` contains every point at distance `≥ ρ` from `a`.
* **Opposite orientation.** The transposed cells of `X` give the input of the
  translation stage for `X ∘ swap`, with positioning function `ε(u, ·)⁻¹` and
  paradigms `t₁(u)`, `t(u)` (`swapInput`). The genuine shift for the transpose
  follows from taggedness: `ε⁻¹(y)` lies in the first projection of `X_u`, on
  which the leading term is constant.
* **Label families.** `A₁ = {(a, u) : a ∈ first(X_u)}` and
  `A₂ = {(b, u) : b ∈ second(X_u)}` (`firstFamily`, `secondFamily`,
  `mem_firstFamily`, `mem_secondFamily`). The map `(a, u) ↦ (ε(u, a), u)` is a
  proper covariant homeomorphism `A₁ → A₂` (`positionMap`, `positionMap_home`):
  it is bijective since each `ε(u, ·)` is, its graph fibres are label fibres of
  `A₁` and `A₂`, and it is continuous since `ε(u, ·)` is `rv`-affine.
* **Jacobian.** At a generic point the Jacobian `J` of `ε(u, ·)` has leading
  term the slope `s` (difference quotients all have leading term `s`), so
  `vrv(J) = vrv(s) = vrv(t(u)) / vrv(t₁(u))` by Remark 7.18
  (`positionMap_jacobian`).
* **Lemma 6.38.** With the label forms `vrv(t(u))` on `A₁` and `vrv(t₁(u))` on
  `A₂` (the paper's constant forms `0` and `-γ` up to the common shift
  `vrv(t(u))`), Lemma 6.38 over the support data gives the two chains, which are
  contraction stages `S₁`, `S₂` (`ChainStages`), and a bijection `ψ` of their
  contracted sets that keeps the old labels `u` and satisfies
  `vrv(lead ψ(z)) · vrv(t₁(u)) = vrv(lead z) · vrv(t(u))`
  (`exists_balanced_matching`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BalancedMatching
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.TwoCells DiamondIntegral.Section7.TwoCellGeometry
open DiamondIntegral.Section7.BalancedShearStages

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Open discs of `VF` -/

theorem isOpenDiscVF_iff {D : Set (VF M)} :
    IsOpenDiscVF D ↔ ∃ a : VF M, ∃ γ : Gamma M, ∀ x, x ∈ D ↔ γ.val < vfValue (x - a) := by
  constructor
  · rintro ⟨a, γ, h⟩
    refine ⟨a, γ, fun x => ?_⟩
    rw [← openDiscCode_mem_iff_value a x γ, ← h]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => (Subtype.ext hyx : y = x) ▸ hy⟩
  · rintro ⟨a, γ, h⟩
    refine ⟨a, γ, ?_⟩
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (openDiscCode_mem_iff_value a x γ).mpr ((h x).mp hx)
    · intro hz
      have hz' : iVF z := disc_underlying_subset_vf _ hz
      exact ⟨⟨z, hz'⟩, (h _).mpr ((openDiscCode_mem_iff_value a ⟨z, hz'⟩ γ).mp hz), rfl⟩

theorem vfValue_sub_swap (a b : VF M) : vfValue (a - b) = vfValue (b - a) := vfValue_sub_comm a b

/-- Every point of an open disc is a centre. -/
theorem openDisc_recentre {D : Set (VF M)} (hD : IsOpenDiscVF D) {a' : VF M} (ha' : a' ∈ D) :
    ∃ γ : Gamma M, ∀ x, x ∈ D ↔ γ.val < vfValue (x - a') := by
  obtain ⟨a, γ, h⟩ := isOpenDiscVF_iff.mp hD
  have h1 : γ.val < vfValue (a' - a) := (h a').mp ha'
  refine ⟨γ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have h2 := vfValue_min_le_sub (x - a) (a' - a)
    rw [show x - a - (a' - a) = x - a' by abel] at h2
    exact (lt_min ((h x).mp hx) h1).trans_le h2
  · apply (h x).mpr
    have h2 := vfValue_min_le_sub (x - a') (a - a')
    rw [show x - a' - (a - a') = x - a by abel] at h2
    have h1' : γ.val < vfValue (a - a') := by rw [vfValue_sub_swap]; exact h1
    exact (lt_min hx h1').trans_le h2

/-- An open disc containing `a'` and `b` contains every `c` at least as close to
`a'` as `b`. -/
theorem openDisc_mem_of_le {D : Set (VF M)} (hD : IsOpenDiscVF D) {a' b c : VF M} (ha' : a' ∈ D)
    (hb : b ∈ D) (hc : vfValue (b - a') ≤ vfValue (c - a')) : c ∈ D := by
  obtain ⟨γ, h⟩ := openDisc_recentre hD ha'
  exact (h c).mpr (((h b).mp hb).trans_le hc)

theorem vfValue_sharp {t : RVInfinity M} {s s' : VF M} (hs : s ∈ sharpSet t) (hs' : s' ∈ sharpSet t) :
    vfValue s = vfValue s' := by
  rw [vfValue_of_rv_eq hs, vfValue_of_rv_eq hs']

theorem vfValue_neg_eq (x : VF M) : vfValue (-x) = vfValue x := vfValue_neg x

theorem rvZero_eq_zero : rvZero M = (0 : RVInfinity M) := Subtype.ext RVOperations.zero_val.symm

theorem slope_value {D : Set (VF M)} {f : VF M → VF M} {s : RV M} (hs : HasSlope D f s)
    {a a' : VF M} (ha : a ∈ D) (ha' : a' ∈ D) :
    vfValue (f a - f a') = (rvRadius s).val * vfValue (a - a') := by
  rw [vfValue_of_rv_eq (hs a ha a' ha'), RVOperations.vrv_mul]
  rfl

theorem gammaTop_lt_mul_iff {σ : Gamma M} {ρ : Gamma M} {w : GammaInfinity M} :
    ρ.val < σ.val * w ↔ (ρ * σ⁻¹).val < w := by
  have hσ : σ.val ≠ 0 := fun h => σ.property (h.trans Values.infinity_eq_zero.symm)
  have hσi : σ.val⁻¹ ≠ 0 := inv_ne_zero hσ
  change ρ.val < σ.val * w ↔ ρ.val * σ.val⁻¹ < w
  constructor
  · intro h
    have h2 := gammaTop_mul_lt_mul hσi h
    rwa [← mul_assoc, inv_mul_cancel₀ hσ, one_mul, mul_comm] at h2
  · intro h
    have h2 := gammaTop_mul_lt_mul hσ h
    rwa [mul_comm ρ.val, ← mul_assoc, mul_inv_cancel₀ hσ, one_mul] at h2

/-! ### The transpose of a balanced cell -/

section Transpose

variable {A : Set (VF M × VF M)} {ε : VF M → VF M} {t₁ t₂ : RVInfinity M}

omit [M ⊨ Axioms.ACVF] in
theorem mem_swap_iff {x y : VF M} : (y, x) ∈ Prod.swap '' A ↔ (x, y) ∈ A := by
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hab
  · intro h
    exact ⟨(x, y), h, rfl⟩

omit [M ⊨ Axioms.ACVF] in
theorem first_swap (A : Set (VF M × VF M)) : first (Prod.swap '' A) = second A := by
  ext y
  constructor
  · rintro ⟨⟨y', x⟩, hp, rfl⟩
    exact ⟨(x, y'), mem_swap_iff.mp hp, rfl⟩
  · rintro ⟨⟨x, y'⟩, hp, rfl⟩
    exact ⟨(y', x), mem_swap_iff.mpr hp, rfl⟩

omit [M ⊨ Axioms.ACVF] in
theorem second_swap (A : Set (VF M × VF M)) : second (Prod.swap '' A) = first A := by
  ext x
  constructor
  · rintro ⟨⟨y, x'⟩, hp, rfl⟩
    exact ⟨(x', y), mem_swap_iff.mp hp, rfl⟩
  · rintro ⟨⟨x', y⟩, hp, rfl⟩
    exact ⟨(y, x'), mem_swap_iff.mpr hp, rfl⟩

theorem positionInv_bijOn (h : Balanced A ε t₁ t₂) :
    Set.BijOn (positionInv A ε) (second A) (first A) :=
  h.bijective.symm h.bijective.invOn_invFunOn.symm

theorem positionInv_position (h : Balanced A ε t₁ t₂) {x : VF M} (hx : x ∈ first A) :
    positionInv A ε (ε x) = x :=
  h.bijective.invOn_invFunOn.1 hx

/-- **The transpose of a balanced cell.** If `ε` is balanced in `A` with
paradigms `t₁`, `t₂`, then `ε⁻¹` is balanced in the transpose `Aᵀ` with paradigms
`t₂`, `t₁`: the fibre of `Aᵀ` over `y` is `t₁^♯ + ε⁻¹(y)`, and
`ε(Aᵀ_y) = y - t₂^♯`. -/
theorem balanced_transpose (h : Balanced A ε t₁ t₂) :
    Balanced (Prod.swap '' A) (positionInv A ε) t₂ t₁ := by
  obtain ⟨hA₁, _, s, hs⟩ := h.rvAffine
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [first_swap]; exact h.second_disc
  · rw [second_swap]; exact h.first_disc
  · rw [first_swap, second_swap]; exact positionInv_bijOn h
  · -- disc-to-disc
    rw [first_swap]
    intro E hEA hE
    obtain ⟨c, ρ, hc⟩ := isOpenDiscVF_iff.mp hE
    have hcE : c ∈ E := (hc c).mpr (by rw [sub_self]; exact gamma_lt_value_zero ρ)
    have hcA : c ∈ second A := hEA hcE
    let a := positionInv A ε c
    have ha : a ∈ first A := positionInv_mem h hcA
    have hεa : ε a = c := position_positionInv h hcA
    obtain ⟨γ₁, hγ₁⟩ := openDisc_recentre hA₁ ha
    let σ := rvRadius s
    let δ := ρ * σ⁻¹
    have himage : ∀ x, x ∈ positionInv A ε '' E ↔ γ₁.val < vfValue (x - a) ∧ δ.val < vfValue (x - a) := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyA := hEA hy
        have hx := positionInv_mem h hyA
        refine ⟨(hγ₁ _).mp hx, ?_⟩
        apply gammaTop_lt_mul_iff.mp
        rw [← slope_value hs hx ha, position_positionInv h hyA, hεa]
        exact (hc y).mp hy
      · rintro ⟨h1, h2⟩
        have hx : x ∈ first A := (hγ₁ x).mpr h1
        refine ⟨ε x, (hc _).mpr ?_, positionInv_position h hx⟩
        rw [← hεa, slope_value hs hx ha]
        exact gammaTop_lt_mul_iff.mpr h2
    apply isOpenDiscVF_iff.mpr
    rcases le_total γ₁ δ with hle | hle
    · refine ⟨a, δ, fun x => (himage x).trans ⟨fun h' => h'.2, fun h' => ⟨?_, h'⟩⟩⟩
      exact (show γ₁.val ≤ δ.val from hle).trans_lt h'
    · refine ⟨a, γ₁, fun x => (himage x).trans ⟨fun h' => h'.1, fun h' => ⟨h', ?_⟩⟩⟩
      exact (show δ.val ≤ γ₁.val from hle).trans_lt h'
  · -- rv-affine
    rw [first_swap]
    have hs0 : s.val ≠ 0 := fun he => s.property (he.trans rvZero_eq_zero.symm)
    refine ⟨h.second_disc, (positionInv_bijOn h).injOn,
      ⟨s.val⁻¹, fun he => inv_ne_zero hs0 (he.trans rvZero_eq_zero)⟩, ?_⟩
    intro y hy y' hy'
    have hx := positionInv_mem h hy
    have hx' := positionInv_mem h hy'
    have hsl := hs _ hx _ hx'
    rw [position_positionInv h hy, position_positionInv h hy'] at hsl
    change rv M (positionInv A ε y - positionInv A ε y') = s.val⁻¹ * rv M (y - y')
    rw [hsl, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  · -- fibres of the transpose
    intro y hy
    rw [first_swap] at hy
    have hfib : ∀ x, x ∈ fibre (Prod.swap '' A) y ↔ (x, y) ∈ A := fun x => mem_swap_iff
    ext x
    rw [hfib, balanced_mem_left h x y hy]
    have ha' := positionInv_mem h hy
    constructor
    · rintro ⟨_, hxs⟩
      exact ⟨x - positionInv A ε y, hxs, sub_add_cancel _ _⟩
    · rintro ⟨s₁, hs₁, rfl⟩
      refine ⟨?_, by rw [add_sub_cancel_right]; exact hs₁⟩
      obtain ⟨s₀, hs₀⟩ := rv_surjective t₁
      have hb : positionInv A ε y - s₀ ∈ first A := by
        have hmem : positionInv A ε y - s₀ ∈ (positionInv A ε y - ·) '' sharpSet t₁ := ⟨s₀, hs₀, rfl⟩
        rw [← h.preimage_eq _ ha'] at hmem
        exact hmem.2
      apply openDisc_mem_of_le hA₁ ha' hb
      rw [show positionInv A ε y - s₀ - positionInv A ε y = -s₀ by abel, add_sub_cancel_right,
        vfValue_neg_eq]
      exact (vfValue_sharp hs₀ hs₁).le
  · -- the preimages of the transposed fibres
    intro y hy
    rw [first_swap] at hy ⊢
    ext b
    constructor
    · rintro ⟨hbfib, hbA⟩
      have hb' : (positionInv A ε b, y) ∈ A := mem_swap_iff.mp hbfib
      have h2 := ((balanced_mem_right h _ y).mp hb').2
      rw [position_positionInv h hbA] at h2
      exact ⟨y - b, h2, sub_sub_cancel y b⟩
    · rintro ⟨s₂, hs₂, rfl⟩
      have ha := positionInv_mem h hy
      have hyA : y ∈ second A := hy
      obtain ⟨s₀, hs₀⟩ := rv_surjective t₂
      have hfibmem : s₀ + y ∈ second A := by
        have hmem : s₀ + ε (positionInv A ε y) ∈ fibre A (positionInv A ε y) := by
          rw [h.fibre_eq _ ha]
          exact ⟨s₀, hs₀, rfl⟩
        rw [position_positionInv h hy] at hmem
        exact mem_second_of_fibre hmem
      have hbA : y - s₂ ∈ second A := by
        apply openDisc_mem_of_le h.second_disc hyA hfibmem
        rw [add_sub_cancel_right, show y - s₂ - y = -s₂ by abel, vfValue_neg_eq]
        exact (vfValue_sharp hs₀ hs₂).le
      refine ⟨?_, hbA⟩
      change (positionInv A ε (y - s₂)) ∈ fibre (Prod.swap '' A) y
      apply mem_swap_iff.mpr
      apply (balanced_mem_right h _ y).mpr
      refine ⟨positionInv_mem h hbA, ?_⟩
      rw [position_positionInv h hbA, sub_sub_cancel]
      exact hs₂

end Transpose

/-! ### The opposite orientation of a balanced family -/

section Swap

variable {S : Set M} {q : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

theorem rv_one_ne_zero : rv M 1 ≠ rvZero M := fun h => one_ne_zero ((rv_eq_zero_iff (1 : VF M)).mp h)

/-- The second paradigm as a nonzero RV element (`rv(1)` where `t₁` vanishes). -/
def secondParadigm (t₁ : (Fin q → RVInfinity M) → RVInfinity M) (u : Fin q → RVInfinity M) : RV M :=
  if h : t₁ u ≠ rvZero M then ⟨t₁ u, h⟩ else ⟨rv M 1, rv_one_ne_zero⟩

omit [M ⊨ Axioms.ACVF] in
theorem nonempty_cell_of_mem {u : Fin q → RVInfinity M} {x y : VF M} (h : (![x, y], u) ∈ X.carrier) :
    (cell X u).Nonempty := ⟨(x, y), h⟩

/-- On a nonempty cell the second paradigm is nonzero (Remark 7.18). -/
theorem secondParadigm_val (H : BalancedShearInput X ε t t₁) {u : Fin q → RVInfinity M}
    (hne : (cell X u).Nonempty) : (secondParadigm t₁ u).val = t₁ u := by
  have hb := H.balanced u hne
  have hfirst : (first (cell X u)).Nonempty := hne.image Prod.fst
  have h0 : t₁ u ≠ rvZero M := fun h => (t u).property ((paradigm_zero_iff hb hfirst).mp h)
  simp [secondParadigm, h0]

/-- The positioning function of the transposed cells: `ε(u, ·)⁻¹`. -/
def swapFocus (X : DefSet (rawMixedSpace (M := M) 2 q) S) (ε : (Fin q → RVInfinity M) → VF M → VF M)
    (u : Fin q → RVInfinity M) (y : VF M) : VF M :=
  positionInv (cell X u) (ε u) y

omit [M ⊨ Axioms.ACVF] in
theorem swapCell_eq (u : Fin q → RVInfinity M) : swapCell X u = Prod.swap '' cell X u := by
  ext ⟨y, x⟩
  exact (mem_swap_iff (A := cell X u)).symm

/-- The index swap of the first two coordinates of `Fin (2 + q)`. -/
def swapIndex (q : ℕ) : Fin (2 + q) → Fin (2 + q) :=
  Fin.append ![Fin.castAdd q 1, Fin.castAdd q 0] (Fin.natAdd 2)

omit [LRV.Structure M] [M ⊨ Axioms.ACVF] in
theorem append_comp_swapIndex (a b : M) (w : Fin q → M) :
    Fin.append ![a, b] w ∘ swapIndex q = Fin.append ![b, a] w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [swapIndex, Fin.append_left]
  · simp [swapIndex, Fin.append_right]

omit [LRV.Structure M] [M ⊨ Axioms.ACVF] in
theorem comp_swapIndex_swapIndex (z : Fin (2 + q) → M) : (z ∘ swapIndex q) ∘ swapIndex q = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [swapIndex, Fin.append_left]
  · simp [swapIndex, Fin.append_right]

/-- **The opposite orientation.** The transposed cells are balanced with
positioning function `ε(u, ·)⁻¹` and paradigms `t(u)`, `t₁(u)`
(`Balanced.transpose`); their graphs are definable from those of `ε` and `t₁`,
and the genuine shift follows from taggedness. So the translation stage of
`BalancedShearStages` applies to `X ∘ swap`. -/
theorem swapInput (H : BalancedShearInput X ε t t₁)
    (ht₁ : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(t₁ u).val] (rvValues u)}) :
    BalancedShearInput (reindexedVFSet X (Equiv.swap 0 1)) (swapFocus X ε) (secondParadigm t₁)
      (fun u => (t u).val) := by
  apply BalancedShearInput.ofSwap H.proper H.doublyBounded H.tagged
  · convert H.focusGraph.preimage_comp (swapIndex q) using 1
    ext z
    constructor
    · rintro ⟨u, x, ⟨y, hyx⟩, rfl⟩
      have hb := H.balanced u (nonempty_cell_of_mem hyx)
      have hx : x ∈ second (cell X u) := ⟨(y, x), hyx, rfl⟩
      obtain ⟨⟨a, y'⟩, hay', ha⟩ := positionInv_mem hb hx
      simp only [Set.mem_preimage]
      rw [append_comp_swapIndex]
      refine ⟨u, swapFocus X ε u x, ⟨y', ?_⟩, ?_⟩
      · change a = swapFocus X ε u x at ha
        rw [← ha]
        exact hay'
      · change Fin.append ![(swapFocus X ε u x).val, x.val] (rvValues u) =
          Fin.append ![(swapFocus X ε u x).val, (ε u (positionInv (cell X u) (ε u) x)).val] (rvValues u)
        rw [position_positionInv hb hx]
    · rintro ⟨u, a, ⟨y, hay⟩, he⟩
      have hb := H.balanced u (nonempty_cell_of_mem hay)
      have ha : a ∈ first (cell X u) := ⟨(a, y), hay, rfl⟩
      obtain ⟨⟨x'', b⟩, hxb, hb'⟩ := hb.bijective.mapsTo ha
      change b = ε u a at hb'
      refine ⟨u, ε u a, ⟨x'', ?_⟩, ?_⟩
      · rw [← hb']
        exact hxb
      · have he' : z ∘ swapIndex q = Fin.append ![a.val, (ε u a).val] (rvValues u) := he
        have hz : z = Fin.append ![(ε u a).val, a.val] (rvValues u) := by
          rw [← comp_swapIndex_swapIndex z, he', append_comp_swapIndex]
        have hpos : swapFocus X ε u (ε u a) = a := positionInv_position hb ha
        rw [hz, hpos]
  · convert ht₁ using 1
    ext z
    constructor
    · rintro ⟨u, x, ⟨y, hyx⟩, rfl⟩
      refine ⟨u, y, ⟨x, hyx⟩, ?_⟩
      rw [secondParadigm_val H (nonempty_cell_of_mem hyx)]
    · rintro ⟨u, x, ⟨y, hxy⟩, rfl⟩
      refine ⟨u, y, ⟨x, hxy⟩, ?_⟩
      rw [secondParadigm_val H (nonempty_cell_of_mem hxy)]
  · intro u hne
    rw [swapCell_eq] at hne ⊢
    have hne' : (cell X u).Nonempty := by
      obtain ⟨_, ⟨p, hp, _⟩⟩ := hne
      exact ⟨p, hp⟩
    rw [secondParadigm_val H hne']
    exact balanced_transpose (H.balanced u hne')
  · rintro u ⟨y, x⟩ hp
    change (![x, y], u) ∈ X.carrier at hp
    have hb := H.balanced u (nonempty_cell_of_mem hp)
    have hy : y ∈ second (cell X u) := ⟨(x, y), hp, rfl⟩
    obtain ⟨⟨a, y'⟩, hay', ha⟩ := positionInv_mem hb hy
    change a = swapFocus X ε u y at ha
    have htag := H.tagged (![a, y'], u) hay' (![x, y], u) hp rfl
    have h0 := congrFun htag 0
    change rv M (swapFocus X ε u y) = rv M x
    rw [← ha]
    exact h0

end Swap

/-! ### The label families of first and second projections -/

section Families

variable {S : Set M} {q : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- The family `A₁ = {(a, u) : a ∈ first(X_u)}` of first projections. -/
def firstFamily (X : DefSet (rawMixedSpace (M := M) 2 q) S) : DefSet (rawMixedSpace (M := M) 1 q) S :=
  (vfDropLast X).image

/-- The family `A₂ = {(b, u) : b ∈ second(X_u)}` of second projections. -/
def secondFamily (X : DefSet (rawMixedSpace (M := M) 2 q) S) : DefSet (rawMixedSpace (M := M) 1 q) S :=
  (vfDropLast (reindexedVFSet X (Equiv.swap 0 1))).image

omit [M ⊨ Axioms.ACVF] in
/-- `A₁` is literally the contracted base `vfDropLast X` of the order-`21` translation. -/
theorem firstFamily_eq (X : DefSet (rawMixedSpace (M := M) 2 q) S) :
    firstFamily X = (vfDropLast X).image := rfl

omit [M ⊨ Axioms.ACVF] in
/-- `A₂` is literally the contracted base of the swapped orientation. -/
theorem secondFamily_eq (X : DefSet (rawMixedSpace (M := M) 2 q) S) :
    secondFamily X = (vfDropLast (reindexedVFSet X (Equiv.swap 0 1))).image := rfl

omit [M ⊨ Axioms.ACVF] in
theorem fin_one_fun_eq {α : Type} (a : Fin 1 → α) : (fun _ : Fin 1 => a 0) = a := by
  funext i
  rw [Fin.fin_one_eq_zero i]

omit [M ⊨ Axioms.ACVF] in
theorem mem_firstFamily (a : Fin 1 → VF M) (u : Fin q → RVInfinity M) :
    (a, u) ∈ (firstFamily X).carrier ↔ a 0 ∈ first (cell X u) := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Fin.init p.val.1 = a := congrArg Prod.fst hp
    have h2 : p.val.2 = u := congrArg Prod.snd hp
    have hp' : (p.val.1, u) ∈ X.carrier := h2 ▸ p.property
    rw [← h1]
    exact BalancedShearInput.base_mem_first hp'
  · rintro ⟨⟨x, y⟩, hxy, hx⟩
    refine ⟨⟨(![x, y], u), hxy⟩, ?_⟩
    change (Fin.init ![x, y], u) = (a, u)
    refine Prod.ext ?_ rfl
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact hx

theorem mem_secondFamily (b : Fin 1 → VF M) (u : Fin q → RVInfinity M) :
    (b, u) ∈ (secondFamily X).carrier ↔ b 0 ∈ second (cell X u) := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Fin.init p.val.1 = b := congrArg Prod.fst hp
    have h2 : p.val.2 = u := congrArg Prod.snd hp
    have hp' : (![p.val.1 0, p.val.1 1], u) ∈ (reindexedVFSet X (Equiv.swap 0 1)).carrier := by
      rw [vec_two, ← h2]
      exact p.property
    rw [mem_reindexed_swap] at hp'
    rw [← h1]
    exact ⟨(p.val.1 1, p.val.1 0), hp', rfl⟩
  · rintro ⟨⟨x, y⟩, hxy, hy⟩
    refine ⟨⟨(![y, x], u), (mem_reindexed_swap y x u).mpr hxy⟩, ?_⟩
    change (Fin.init ![y, x], u) = (b, u)
    refine Prod.ext ?_ rfl
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact hy

theorem firstFamily_properInvariant (H : BalancedShearInput X ε t t₁) :
    ProperInvariant S (firstFamily X).carrier :=
  vfDropLast_image_properInvariant H.proper

theorem secondFamily_properInvariant (H : BalancedShearInput X ε t t₁) :
    ProperInvariant S (secondFamily X).carrier :=
  vfDropLast_image_properInvariant (reindexedVFSet_properInvariant X _ H.proper)

omit [M ⊨ Axioms.ACVF] in
theorem cell_nonempty_of_first {u : Fin q → RVInfinity M} {a : VF M} (ha : a ∈ first (cell X u)) :
    (cell X u).Nonempty := by
  obtain ⟨p, hp, _⟩ := ha
  exact ⟨p, hp⟩

theorem focus_mem_second (H : BalancedShearInput X ε t t₁) {u : Fin q → RVInfinity M} {a : VF M}
    (ha : a ∈ first (cell X u)) : ε u a ∈ second (cell X u) :=
  (H.balanced u (cell_nonempty_of_first ha)).bijective.mapsTo ha

/-- **The positioning map of the family**, `(a, u) ↦ (ε(u, a), u)`. -/
def positionMap (H : BalancedShearInput X ε t t₁) : Map (firstFamily X) (secondFamily X) where
  toFun p := ⟨(fun _ => ε p.val.2 (p.val.1 0), p.val.2),
    (mem_secondFamily _ _).mpr (focus_mem_second H ((mem_firstFamily _ _).mp p.property))⟩
  graph_definable := by
    let P := rawMixedSpace (M := M) 1 q
    let ρ : Fin (2 + q) → P.Index ⊕ P.Index :=
      Fin.append ![Sum.inl (Sum.inl (0 : Fin 1)), Sum.inr (Sum.inl (0 : Fin 1))] (fun j => Sum.inl (Sum.inr j))
    have hA : S.Definable LRV (P.preimage (firstFamily X).carrier) := (firstFamily X).definable
    have hL : S.Definable LRV {z : P.Index ⊕ P.Index → M |
        ∀ j : Fin q, z (Sum.inr (Sum.inr j)) = z (Sum.inl (Sum.inr j))} := by
      have h := Set.definable_iInter_of_finite (fun j : Fin q =>
        (Set.DefinableFun.proj LRV (A := S) (i := (Sum.inr (Sum.inr j) : P.Index ⊕ P.Index))).ofPred_eq
          (Set.DefinableFun.proj LRV (i := (Sum.inl (Sum.inr j) : P.Index ⊕ P.Index))))
      convert h using 1
      ext z
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    have h := ((hA.preimage_comp (Sum.inl : P.Index → P.Index ⊕ P.Index)).inter
      (H.focusGraph.preimage_comp ρ)).inter hL
    change S.Definable LRV (P.relation P _)
    convert h using 1
    ext z
    constructor
    · rintro ⟨hx, hy, a, ha, hay⟩
      have hcx : mixedValues (P.decode ⟨z ∘ Sum.inl, hx⟩) = z ∘ Sum.inl := mixedValues_decode ⟨_, hx⟩
      have hcy : mixedValues (P.decode ⟨z ∘ Sum.inr, hy⟩) = z ∘ Sum.inr := mixedValues_decode ⟨_, hy⟩
      have hxA : P.decode ⟨z ∘ Sum.inl, hx⟩ ∈ (firstFamily X).carrier := ha ▸ a.property
      have hay' : ((fun _ : Fin 1 => ε (P.decode ⟨z ∘ Sum.inl, hx⟩).2 ((P.decode ⟨z ∘ Sum.inl, hx⟩).1 0)),
          (P.decode ⟨z ∘ Sum.inl, hx⟩).2) = P.decode ⟨z ∘ Sum.inr, hy⟩ := by
        rw [← ha]
        exact hay
      rw [← hay'] at hcy
      obtain ⟨⟨x₀, y₀⟩, hxy, hx₀⟩ := (mem_firstFamily _ _).mp hxA
      refine ⟨⟨⟨hx, hxA⟩, (P.decode ⟨z ∘ Sum.inl, hx⟩).2, (P.decode ⟨z ∘ Sum.inl, hx⟩).1 0,
        ⟨y₀, ?_⟩, ?_⟩, ?_⟩
      · have hx₀' : x₀ = (P.decode ⟨z ∘ Sum.inl, hx⟩).1 0 := hx₀
        have hxy' : (![x₀, y₀], (P.decode ⟨z ∘ Sum.inl, hx⟩).2) ∈ X.carrier := hxy
        subst hx₀'
        exact hxy'
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · fin_cases j
          · simp only [ρ, Function.comp_apply, Fin.append_left]
            exact (congrFun hcx (Sum.inl 0)).symm
          · simp only [ρ, Function.comp_apply, Fin.append_left]
            exact (congrFun hcy (Sum.inl 0)).symm
        · simp only [ρ, Function.comp_apply, Fin.append_right]
          exact (congrFun hcx (Sum.inr j)).symm
      · intro j
        exact (congrFun hcy (Sum.inr j)).symm.trans (congrFun hcx (Sum.inr j))
    · rintro ⟨⟨⟨hx, hxA⟩, u, a₀, ⟨y₀, _⟩, hz⟩, hlab⟩
      have hcx : mixedValues (P.decode ⟨z ∘ Sum.inl, hx⟩) = z ∘ Sum.inl := mixedValues_decode ⟨_, hx⟩
      have hz0 := congrFun hz (Fin.castAdd q 0)
      have hz1 := congrFun hz (Fin.castAdd q 1)
      simp only [ρ, Function.comp_apply, Fin.append_left, Matrix.cons_val_zero, Matrix.cons_val_one] at hz0 hz1
      have hb0 : (P.decode ⟨z ∘ Sum.inl, hx⟩).1 0 = a₀ :=
        Subtype.ext ((congrFun hcx (Sum.inl 0)).trans hz0)
      have hbu : (P.decode ⟨z ∘ Sum.inl, hx⟩).2 = u := by
        funext j
        apply Subtype.ext
        have hzj := congrFun hz (Fin.natAdd 2 j)
        simp only [ρ, Function.comp_apply, Fin.append_right] at hzj
        exact (congrFun hcx (Sum.inr j)).trans hzj
      have hy : z ∘ Sum.inr ∈ P.domain := by
        refine ⟨⟨fun _ => ε u a₀, ?_⟩, ⟨u, ?_⟩⟩
        · funext i
          rw [Fin.fin_one_eq_zero i]
          exact hz1.symm
        · funext j
          change (u j).val = z (Sum.inr (Sum.inr j))
          rw [hlab j, ← hbu]
          exact congrFun hcx (Sum.inr j)
      have hcy : mixedValues (P.decode ⟨z ∘ Sum.inr, hy⟩) = z ∘ Sum.inr := mixedValues_decode ⟨_, hy⟩
      refine ⟨hx, hy, ⟨P.decode ⟨z ∘ Sum.inl, hx⟩, hxA⟩, rfl, ?_⟩
      apply mixedValues_injective
      rw [hcy]
      funext i
      rcases i with i | j
      · rw [Fin.fin_one_eq_zero i]
        change (ε (P.decode ⟨z ∘ Sum.inl, hx⟩).2 ((P.decode ⟨z ∘ Sum.inl, hx⟩).1 0)).val = z (Sum.inr (Sum.inl (0 : Fin 1)))
        rw [hb0, hbu]
        exact hz1.symm
      · change ((P.decode ⟨z ∘ Sum.inl, hx⟩).2 j).val = z (Sum.inr (Sum.inr j))
        rw [hlab j]
        exact congrFun hcx (Sum.inr j)

theorem positionMap_apply (H : BalancedShearInput X ε t t₁) (p : firstFamily X) :
    (positionMap H p).val = (fun _ => ε p.val.2 (p.val.1 0), p.val.2) := rfl

theorem positionMap_bijective (H : BalancedShearInput X ε t t₁) : Function.Bijective (positionMap H) := by
  constructor
  · intro p p' he
    have hval := congrArg Subtype.val he
    rw [positionMap_apply, positionMap_apply] at hval
    have hu : p.val.2 = p'.val.2 := (Prod.mk.inj hval).2
    have hε : ε p.val.2 (p.val.1 0) = ε p'.val.2 (p'.val.1 0) := congrFun (Prod.mk.inj hval).1 0
    have hp : p.val.1 0 ∈ first (cell X p.val.2) := (mem_firstFamily _ _).mp p.property
    have hp' : p'.val.1 0 ∈ first (cell X p.val.2) := hu ▸ (mem_firstFamily _ _).mp p'.property
    rw [← hu] at hε
    have h0 := (H.balanced p.val.2 (cell_nonempty_of_first hp)).bijective.injOn hp hp' hε
    apply Subtype.ext
    apply Prod.ext _ hu
    rw [← fin_one_fun_eq p.val.1, ← fin_one_fun_eq p'.val.1, h0]
  · rintro ⟨⟨b, u⟩, hb⟩
    have hb0 : b 0 ∈ second (cell X u) := (mem_secondFamily _ _).mp hb
    have hne : (cell X u).Nonempty := by
      obtain ⟨p, hp, _⟩ := hb0
      exact ⟨p, hp⟩
    obtain ⟨a, ha, hab⟩ := (H.balanced u hne).bijective.surjOn hb0
    refine ⟨⟨(fun _ => a, u), (mem_firstFamily _ _).mpr ha⟩, ?_⟩
    apply Subtype.ext
    rw [positionMap_apply]
    change ((fun _ => ε u a), u) = (b, u)
    rw [hab, fin_one_fun_eq b]

end Families

/-! ### The positioning map is a proper covariant homeomorphism -/

section Homeomorphism

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {S : Set M} {q : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

theorem positionMap_graphFibre_iff (H : BalancedShearInput X ε t t₁) (u v : Fin q → RVInfinity M)
    (a b : Fin 1 → VF M) :
    graphFibre (positionMap H) u v a b ↔
      (a, u) ∈ (firstFamily X).carrier ∧ v = u ∧ b = fun _ => ε u (a 0) := by
  constructor
  · rintro ⟨p, he, hfp⟩
    have hfp' : ((fun _ => ε p.val.2 (p.val.1 0)), p.val.2) = (b, v) := hfp
    rw [he] at hfp'
    exact ⟨he ▸ p.property, (Prod.mk.inj hfp').2.symm, (Prod.mk.inj hfp').1.symm⟩
  · rintro ⟨h, hvu, hb⟩
    exact ⟨⟨(a, u), h⟩, rfl, by rw [hvu, hb]; rfl⟩

/-- The positioning map is continuous on each label fibre: `ε(u, ·)` is
`rv`-affine on the first projection of the cell. -/
theorem focus_pair_continuousOn (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (H : BalancedShearInput X ε t t₁) (u : Fin q → RVInfinity M) :
    ContinuousOn (fun a : Fin 1 → VF M => fun _ : Fin 1 => ε u (a 0))
      (vfFibre (firstFamily X).carrier u) := by
  by_cases hne : (vfFibre (firstFamily X).carrier u).Nonempty
  · obtain ⟨a₀, ha₀⟩ := hne
    have hcell : (cell X u).Nonempty := cell_nonempty_of_first ((mem_firstFamily _ _).mp ha₀)
    obtain ⟨_, _, s, hs⟩ := (H.balanced u hcell).rvAffine
    let σ := rvRadius s
    have hσ : σ.val ≠ 0 := fun h => σ.property (h.trans Values.infinity_eq_zero.symm)
    intro a ha
    apply (continuousWithinAt_iff_vfBalls hv _ _ a).mpr
    intro η
    refine ⟨η * σ⁻¹, fun x hx hxa _ => ?_⟩
    have h0 : (η * σ⁻¹).val < vfValue (x 0 - a 0) := hxa 0
    change η.val < vfValue (ε u (x 0) - ε u (a 0))
    rw [slope_value hs ((mem_firstFamily _ _).mp hx) ((mem_firstFamily _ _).mp ha)]
    exact gammaTop_lt_mul_iff.mpr h0
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact continuousOn_empty _

theorem positionMap_source_subset (H : BalancedShearInput X ε t t₁) (u v : Fin q → RVInfinity M) :
    graphFibreSource (positionMap H) u v ⊆ vfFibre (firstFamily X).carrier u := by
  rintro a ⟨b, hab⟩
  exact ((positionMap_graphFibre_iff H u v a b).mp hab).1

theorem positionMap_source_eq (H : BalancedShearInput X ε t t₁) (u : Fin q → RVInfinity M) :
    graphFibreSource (positionMap H) u u = vfFibre (firstFamily X).carrier u := by
  refine Set.Subset.antisymm (positionMap_source_subset H u u) (fun a ha => ?_)
  exact ⟨_, (positionMap_graphFibre_iff H u u a _).mpr ⟨ha, rfl, rfl⟩⟩

theorem positionMap_source_empty (H : BalancedShearInput X ε t t₁) {u v : Fin q → RVInfinity M}
    (huv : v ≠ u) : graphFibreSource (positionMap H) u v = ∅ := by
  ext a
  refine ⟨fun ⟨b, hab⟩ => (huv ((positionMap_graphFibre_iff H u v a b).mp hab).2.1).elim, False.elim⟩

theorem positionMap_range_eq (H : BalancedShearInput X ε t t₁) (u : Fin q → RVInfinity M) :
    graphFibreRange (positionMap H) u u = vfFibre (secondFamily X).carrier u := by
  ext b
  constructor
  · rintro ⟨a, hab⟩
    obtain ⟨ha, -, rfl⟩ := (positionMap_graphFibre_iff H u u a b).mp hab
    exact (mem_secondFamily _ _).mpr (focus_mem_second H ((mem_firstFamily _ _).mp ha))
  · intro hb
    have hb0 : b 0 ∈ second (cell X u) := (mem_secondFamily _ _).mp hb
    obtain ⟨p, hp, _⟩ := hb0
    obtain ⟨a, ha, hab⟩ := (H.balanced u ⟨p, hp⟩).bijective.surjOn ((mem_secondFamily _ _).mp hb)
    refine ⟨fun _ => a, (positionMap_graphFibre_iff H u u _ b).mpr ⟨(mem_firstFamily _ _).mpr ha, rfl, ?_⟩⟩
    change b = fun _ => ε u a
    rw [hab, fin_one_fun_eq b]

theorem positionMap_range_empty (H : BalancedShearInput X ε t t₁) {u v : Fin q → RVInfinity M}
    (huv : v ≠ u) : graphFibreRange (positionMap H) u v = ∅ := by
  ext b
  refine ⟨fun ⟨a, hab⟩ => (huv ((positionMap_graphFibre_iff H u v a b).mp hab).2.1).elim, False.elim⟩

theorem positionMap_continuous (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (H : BalancedShearInput X ε t t₁) : ContinuousOnGraphFibres (positionMap H) := by
  intro u v
  refine ((focus_pair_continuousOn hv H u).mono (positionMap_source_subset H u v)).congr ?_
  intro a ha
  exact ((positionMap_graphFibre_iff H u v a _).mp (graphFibreMap_graph _ u v ha)).2.2

/-- **The positioning map `(a, u) ↦ (ε(u, a), u)` is a proper covariant
homeomorphism** `A₁ → A₂`. -/
theorem positionMap_home (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (H : BalancedShearInput X ε t t₁) : ProperCovariantHomeomorphism (G := G) (positionMap H) := by
  have hcont := positionMap_continuous (G := G) hv H
  refine properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ _
    (properCovariant_of_clopen_ranges h00 hc hκ hs hv _ (firstFamily_properInvariant H)
      (secondFamily_properInvariant H) hcont ?_ ?_) (positionMap_bijective H) hcont
  · intro u v
    by_cases huv : v = u
    · subst huv
      rw [positionMap_source_eq]
      exact ((firstFamily_properInvariant H).clopen_fibres hv v).isOpen
    · rw [positionMap_source_empty H huv]
      exact isOpen_empty
  · intro u v
    by_cases huv : v = u
    · subst huv
      rw [positionMap_range_eq]
      exact (secondFamily_properInvariant H).clopen_fibres hv v
    · rw [positionMap_range_empty H huv]
      exact isClopen_empty

end Homeomorphism

/-! ### Volume forms depending on the labels -/

section Forms

variable {S : Set M} {q : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- The labels of the nonempty cells of `X`. -/
def cellLabels (X : DefSet (rawMixedSpace (M := M) 2 q) S) : Set (Fin q → RVInfinity M) :=
  {u | (cell X u).Nonempty}

/-- The graph of an RV-valued label function, given over the labels of `X`. -/
theorem rvScalarGraph_of_labels (f : (Fin q → RVInfinity M) → RV M)
    (hf : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(f u).val.val] (rvValues u)}) :
    S.Definable LRV (rvScalarFunctionGraph (cellLabels X) f) := by
  let κ : Fin (1 + q) → Fin q ⊕ Fin 1 := Fin.append ![Sum.inr 0] Sum.inl
  convert hf.preimage_comp κ using 1
  ext z
  constructor
  · rintro ⟨u, ⟨⟨x, y⟩, hxy⟩, huz, hfz⟩
    refine ⟨u, x, ⟨y, hxy⟩, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.fin_one_eq_zero j]
      simp only [κ, Function.comp_apply, Fin.append_left, Matrix.cons_val_zero]
      exact hfz.symm
    · simp only [κ, Function.comp_apply, Fin.append_right]
      exact (congrFun huz j).symm
  · rintro ⟨u, x, ⟨y, hxy⟩, he⟩
    have h0 := congrFun he (Fin.castAdd q 0)
    simp only [κ, Function.comp_apply, Fin.append_left, Matrix.cons_val_zero] at h0
    refine ⟨u, ⟨(x, y), hxy⟩, ?_, h0.symm⟩
    funext j
    have hj := congrFun he (Fin.natAdd 1 j)
    simp only [κ, Function.comp_apply, Fin.append_right] at hj
    exact hj.symm

/-- A Gamma form depending only on the labels has a definable graph. -/
theorem mixedGammaGraph_labels_definable {n : ℕ} (A : DefSet (rawMixedSpace (M := M) n q) S)
    (U : Set (Fin q → RVInfinity M)) (hAU : ∀ p ∈ A.carrier, p.2 ∈ U)
    (g : (Fin q → RVInfinity M) → Gamma M) (hg : S.Definable LRV (rvGammaFunctionGraph U g)) :
    S.Definable LRV (mixedGammaGraph A.carrier (fun p => g p.2)) := by
  let τ : Fin q ⊕ Fin 1 → Fin (n + q) ⊕ Fin 1 := Sum.elim (fun j => Sum.inl (Fin.natAdd n j)) Sum.inr
  have h := ((mixed_tuple_image_definable S A.carrier A.definable).preimage_comp
    (Sum.inl : Fin (n + q) → Fin (n + q) ⊕ Fin 1)).inter (hg.preimage_comp τ)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hNZ, x, hx, hxz, hval⟩
    refine ⟨⟨x, hx, hxz⟩, x.2, hAU x hx, ?_, hNZ, hval⟩
    funext j
    have h2 := congrFun hxz (Fin.natAdd n j)
    simp only [mixedTuple, Fin.append_right] at h2
    exact h2
  · rintro ⟨⟨x, hx, hxz⟩, u, _, huz, hNZ, hval⟩
    have hux : u = x.2 := by
      funext j
      apply Subtype.ext
      have h1 := congrFun huz j
      have h2 := congrFun hxz (Fin.natAdd n j)
      simp only [mixedTuple, Fin.append_right] at h2
      exact h1.trans h2.symm
    subst hux
    exact ⟨hNZ, x, hx, hxz, hval⟩

/-- **A label Gamma map**: `p ↦ vrv(f(p.2))` on a family whose labels are cell
labels of `X`, for an RV-valued `f` with definable graph over the labels of `X`. -/
def labelGammaMap {n : ℕ} (A : DefSet (rawMixedSpace (M := M) n q) S)
    (hAX : ∀ p ∈ A.carrier, p.2 ∈ cellLabels X) (f : (Fin q → RVInfinity M) → RV M)
    (hf : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(f u).val.val] (rvValues u)}) : Map A (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  gammaFormMap A (fun p => GammaParameters.codeValue (f p.2).val.val)
    (mixedGammaGraph_labels_definable A (cellLabels X) hAX _
      (rvGammaFunctionGraph_of_rv_definable S _ f (rvScalarGraph_of_labels f hf)))

theorem labelGammaMap_value {n : ℕ} (A : DefSet (rawMixedSpace (M := M) n q) S)
    (hAX : ∀ p ∈ A.carrier, p.2 ∈ cellLabels X) (f : (Fin q → RVInfinity M) → RV M)
    (hf : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(f u).val.val] (rvValues u)}) (p : A) :
    gammaMapValue (labelGammaMap A hAX f hf) p = rvRadius (f p.val.2) :=
  Subtype.ext (nonzero_rv_codeValue_val (f p.val.2).val (f p.val.2).property)

theorem labelGammaMap_extension {n : ℕ} (A : DefSet (rawMixedSpace (M := M) n q) S)
    (hAX : ∀ p ∈ A.carrier, p.2 ∈ cellLabels X) (f : (Fin q → RVInfinity M) → RV M)
    (hf : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(f u).val.val] (rvValues u)}) {p : Mixed M n q} (hp : p ∈ A.carrier) :
    gammaFormExtension (labelGammaMap A hAX f hf) p = rvRadius (f p.2) := by
  rw [gammaFormExtension_at _ ⟨p, hp⟩]
  exact labelGammaMap_value A hAX f hf ⟨p, hp⟩

theorem labelGammaMap_levels_open {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 q) S) (hA : ProperInvariant S A.carrier)
    (hAX : ∀ p ∈ A.carrier, p.2 ∈ cellLabels X) (f : (Fin q → RVInfinity M) → RV M)
    (hf : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(f u).val.val] (rvValues u)}) (u : Fin q → RVInfinity M) (γ : Gamma M) :
    IsOpen {a : Fin 1 → VF M | (a, u) ∈ A.carrier ∧ gammaFormExtension (labelGammaMap A hAX f hf) (a, u) = γ} := by
  by_cases hγ : rvRadius (f u) = γ
  · have he : {a : Fin 1 → VF M | (a, u) ∈ A.carrier ∧
        gammaFormExtension (labelGammaMap A hAX f hf) (a, u) = γ} = vfFibre A.carrier u := by
      ext a
      exact ⟨fun h => h.1, fun h => ⟨h, (labelGammaMap_extension A hAX f hf h).trans hγ⟩⟩
    rw [he]
    exact (hA.clopen_fibres hv u).isOpen
  · have he : {a : Fin 1 → VF M | (a, u) ∈ A.carrier ∧
        gammaFormExtension (labelGammaMap A hAX f hf) (a, u) = γ} = ∅ := by
      ext a
      exact ⟨fun h => hγ ((labelGammaMap_extension A hAX f hf h.1).symm.trans h.2), False.elim⟩
    rw [he]
    exact isOpen_empty

omit [M ⊨ Axioms.ACVF] in
theorem firstFamily_labels : ∀ p ∈ (firstFamily X).carrier, p.2 ∈ cellLabels X :=
  fun p hp => cell_nonempty_of_first ((mem_firstFamily p.1 p.2).mp hp)

theorem secondFamily_labels : ∀ p ∈ (secondFamily X).carrier, p.2 ∈ cellLabels X := by
  intro p hp
  obtain ⟨q', hq', _⟩ := (mem_secondFamily p.1 p.2).mp hp
  exact ⟨q', hq'⟩

/-- The graph of the second paradigm over the labels of `X`. -/
theorem secondParadigm_graph (H : BalancedShearInput X ε t t₁)
    (ht₁ : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(t₁ u).val] (rvValues u)}) :
    S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(secondParadigm t₁ u).val.val] (rvValues u)} := by
  convert ht₁ using 1
  ext z
  constructor
  · rintro ⟨u, x, ⟨y, hxy⟩, rfl⟩
    exact ⟨u, x, ⟨y, hxy⟩, by rw [secondParadigm_val H (nonempty_cell_of_mem hxy)]⟩
  · rintro ⟨u, x, ⟨y, hxy⟩, rfl⟩
    exact ⟨u, x, ⟨y, hxy⟩, by rw [secondParadigm_val H (nonempty_cell_of_mem hxy)]⟩

/-- The form `ω(a, u) = vrv(t(u))` on `A₁`. -/
def sourceGammaForm (H : BalancedShearInput X ε t t₁) :
    Map (firstFamily X) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  labelGammaMap (firstFamily X) firstFamily_labels t H.paradigmGraph

/-- The form `σ(b, u) = vrv(t₁(u))` on `A₂`. -/
def targetGammaForm (H : BalancedShearInput X ε t t₁)
    (ht₁ : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(t₁ u).val] (rvValues u)}) :
    Map (secondFamily X) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  labelGammaMap (secondFamily X) secondFamily_labels (secondParadigm t₁) (secondParadigm_graph H ht₁)

end Forms

/-! ### The Jacobian of the positioning map -/

section Jacobian

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {S : Set M} {q : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- The leading term of the Jacobian of `ε(u, ·)` is its slope. -/
theorem jacobian_rv_eq (H : BalancedShearInput X ε t t₁) (a : firstFamily X) {J : VF M}
    (hJ : HasMixedVFJacobianAt (positionMap H) a J) {s : RV M}
    (hs : HasSlope (first (cell X a.val.2)) (ε a.val.2) s) : rv M J = s.val := by
  obtain ⟨F, hF, A, hpart, hdet⟩ := hJ
  have hJ0 : A 0 0 = J := by rw [← hdet, Matrix.det_fin_one]
  have hp := hpart 0 0
  rw [hJ0] at hp
  have hcenter : F a.val.1 = (positionMap H a).val.1 := hF.center
  obtain ⟨ρ, hρ⟩ := hF
  let σ := rvRadius s
  obtain ⟨δ, hδ⟩ := hp σ
  obtain ⟨γ, hγ⟩ := exists_gt (max δ ρ)
  obtain ⟨r, hr, hval⟩ := SpecialTransformations.Section8.gamma_has_vf_representative γ
  have hrδ : δ.val < Values.vfValueHom r := by
    rw [hval]
    exact (show δ ≤ max δ ρ from le_max_left _ _).trans_lt hγ
  let a₁ : Fin 1 → VF M := a.val.1
  let x : Fin 1 → VF M := a₁ + Pi.single (0 : Fin 1) r
  have hx : x ∈ vfBall a.val.1 ρ := by
    intro i
    rw [Fin.fin_one_eq_zero i]
    change ρ.val < Values.vfValueHom (a.val.1 0 + (Pi.single (0 : Fin 1) r : Fin 1 → VF M) 0 - a.val.1 0)
    rw [Pi.single_eq_same, add_sub_cancel_left, hval]
    exact (show ρ ≤ max δ ρ from le_max_right _ _).trans_lt hγ
  obtain ⟨hxA, hFx⟩ := hρ x hx
  have hFx0 : F x 0 = ε a.val.2 (x 0) := (congrFun (congrArg Prod.fst hFx) 0).symm
  have hFa0 : F a.val.1 0 = ε a.val.2 (a.val.1 0) := congrFun hcenter 0
  have hx0 : x 0 = a.val.1 0 + r := by
    change a.val.1 0 + (Pi.single (0 : Fin 1) r : Fin 1 → VF M) 0 = _
    rw [Pi.single_eq_same]
  have hxf : x 0 ∈ first (cell X a.val.2) := (mem_firstFamily _ _).mp hxA
  have haf : a.val.1 0 ∈ first (cell X a.val.2) := (mem_firstFamily _ _).mp a.property
  have hest := hδ r hr hrδ
  change σ.val * Values.vfValueHom r < Values.vfValueHom (F x 0 - F a.val.1 0 - J * r) at hest
  rw [hFx0, hFa0] at hest
  let D := ε a.val.2 (x 0) - ε a.val.2 (a.val.1 0)
  have hDrv : rv M D = s.val * rv M r := by
    have h := hs _ hxf _ haf
    rw [hx0, add_sub_cancel_left] at h
    exact h
  have hr0 : rv M r ≠ 0 := (RVOperations.rv_ne_zero r).mpr hr
  have hs0 : s.val ≠ 0 := fun he => s.property (he.trans rvZero_eq_zero.symm)
  have hD0 : D ≠ 0 := by
    intro he
    have h := hDrv
    rw [he, rv_zero] at h
    exact mul_ne_zero hs0 hr0 (h.symm.trans rvZero_eq_zero)
  have hDval : vfValue D = σ.val * vfValue r := by
    rw [vfValue_of_rv_eq hDrv, RVOperations.vrv_mul]
    rfl
  have hclose : vfValue D < vfValue (J * r - D) := by
    rw [hDval, show J * r - D = -(D - J * r) by abel, vfValue_neg_eq]
    exact hest
  have hJr : rv M (J * r) = rv M D := rv_eq_of_value_close hD0 hclose
  have hmul : rv M (J * r) = rv M J * rv M r := RVOperations.rv_mul J r
  rw [hmul, hDrv] at hJr
  exact mul_right_cancel₀ hr0 hJr

/-- **The Jacobian of the positioning map** at a generic point has value
`vrv(t(u)) / vrv(t₁(u))`, the value of the slope (Remark 7.18). -/
theorem positionMap_jacobian (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (H : BalancedShearInput X ε t t₁) (a : firstFamily X)
    (ha : AlgebraicIndependent (vfParameterField S) a.val.1) :
    ∃ J : VF M, HasMixedVFJacobianAt (positionMap H) a J ∧
      vfValue J * (rvRadius (secondParadigm t₁ a.val.2)).val = (rvRadius (t a.val.2)).val := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  obtain ⟨L, F, hF, hD⟩ := mixedDifferentiableAt_of_independent hc hκ.le hs hsmall hv (positionMap H) a ha
  have hJ : HasMixedVFJacobianAt (positionMap H) a (LinearMap.toMatrix' L).det := ⟨F, hF, hD.hasJacobianAt⟩
  refine ⟨_, hJ, ?_⟩
  have haf : a.val.1 0 ∈ first (cell X a.val.2) := (mem_firstFamily _ _).mp a.property
  have hne := cell_nonempty_of_first haf
  have hb := H.balanced a.val.2 hne
  obtain ⟨_, _, s, hsl⟩ := hb.rvAffine
  rw [vfValue_of_rv_eq (jacobian_rv_eq H a hJ hsl)]
  have he := slope_eq hb (hne.image Prod.fst) hsl
  have h := congrArg Values.vrv he
  rw [RVOperations.vrv_mul, RVOperations.vrv_mul] at h
  have h1 : Values.vrv (rv M (-1)) = 1 := by
    change vfValue (-1 : VF M) = 1
    rw [vfValue_neg_eq]
    exact Values.vf_value_one
  rw [h1, one_mul] at h
  rw [rvRadius_val, rvRadius_val, secondParadigm_val H hne]
  exact h

end Jacobian

/-! ### Lemma 6.38 for the positioning map -/

section Matching

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {S : Set M} {q : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

omit [M ⊨ Axioms.ACVF] in
/-- The identity map between definable sets with the same carrier. -/
def castMap {P : Space LRV M} {A B : DefSet P S} (h : A.carrier = B.carrier) : Map A B where
  toFun p := ⟨p.val, h ▸ p.property⟩
  graph_definable := (Map.id A).graph_definable

omit [M ⊨ Axioms.ACVF] in
theorem castMap_val {P : Space LRV M} {A B : DefSet P S} (h : A.carrier = B.carrier) (p : A) :
    (castMap h p).val = p.val := rfl

omit [M ⊨ Axioms.ACVF] in
/-- For unary sets, dropping the VF coordinate and the RV-tag quotient have
the same image. -/
theorem contracted_carrier_eq {s : ℕ} (B : DefSet (rawMixedSpace (M := M) 1 s) S) :
    (vfDropLast B).image.carrier = (rvTagQuotient B).carrier := by
  ext z
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, Prod.ext (funext fun i => i.elim0) ?_⟩
    have h2 : p.val.2 = z.2 := congrArg Prod.snd hp
    exact h2
  · rintro ⟨p, hp⟩
    refine ⟨p, Prod.ext (funext fun i => i.elim0) ?_⟩
    have h2 : p.val.2 = z.2 := congrArg Prod.snd hp
    exact h2

theorem codeValue_eq_gam (x : RVInfinity M) : GammaParameters.codeValue x.val = FirstStage.gam x := by
  by_cases h : x.val = iRVZero
  · have hNZ : ¬ GammaParameters.NonzeroRV x.val := fun h' => h'.2 h
    have e1 : GammaParameters.codeValue x.val = 1 := by simp [GammaParameters.codeValue, hNZ]
    have e2 : FirstStage.gam x = 1 := by simp [FirstStage.gam, h]
    rw [e1, e2]
  · apply Subtype.ext
    rw [nonzero_rv_codeValue_val x (fun he => h (congrArg Subtype.val he))]
    simp only [FirstStage.gam, dite_eq_left h]
    rfl

theorem gam_rvRadius (w : RV M) : FirstStage.gam w.val = rvRadius w := by
  rw [← codeValue_eq_gam]
  exact Subtype.ext (nonzero_rv_codeValue_val w.val w.property)

/-- **Lemma 6.38 for the positioning map of a balanced family** (referee R132).
Apply Lemma 6.38 over the support data to `(a, u) ↦ (ε(u, a), u)` from `A₁` to
`A₂`, with the label forms `vrv(t(u))` on `A₁` and `vrv(t₁(u))` on `A₂` (the
paper's constant forms `0` and `-γ`, shifted by `vrv(t(u))`). Its two chains are
contraction stages `S₁`, `S₂` (`ChainStages`), and the RV map `ψ` between their
contracted sets is a bijection keeping the old labels `u`, with
`vrv(lead ψ(z)) · vrv(t₁(u)) = vrv(lead z) · vrv(t(u))`; additively,
`vrv(lead ψ z) = vrv(lead z) + γ(u)` with `γ = vrv(t) - vrv(t₁)` the shift of
`ε(u, ·)`. -/
theorem exists_balanced_matching (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (H : BalancedShearInput X ε t t₁)
    (ht₁ : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![(t₁ u).val] (rvValues u)}) :
    ∃ (S₁ : StandardContractionStage (G := G) (firstFamily X))
      (S₂ : StandardContractionStage (G := G) (secondFamily X))
      (ψ : Map S₁.contracted S₂.contracted), Function.Bijective ψ ∧
      (∀ z i, (ψ z).val.2 (S₂.oldLabels i) = z.val.2 (S₁.oldLabels i)) ∧
      ∀ z : S₁.contracted,
        FirstStage.gam ((ψ z).val.2 S₂.leading) * FirstStage.gam (t₁ (fun i => z.val.2 (S₁.oldLabels i))) =
          FirstStage.gam (z.val.2 S₁.leading) * FirstStage.gam (t (fun i => z.val.2 (S₁.oldLabels i))).val := by
  obtain ⟨Hm⟩ := SetBaseMatching.unary_relative_measured_rv_family_matching_exists_of_support (G := G)
    h00 hc linear hκ hs hv S V hV hVS hSV hnt hsmall hΓ (firstFamily X) (secondFamily X) (positionMap H)
    (positionMap_home h00 hc linear hκ hs hv hsmall hΓ H)
    (firstFamily_properInvariant H) (secondFamily_properInvariant H) (sourceGammaForm H) (targetGammaForm H ht₁)
    (labelGammaMap_levels_open (G := G) hv _ (firstFamily_properInvariant H) _ _ _)
    (labelGammaMap_levels_open (G := G) hv _ (secondFamily_properInvariant H) _ _ _)
    (fun a ha => by
      obtain ⟨J, hJ, hval⟩ := positionMap_jacobian h00 hc hκ hs hsmall hv H a ha
      refine ⟨J, hJ, ?_⟩
      have h1 : gammaMapValue (sourceGammaForm H) a = rvRadius (t a.val.2) :=
        labelGammaMap_value _ _ _ _ a
      have h2 : gammaMapValue (targetGammaForm H ht₁) (positionMap H a) =
          rvRadius (secondParadigm t₁ a.val.2) := labelGammaMap_value _ _ _ _ _
      rw [h1, h2, div_eq_mul_inv]
      have hne : (rvRadius (secondParadigm t₁ a.val.2)).val ≠ 0 := fun h =>
        (rvRadius (secondParadigm t₁ a.val.2)).property (h.trans Values.infinity_eq_zero.symm)
      change vfValue J = (rvRadius (t a.val.2)).val * (rvRadius (secondParadigm t₁ a.val.2)).val⁻¹
      exact (eq_mul_inv_iff_mul_eq₀ hne).mpr hval)
  let S₁ := ChainStages.sourceStage h00 hc linear hκ hs hv hsmall hΓ Hm
  let S₂ := ChainStages.targetStage h00 hc linear hκ hs hv hsmall hΓ Hm
  have h₁ : S₁.contracted.carrier = (rvTagQuotient Hm.geometry.source).carrier :=
    contracted_carrier_eq Hm.geometry.source
  have h₂ : S₂.contracted.carrier = (rvTagQuotient Hm.geometry.target).carrier :=
    contracted_carrier_eq Hm.geometry.target
  let ψ : Map S₁.contracted S₂.contracted := (castMap h₂.symm).comp (Hm.rv.map.comp (castMap h₁))
  have hψ : ∀ z : S₁.contracted, (ψ z).val = (Hm.rv.map (castMap h₁ z)).val := fun _ => rfl
  -- every contracted point comes from a point of `A₁`
  have hz : ∀ z : S₁.contracted, ∃ a : firstFamily X,
      castMap h₁ z = rvTagQuotientMap Hm.geometry.source (Hm.geometry.sourceMap a) := by
    intro z
    obtain ⟨p, hp⟩ := z.property
    obtain ⟨a, ha⟩ := (Hm.geometry.sourceChain.bijective h00).2 p
    refine ⟨a, Subtype.ext (Prod.ext (funext fun i => i.elim0) ?_)⟩
    change z.val.2 = (Hm.geometry.sourceMap a).val.2
    rw [ha]
    exact (congrArg Prod.snd hp).symm
  have hψa : ∀ (z : S₁.contracted) (a : firstFamily X),
      castMap h₁ z = rvTagQuotientMap Hm.geometry.source (Hm.geometry.sourceMap a) →
        (ψ z).val.2 = (Hm.geometry.targetMap (positionMap H a)).val.2 := by
    intro z a ha
    rw [hψ, ha, Hm.rv.commutes, Hm.geometry.commutes]
    rfl
  have hza : ∀ (z : S₁.contracted) (a : firstFamily X),
      castMap h₁ z = rvTagQuotientMap Hm.geometry.source (Hm.geometry.sourceMap a) →
        z.val.2 = (Hm.geometry.sourceMap a).val.2 := by
    intro z a ha
    exact congrArg (fun w : rvTagQuotient Hm.geometry.source => w.val.2) ha
  have hold₁ : ∀ (a : firstFamily X) (i : Fin q),
      (Hm.geometry.sourceMap a).val.2 (S₁.oldLabels i) = a.val.2 i := fun a i => S₁.retained a i
  have hold₂ : ∀ (b : secondFamily X) (i : Fin q),
      (Hm.geometry.targetMap b).val.2 (S₂.oldLabels i) = b.val.2 i := fun b i => S₂.retained b i
  refine ⟨S₁, S₂, ψ, ?_, ?_, ?_⟩
  · -- bijectivity
    constructor
    · intro z z' he
      apply Subtype.ext
      have h := Hm.rv.bijective.1 (Subtype.ext (by
        have := congrArg Subtype.val he
        rw [hψ, hψ] at this
        exact this) : Hm.rv.map (castMap h₁ z) = Hm.rv.map (castMap h₁ z'))
      have h' := congrArg Subtype.val h
      exact h'
    · intro w
      obtain ⟨v, hv'⟩ := Hm.rv.bijective.2 (castMap h₂ w)
      refine ⟨castMap h₁.symm v, Subtype.ext ?_⟩
      rw [hψ]
      have hcast : castMap h₁ (castMap h₁.symm v) = v := Subtype.ext rfl
      rw [hcast, hv']
      rfl
  · -- the old labels are kept
    intro z i
    obtain ⟨a, ha⟩ := hz z
    rw [hψa z a ha, hza z a ha, hold₂, hold₁]
    rfl
  · -- the Gamma identity
    intro z
    obtain ⟨a, ha⟩ := hz z
    have hu : (fun i => z.val.2 (S₁.oldLabels i)) = a.val.2 := by
      funext i
      rw [hza z a ha, hold₁]
    rw [hu]
    have hvol := Hm.rv.volume (castMap h₁ z)
    rw [ha, Hm.rv.commutes, Hm.geometry.commutes] at hvol
    have hω' : ∀ p ∈ Hm.geometry.source.carrier, ∀ p' ∈ Hm.geometry.source.carrier, p.2 = p'.2 →
        gammaFormExtension (Hm.geometry.sourceForm h00 (sourceGammaForm H)) p =
          gammaFormExtension (Hm.geometry.sourceForm h00 (sourceGammaForm H)) p' := Hm.sourceContractible
    have hσ' : ∀ p ∈ Hm.geometry.target.carrier, ∀ p' ∈ Hm.geometry.target.carrier, p.2 = p'.2 →
        gammaFormExtension (Hm.geometry.targetForm h00 (targetGammaForm H ht₁)) p =
          gammaFormExtension (Hm.geometry.targetForm h00 (targetGammaForm H ht₁)) p' := Hm.targetContractible
    have hA : rvContractedGamma Hm.geometry.source.carrier
        (gammaFormExtension (Hm.geometry.sourceForm h00 (sourceGammaForm H)))
        (rvInputValues (Hm.geometry.sourceMap a).val.2) = rvRadius (t a.val.2) := by
      rw [rvContractedGamma_at _ _ hω' _ (Hm.geometry.sourceMap a).property, gammaFormExtension_at,
        Hm.geometry.sourceForm_transport]
      exact labelGammaMap_value _ _ _ _ a
    have hB : rvContractedGamma Hm.geometry.target.carrier
        (gammaFormExtension (Hm.geometry.targetForm h00 (targetGammaForm H ht₁)))
        (rvInputValues (Hm.geometry.targetMap (positionMap H a)).val.2) =
          rvRadius (secondParadigm t₁ a.val.2) := by
      rw [rvContractedGamma_at _ _ hσ' _ (Hm.geometry.targetMap (positionMap H a)).property,
        gammaFormExtension_at, Hm.geometry.targetForm_transport]
      exact labelGammaMap_value _ _ _ _ (positionMap H a)
    change rvContractedGamma Hm.geometry.source.carrier
        (gammaFormExtension (Hm.geometry.sourceForm h00 (sourceGammaForm H)))
        (rvInputValues (Hm.geometry.sourceMap a).val.2) *
          GammaParameters.codeValue ((Hm.geometry.sourceMap a).val.2 Hm.sourceIndex).val =
        rvContractedGamma Hm.geometry.target.carrier
          (gammaFormExtension (Hm.geometry.targetForm h00 (targetGammaForm H ht₁)))
          (rvInputValues (Hm.geometry.targetMap (positionMap H a)).val.2) *
            GammaParameters.codeValue ((Hm.geometry.targetMap (positionMap H a)).val.2 Hm.targetIndex).val at hvol
    rw [hA, hB, codeValue_eq_gam, codeValue_eq_gam] at hvol
    have hne : (cell X a.val.2).Nonempty := cell_nonempty_of_first ((mem_firstFamily _ _).mp a.property)
    rw [gam_rvRadius, ← secondParadigm_val H hne, gam_rvRadius, hψa z a ha, hza z a ha]
    change FirstStage.gam ((Hm.geometry.targetMap (positionMap H a)).val.2 Hm.targetIndex) *
        rvRadius (secondParadigm t₁ a.val.2) =
      FirstStage.gam ((Hm.geometry.sourceMap a).val.2 Hm.sourceIndex) * rvRadius (t a.val.2)
    rw [mul_comm, ← hvol, mul_comm]

end Matching

end DiamondIntegral.Section7.BalancedMatching
