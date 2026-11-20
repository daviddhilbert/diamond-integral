import «section 7».BalancedShearStages
import «section 7».ChainStages
import «section 7».SetBaseMatching
import «section 7».FirstStage

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
    have h1' : γ.val < vfValue (a - a') := by rw [vfValue_sub_comm']; exact h1
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

theorem vfValue_neg' (x : VF M) : vfValue (-x) = vfValue x := vfValue_neg x

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
        vfValue_neg']
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
        rw [add_sub_cancel_right, show y - s₂ - y = -s₂ by abel, vfValue_neg']
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

end DiamondIntegral.Section7.BalancedMatching
