import «section 7».Lemma720Good

/-! Lemma 7.20, step 9: the protected neighbourhood of the obstacles (set level).

Data: a set `B ⊆ VF × RVᵃ`, a positioning function `e`, a leading label `lead` and a
finite set `Q ⊆ VF`. A radius `β` is *good* for `z ∈ Q` and labels `w` if the open ball of
radius `β` around `z` lies in `B_w`, the translates `e(·, w) + t^♯` are constant on it, and
it contains no other point of `Q`. `K w z` is the union of the good balls around `z`, and
`U` is the union of the `K w z`.

* `K_disjoint`: the `K w z` for distinct `z ∈ Q` are disjoint.
* `self_mem_K`: under local constancy of the translates (`LocConst`), `z ∈ K w z` whenever
  `(z, w) ∈ B`.
* `U_fibre_invariant`, `compl_fibre_invariant`: the fibres of `U` and of `B ∖ U` are
  `α`-invariant.
* `disc_sub_K`: an open disc inside `U_w` lies in a single `K w z`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Protect
variable (B : Set (Mixed M 1 a)) (e : Mixed M 1 a → VF M) (lead : Fin a) (Q : Finset (VF M))

/-- A good radius around `z ∈ Q` for the labels `w`. -/
def Good (w : Fin a → RVInfinity M) (z : VF M) (β : Gamma M) : Prop :=
  (∀ x', β.val < vfValue (x' - z) →
    mkPoint x' w ∈ B ∧ Values.vrv (w lead) < vfValue (e (mkPoint x' w) - e (mkPoint z w))) ∧
  (∀ z' ∈ Q, z' ≠ z → ¬ β.val < vfValue (z' - z))

/-- The union of the good balls around `z`. -/
def K (w : Fin a → RVInfinity M) (z : VF M) : Set (VF M) :=
  {x | ∃ β, β.val < vfValue (x - z) ∧ Good B e lead Q w z β}

/-- The protected neighbourhood of `Q`. -/
def U : Set (Mixed M 1 a) := {q | q ∈ B ∧ ∃ z ∈ Q, q.1 0 ∈ K B e lead Q q.2 z}

/-- Local constancy of the translates, with a radius for each label tuple. -/
def LocConst : Prop :=
  ∀ w : Fin a → RVInfinity M, ∃ α : Gamma M, ∀ x x' : VF M, α.val < vfValue (x - x') →
    mkPoint x w ∈ B → mkPoint x' w ∈ B ∧ Values.vrv (w lead) < vfValue (e (mkPoint x w) - e (mkPoint x' w))

variable {B e lead Q}

theorem good_mono {w : Fin a → RVInfinity M} {z : VF M} {β β' : Gamma M}
    (h : Good B e lead Q w z β) (hle : β ≤ β') : Good B e lead Q w z β' := by
  refine ⟨fun x' hx' => h.1 x' (lt_of_le_of_lt (show β.val ≤ β'.val from hle) hx'), fun z' hz' hne hlt => ?_⟩
  exact h.2 z' hz' hne (lt_of_le_of_lt (show β.val ≤ β'.val from hle) hlt)

theorem mem_K_sub {w : Fin a → RVInfinity M} {z x : VF M} (hx : x ∈ K B e lead Q w z) :
    mkPoint x w ∈ B ∧ Values.vrv (w lead) < vfValue (e (mkPoint x w) - e (mkPoint z w)) := by
  obtain ⟨β, hβ, hgood⟩ := hx
  exact hgood.1 x hβ

section Val
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
include hv

theorem K_disjoint {w : Fin a → RVInfinity M} {z z' : VF M} (hz : z ∈ Q) (hz' : z' ∈ Q) (hne : z ≠ z')
    {x : VF M} (hx : x ∈ K B e lead Q w z) (hx' : x ∈ K B e lead Q w z') : False := by
  obtain ⟨β, hβ, hg⟩ := hx
  obtain ⟨β', hβ', hg'⟩ := hx'
  rcases le_total β β' with h | h
  · apply hg.2 z' hz' (Ne.symm hne)
    have he : z' - z = -(x - z') + (x - z) := by ring
    rw [he]
    exact lt_vfValue_add hv (by rw [vfValue_neg hv]; exact lt_of_le_of_lt (show β.val ≤ β'.val from h) hβ') hβ
  · apply hg'.2 z hz hne
    have he : z - z' = -(x - z) + (x - z') := by ring
    rw [he]
    exact lt_vfValue_add hv (by rw [vfValue_neg hv]; exact lt_of_le_of_lt (show β'.val ≤ β.val from h) hβ) hβ'

/-- A good radius exists around every point of `Q` in `B_w`. -/
theorem exists_good (hloc : LocConst B e lead) (w : Fin a → RVInfinity M) {z : VF M}
    (hzB : mkPoint z w ∈ B) : ∃ β, Good B e lead Q w z β := by
  obtain ⟨α, hα⟩ := hloc w
  classical
  let γ' : VF M → Gamma M := fun z' => if h : z' = z then α else gval (z' - z) (sub_ne_zero.mpr h)
  obtain ⟨β₀, hβ₀⟩ := (Q.image γ').exists_le
  refine ⟨max α β₀, fun x' hx' => ?_, fun z' hz' hne hlt => ?_⟩
  · have hclose : α.val < vfValue (z - x') := by
      rw [vfValue_sub_comm hv]
      exact lt_of_le_of_lt (show α.val ≤ (max α β₀).val from le_max_left α β₀) hx'
    obtain ⟨hB, hval⟩ := hα z x' hclose hzB
    exact ⟨hB, by rw [vfValue_sub_comm hv]; exact hval⟩
  · have hle : γ' z' ≤ β₀ := hβ₀ _ (Finset.mem_image.mpr ⟨z', hz', rfl⟩)
    have hγ : vfValue (z' - z) = (γ' z').val := by
      simp only [γ', dif_neg hne, gval_val]
    rw [hγ] at hlt
    exact absurd (lt_of_lt_of_le hlt (show (γ' z').val ≤ (max α β₀).val from
      hle.trans (le_max_right α β₀))) (lt_irrefl _)

theorem self_mem_K (hloc : LocConst B e lead) (w : Fin a → RVInfinity M) {z : VF M}
    (hzB : mkPoint z w ∈ B) : z ∈ K B e lead Q w z := by
  obtain ⟨β, hβ⟩ := exists_good hv hloc w hzB
  refine ⟨β, ?_, hβ⟩
  rw [sub_self]
  exact SpecialTransformations.Section9.gamma_lt_value_zero β

theorem mkPoint_eta (x : Fin 1 → VF M) (w : Fin a → RVInfinity M) : mkPoint (x 0) w = (x, w) := by
  refine Prod.ext ?_ rfl
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rfl

/-- Membership in `K` is stable under moving by more than a good radius. -/
theorem K_stable (hloc : LocConst B e lead) {w : Fin a → RVInfinity M} {z x x' : VF M} (hz : z ∈ Q)
    (hx : x ∈ K B e lead Q w z) {β₀ : Gamma M} (hβ₀ : Good B e lead Q w z β₀)
    (hclose : β₀.val < vfValue (x' - x)) : x' ∈ K B e lead Q w z := by
  obtain ⟨β, hβ, hg⟩ := hx
  let β' := min β β₀
  have hg' : Good B e lead Q w z β' := by
    change Good B e lead Q w z (min β β₀)
    rcases min_choice β β₀ with h | h <;> rw [h] <;> assumption
  refine ⟨β', ?_, hg'⟩
  have he : x' - z = (x' - x) + (x - z) := by ring
  rw [he]
  exact lt_vfValue_add hv (lt_of_le_of_lt (show β'.val ≤ β₀.val from min_le_right β β₀) hclose)
    (lt_of_le_of_lt (show β'.val ≤ β.val from min_le_left β β₀) hβ)

/-- **Invariance of the fibres of `U`.** -/
theorem U_fibre_invariant (hloc : LocConst B e lead) (w : Fin a → RVInfinity M) :
    ∃ β : Gamma M, ∀ x x' : Fin 1 → VF M, β.val < vfValue (x 0 - x' 0) →
      ((x, w) ∈ U B e lead Q ↔ (x', w) ∈ U B e lead Q) := by
  classical
  -- a good radius for each relevant point of `Q`
  have hgood : ∀ z ∈ Q, ∃ β : Gamma M, mkPoint z w ∈ B → Good B e lead Q w z β := by
    intro z hz
    by_cases hzB : mkPoint z w ∈ B
    · obtain ⟨β, hβ⟩ := exists_good hv hloc w hzB
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨1, fun h => absurd h hzB⟩
  choose βf hβf using hgood
  let γ' : VF M → Gamma M := fun z => if h : z ∈ Q then βf z h else 1
  obtain ⟨β, hβ⟩ := (Q.image γ').exists_le
  have hstep : ∀ x x' : Fin 1 → VF M, β.val < vfValue (x 0 - x' 0) →
      (x, w) ∈ U B e lead Q → (x', w) ∈ U B e lead Q := by
    rintro x x' hxx' ⟨-, z, hz, hxK⟩
    have hzB : mkPoint z w ∈ B := by
      obtain ⟨β₁, -, hg₁⟩ := hxK
      refine (hg₁.1 z ?_).1
      rw [sub_self]
      exact SpecialTransformations.Section9.gamma_lt_value_zero β₁
    have hgz := hβf z hz hzB
    have hle : βf z hz ≤ β := by
      have := hβ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      simpa only [γ', dif_pos hz] using this
    have hx'K : x' 0 ∈ K B e lead Q w z :=
      K_stable hv hloc hz hxK (good_mono hgz le_rfl)
        (lt_of_le_of_lt (show (βf z hz).val ≤ β.val from hle)
          (by rw [vfValue_sub_comm hv]; exact hxx'))
    refine ⟨?_, z, hz, hx'K⟩
    have := (mem_K_sub hx'K).1
    rwa [mkPoint_eta] at this
  refine ⟨β, fun x x' hxx' => ⟨hstep x x' hxx', hstep x' x (by rw [vfValue_sub_comm hv]; exact hxx')⟩⟩

theorem vfValue_natCast_mul (h00 : M ⊨ Axioms.ACVF00) (n : ℕ) (hn : n ≠ 0) (π : VF M) :
    vfValue ((n : VF M) * π) = vfValue π := by
  rw [vfValue_mul_eq]
  have h1 : vfValue (n : VF M) = vfValue (1 : VF M) := by
    rw [vfValue_eq_iff hv, map_one]
    exact SpecialTransformations.Section3.Barycentre.natCast_value_one Valued.v hv h00 n hn
  rw [h1, ← vfValue_mul_eq, one_mul]

/-- Points `d + k π`, `k = 1, …, N`, are at pairwise distance `vfValue π`. -/
theorem vfValue_sub_points (h00 : M ⊨ Axioms.ACVF00) (d π : VF M) {k l : ℕ} (hkl : k ≠ l) :
    vfValue ((d + (k : VF M) * π) - (d + (l : VF M) * π)) = vfValue π := by
  rcases lt_or_gt_of_ne hkl with h | h
  · have he : (d + (k : VF M) * π) - (d + (l : VF M) * π) = -(((l - k : ℕ) : VF M) * π) := by
      rw [Nat.cast_sub h.le]
      ring
    rw [he, vfValue_neg hv, vfValue_natCast_mul hv h00 _ (Nat.sub_ne_zero_of_lt h)]
  · have he : (d + (k : VF M) * π) - (d + (l : VF M) * π) = ((k - l : ℕ) : VF M) * π := by
      rw [Nat.cast_sub h.le]
      ring
    rw [he, vfValue_natCast_mul hv h00 _ (Nat.sub_ne_zero_of_lt h)]

/-- **An open disc inside `U_w` lies in a single `K w z`.** -/
theorem disc_sub_K (h00 : M ⊨ Axioms.ACVF00) {w : Fin a → RVInfinity M} {D : Set (VF M)}
    (hD : IsOpenDiscVF D) (hsub : ∀ x ∈ D, ∃ z ∈ Q, x ∈ K B e lead Q w z) :
    ∃ z ∈ Q, D ⊆ K B e lead Q w z := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨d, ρ, hρ⟩ := hD
  have hdD : d ∈ D := (mem_disc_iff hv hρ d).mpr (by rw [sub_self]; exact SpecialTransformations.Section9.gamma_lt_value_zero ρ)
  -- a point of `D` outside each `K w z`
  have hout : ∀ z, ∃ y ∈ D, z ∈ Q → y ∉ K B e lead Q w z := by
    intro z
    by_cases hz : z ∈ Q
    · obtain ⟨y, hyD, hyK⟩ := Set.not_subset.mp (hno z hz)
      exact ⟨y, hyD, fun _ => hyK⟩
    · exact ⟨d, hdD, fun h => absurd h hz⟩
  choose xz hxzD hxzK using hout
  -- points of `D ∩ K w z` are closer to `z` than `xz z`
  have hclaim : ∀ z ∈ Q, ∀ x ∈ D, x ∈ K B e lead Q w z →
      vfValue (xz z - z) < vfValue (x - z) ∧ ρ.val < vfValue (xz z - z) := by
    intro z hz x hxD hxK
    obtain ⟨β, hβ, hg⟩ := hxK
    have h1 : vfValue (xz z - z) ≤ β.val := by
      by_contra hlt
      rw [not_le] at hlt
      exact hxzK z hz ⟨β, hlt, hg⟩
    refine ⟨lt_of_le_of_lt h1 hβ, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hxx : ρ.val < vfValue (xz z - x) := lt_of_mem_disc hv hρ (hxzD z) hxD
    have h2 : vfValue (xz z - z) < vfValue (xz z - x) := lt_of_le_of_lt hle hxx
    have h3 : vfValue (xz z - z) < vfValue (x - z) := lt_of_le_of_lt h1 hβ
    have he : xz z - z = (xz z - x) + (x - z) := by ring
    have h4 := lt_vfValue_add hv h2 h3
    rw [← he] at h4
    exact lt_irrefl _ h4
  -- the relevant points of `Q`
  let R := Q.filter (fun z => ∃ x ∈ D, x ∈ K B e lead Q w z)
  obtain ⟨z₀, hz₀, hdK⟩ := hsub d hdD
  have hRne : R.Nonempty := ⟨z₀, Finset.mem_filter.mpr ⟨hz₀, d, hdD, hdK⟩⟩
  have hne0 : ∀ z ∈ R, xz z - z ≠ 0 := by
    intro z hz h0
    obtain ⟨hzQ, x, hxD, hxK⟩ := Finset.mem_filter.mp hz
    have := (hclaim z hzQ x hxD hxK).1
    rw [h0] at this
    have hinf : vfValue (0 : VF M) = SpecialTransformations.Section3.Values.infinity := by
      change Values.vfValueHom (0 : VF M) = _
      rw [map_zero, ← Values.infinity_eq_zero]
    rw [hinf] at this
    exact absurd (lt_of_lt_of_le this (SpecialTransformations.Section3.Values.le_infinity _))
      (lt_irrefl _)
  let g : VF M → Gamma M := fun z => if h : xz z - z ≠ 0 then gval _ h else ρ
  have hg : ∀ z ∈ R, (g z).val = vfValue (xz z - z) := by
    intro z hz
    simp only [g, dif_pos (hne0 z hz), gval_val]
  let μ := (R.image g).min' (hRne.image g)
  have hρμ : ρ < μ := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro γ hγ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨hzQ, x, hxD, hxK⟩ := Finset.mem_filter.mp hz
    have := (hclaim z hzQ x hxD hxK).2
    rw [← hg z hz] at this
    exact this
  have hμg : ∀ z ∈ R, μ ≤ g z := fun z hz => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  obtain ⟨t, -, ht⟩ := SpecialTransformations.Section3.Values.gamma_has_nonzero_representative μ
  obtain ⟨π, hπ⟩ := rv_surjective t
  have hvπ : vfValue π = μ.val := by
    change Values.vrv (rv M π) = μ.val
    rw [hπ]
    exact ht
  let pt (k : ℕ) : VF M := d + (k : VF M) * π
  have hptD : ∀ k, pt k ∈ D := by
    intro k
    apply mem_disc_of_close hv hρ hdD
    by_cases hk : k = 0
    · rw [hk, Nat.cast_zero, zero_mul]
      exact SpecialTransformations.Section9.gamma_lt_value_zero ρ
    · rw [vfValue_natCast_mul hv h00 k hk, hvπ]
      exact hρμ
  have hcover : ∀ k, ∃ z ∈ Q, pt k ∈ K B e lead Q w z := fun k => hsub (pt k) (hptD k)
  choose zk hzkQ hzkK using hcover
  have hinj : Set.InjOn zk (Finset.range (Q.card + 1) : Set ℕ) := by
    intro k _ l _ hkl
    by_contra hne
    have hzR : zk k ∈ R := Finset.mem_filter.mpr ⟨hzkQ k, pt k, hptD k, hzkK k⟩
    have h1 := (hclaim (zk k) (hzkQ k) (pt k) (hptD k) (hzkK k)).1
    have h2 := (hclaim (zk k) (hzkQ k) (pt l) (hptD l) (hkl ▸ hzkK l)).1
    rw [← hg _ hzR] at h1 h2
    have hμ : μ.val ≤ (g (zk k)).val := hμg _ hzR
    have he : pt k - pt l = (pt k - zk k) + -(pt l - zk k) := by ring
    have h3 := lt_vfValue_add hv h1 (by rw [vfValue_neg hv]; exact h2)
    rw [← he, vfValue_sub_points hv h00 d π hne, hvπ] at h3
    exact absurd (lt_of_le_of_lt hμ h3) (lt_irrefl _)
  have hmaps : Set.MapsTo zk (Finset.range (Q.card + 1) : Set ℕ) (Q : Set (VF M)) :=
    fun k _ => hzkQ k
  have hcard := Finset.card_le_card_of_injOn zk hmaps hinj
  simp only [Finset.card_range] at hcard
  omega

end Val

end Protect

end DiamondIntegral.Section7.Lemma720
