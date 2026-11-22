import «section 8».TruncGood

/-! Equality of truncation classes of ambient sets, and its composition.

`TEq P m A B`: at every scale `L` and cutoffs `b` for which the scaled traces of `A` and `B` lie in
`𝒪` and are invariant, their normalized truncation classes agree. `Good P m A` collects the bounds of
a proper invariant set (`good_of_proper`).

* `fullClass_strace_shift`: changing the scale `L` multiplies the class by a power of `[𝔸]`;
* `teq_trans`: `TEq` is transitive between good sets (change scale and cutoffs);
* `teq_of_step`: a bijection respecting congruence at cofinally many cutoffs, both ways, gives `TEq`
  (`fullClass_eq_of_ambient`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open DiamondIntegral.Section2 DiamondIntegral.Section3
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal DiamondIntegral.Section8.Hm

local instance chainStructure : LRV.Structure Carrier := canonicalInterpret
local instance chainModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

/-! ### Congruence of classes -/

theorem resSetClass_congr {K : ℕ} (A B : DefSet (rawRVSpace (M := Carrier) K) {c | baseCarrier c})
    (h : A.carrier = B.carrier) (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite) :
    resSetClass canonicalInterpret_isCanonical A hA = resSetClass canonicalInterpret_isCanonical B hB := by
  cases A
  cases B
  cases h
  rfl

variable (P : PuiseuxAmbient) {n l : ℕ} (m : ℕ+) (b : Fin n → ℕ)

theorem fullClass_congr {X X' : Set (Fin (n + l) → Carrier)} (h : mixedSet X = mixedSet X')
    (Q : Finset (Fin l → ℤ)) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hX' : DefinableOver {c | baseCarrier c} (mixedSorts n l) X')
    (hA : Invariant m b (mixedSet X)) (hA' : Invariant m b (mixedSet X'))
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q (mixedSet X')) :
    fullClass m b Q hX hA hQ = fullClass m b Q hX' hA' hQ' := by
  have e := resSetClass_congr (fullTruncDefSet m b Q hX hA hQ) (fullTruncDefSet m b Q hX' hA' hQ')
    (by simp only [fullTruncDefSet, h]) (fullTruncSet_finite_values m b Q hX hA hQ)
    (fullTruncSet_finite_values m b Q hX' hA' hQ')
  unfold fullClass
  rw [e]

theorem fullClass_Q (Q Q' : Finset (Fin l → ℤ)) {X : Set (Fin (n + l) → Carrier)}
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) (hA : Invariant m b (mixedSet X))
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet X)) :
    fullClass m b Q hX hA hQ = fullClass m b Q' hX hA hQ' := by
  have e := resSetClass_congr (fullTruncDefSet m b Q hX hA hQ) (fullTruncDefSet m b Q' hX hA hQ') rfl
    (fullTruncSet_finite_values m b Q hX hA hQ) (fullTruncSet_finite_values m b Q' hX hA hQ')
  unfold fullClass
  rw [e]

/-! ### Changing the scale of a trace -/

theorem tInv_add (L k : ℕ) : tInv (L + k) = tInv L * tInv k := by
  rw [tInv, tInv, tInv, tPow, tPow, tPow, pow_add, mul_inv]

theorem unscaleP_add (L k : ℕ) (p : (Fin n → Ser) × (Fin l → RV)) :
    unscaleP L (unscaleP k p) = unscaleP (L + k) p :=
  Prod.ext (funext fun i => by change tInv L * (tInv k * p.1 i) = tInv (L + k) * p.1 i; rw [tInv_add, mul_assoc]) rfl

theorem mixedSet_scale_strace (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) (L k : ℕ) :
    mixedSet (scaleRaw k (strace P L A)) = mixedSet (strace P (L + k) A) := by
  ext p
  rw [mem_mixedSet_scale, mem_strace, mem_strace, unscaleP_add]

theorem rationalIntegral_scale {X : Set (Fin (n + l) → Carrier)} (k : ℕ)
    (h : RationalIntegral m (mixedSet X)) : RationalIntegral m (mixedSet (scaleRaw k X)) := by
  intro p hp hr i γ hγ
  rw [mem_mixedSet_scale] at hp
  have hint := h _ hp (fun i => isRational_tInv m k (hr i)) i
  have he : p.1 i = tPow k * (tInv k * p.1 i) := (tPow_mul_tInv k _).symm
  rw [he, cf_tPow_mul]
  exact hint _ (by have : (0 : ℚ) ≤ k := by positivity
                   linarith)

/-- **Changing the scale of a trace.** -/
theorem fullClass_strace_shift (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) (L k : ℕ)
    (Q : Finset (Fin l → ℤ)) (hA : Invariant m b (mixedSet (strace P L A)))
    (hQ : Covers m Q (mixedSet (strace P L A))) (hnz : LabelsNonzero (mixedSet (strace P L A)))
    (hlow : RationalIntegral m (mixedSet (strace P L A)))
    (hA' : Invariant m (bL m b k) (mixedSet (strace P (L + k) A)))
    (hQ' : Covers m Q (mixedSet (strace P (L + k) A))) :
    fullClass m (bL m b k) Q (strace_definableOver P (L + k) A) hA' hQ' =
      fullClass m b Q (strace_definableOver P L A) hA hQ * Linv (n * ((m : ℕ) * k)) := by
  rw [← fullClass_scale m b k Q (strace_definableOver P L A) hA hQ hnz hlow]
  exact fullClass_congr m _ (mixedSet_scale_strace P A L k).symm Q _ _ _ _ _ _

theorem Linv_cancel {x y : Rloc} (k : ℕ) (h : x * Linv k = y * Linv k) : x = y := by
  have hu : IsUnit (Linv k) := (Units.isUnit _).pow k
  exact hu.mul_right_cancel h

/-! ### Good sets -/

/-- The bounds needed to compare truncation classes. -/
structure Good {l : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) : Prop where
  low : ∃ N : ℕ, ∀ L, N ≤ L → RationalIntegral m (mixedSet (strace P L A))
  nz : ∀ L, LabelsNonzero (mixedSet (strace P L A))
  cov : ∀ L, ∃ Q : Finset (Fin l → ℤ), Covers m Q (mixedSet (strace P L A))
  inv : ∃ q : ℚ, ∀ (L : ℕ) (b : Fin n → ℕ), (∀ i, q ≤ lev m (b i) - L) →
    AmbInvariant P (rad P m b L) A.carrier

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hv in
theorem good_of_proper {l : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hA : DiamondIntegral.Section6.ProperInvariant (P.G.real : Set P.N) A.carrier) : Good P m A :=
  ⟨rationalIntegral_strace P m A hA.vfBounded, fun L => labelsNonzero_strace P L A hA.rvBounded,
    fun L => covers_strace P m L A hA.rvBounded, amb_invariant P Gv hv m A hA⟩

/-- Cutoffs above a threshold. -/
theorem exists_cutoff (q : ℚ) (L : ℕ) (b0 : Fin n → ℕ) :
    ∃ b : Fin n → ℕ, (∀ i, b0 i ≤ b i) ∧ ∀ i, q ≤ lev m (b i) - L := by
  refine ⟨fun i => max (b0 i) ⌈((m : ℕ) : ℚ) * (q + L)⌉₊, fun i => le_max_left _ _, fun i => ?_⟩
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  have h1 : ((m : ℕ) : ℚ) * (q + L) ≤ (max (b0 i) ⌈((m : ℕ) : ℚ) * (q + L)⌉₊ : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  rw [lev, le_sub_iff_add_le, le_div_iff₀ hm]
  linarith

theorem invariant_of_good {l : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
    (hA : Good P m A) (L : ℕ) (b0 : Fin n → ℕ) :
    ∃ b : Fin n → ℕ, (∀ i, b0 i ≤ b i) ∧ Invariant m b (mixedSet (strace P L A)) := by
  obtain ⟨q, hq⟩ := hA.inv
  obtain ⟨b, hb, hbq⟩ := exists_cutoff m q L b0
  exact ⟨b, hb, invariant_strace P m b L A (hq L b hbq)⟩

/-! ### Equality of classes -/

/-- **Equality of the normalized truncation classes** of two ambient sets, at every admissible scale
and cutoff. -/
def TEq {r s : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N))
    (B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)) : Prop :=
  ∀ (L : ℕ) (b : Fin n → ℕ) (QA : Finset (Fin r → ℤ)) (QB : Finset (Fin s → ℤ))
    (hA : Invariant m b (mixedSet (strace P L A))) (hB : Invariant m b (mixedSet (strace P L B)))
    (hQA : Covers m QA (mixedSet (strace P L A))) (hQB : Covers m QB (mixedSet (strace P L B))),
    RationalIntegral m (mixedSet (strace P L A)) → RationalIntegral m (mixedSet (strace P L B)) →
    fullClass m b QA (strace_definableOver P L A) hA hQA = fullClass m b QB (strace_definableOver P L B) hB hQB

theorem teq_refl {r : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)) : TEq P m A A :=
  fun L b QA QB hA hB hQA hQB _ _ => fullClass_Q m b QA QB _ hA hQA hQB

/-- Moving up the cutoffs. -/
theorem fullClass_strace_mono {r : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N))
    (L : ℕ) {b b' : Fin n → ℕ} (h : ∀ i, b i ≤ b' i) (Q : Finset (Fin r → ℤ))
    (hA : Invariant m b (mixedSet (strace P L A))) (hA' : Invariant m b' (mixedSet (strace P L A)))
    (hQ : Covers m Q (mixedSet (strace P L A))) (hnz : LabelsNonzero (mixedSet (strace P L A))) :
    fullClass m b' Q (strace_definableOver P L A) hA' hQ = fullClass m b Q (strace_definableOver P L A) hA hQ :=
  fullClass_cutoff m h Q (strace_definableOver P L A) hA hQ hnz

/-- **Transitivity of `TEq`.** -/
theorem teq_trans {r s t : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)}
    {B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)}
    {C : DefSet (rawMixedSpace (M := P.N) n t) (P.G.real : Set P.N)}
    (gA : Good P m A) (gB : Good P m B) (gC : Good P m C) (hAB : TEq P m A B) (hBC : TEq P m B C) :
    TEq P m A C := by
  intro L b QA QC hA hC hQA hQC rA rC
  obtain ⟨N, hN⟩ := gB.low
  let k := N
  have hLk : N ≤ L + k := Nat.le_add_left N L
  obtain ⟨QB, hQB⟩ := gB.cov (L + k)
  obtain ⟨b', hbb', hB'⟩ := invariant_of_good P m gB (L + k) (bL m b k)
  have hA1 : Invariant m (bL m b k) (mixedSet (strace P (L + k) A)) := by
    have h := invariant_scale m b k hA
    rwa [mixedSet_scale_strace] at h
  have hC1 : Invariant m (bL m b k) (mixedSet (strace P (L + k) C)) := by
    have h := invariant_scale m b k hC
    rwa [mixedSet_scale_strace] at h
  have hQA1 : Covers m QA (mixedSet (strace P (L + k) A)) := by
    have h := covers_scale m k hQA rA
    rwa [mixedSet_scale_strace] at h
  have hQC1 : Covers m QC (mixedSet (strace P (L + k) C)) := by
    have h := covers_scale m k hQC rC
    rwa [mixedSet_scale_strace] at h
  have rA1 : RationalIntegral m (mixedSet (strace P (L + k) A)) := by
    have h := rationalIntegral_scale m k rA
    rwa [mixedSet_scale_strace] at h
  have rC1 : RationalIntegral m (mixedSet (strace P (L + k) C)) := by
    have h := rationalIntegral_scale m k rC
    rwa [mixedSet_scale_strace] at h
  have hA2 := invariant_mono m hbb' hA1
  have hC2 := invariant_mono m hbb' hC1
  have e1 := fullClass_strace_shift P m b A L k QA hA hQA (gA.nz L) rA hA1 hQA1
  have e2 := fullClass_strace_shift P m b C L k QC hC hQC (gC.nz L) rC hC1 hQC1
  have e3 := fullClass_strace_mono P m A (L + k) hbb' QA hA1 hA2 hQA1 (gA.nz _)
  have e4 := fullClass_strace_mono P m C (L + k) hbb' QC hC1 hC2 hQC1 (gC.nz _)
  have e5 := hAB (L + k) b' QA QB hA2 hB' hQA1 hQB rA1 (hN _ hLk)
  have e6 := hBC (L + k) b' QB QC hB' hC2 hQB hQC1 (hN _ hLk) rC1
  apply Linv_cancel (n * ((m : ℕ) * k))
  rw [← e1, ← e2, ← e3, ← e4, e5, e6]

/-- **The cofinal criterion.** -/
theorem teq_of_cofinal {r s : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)}
    {B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)} (gA : Good P m A) (gB : Good P m B)
    (h : ∀ (L : ℕ) (b0 : Fin n → ℕ), ∃ b : Fin n → ℕ, (∀ i, b0 i ≤ b i) ∧
      ∀ (QA : Finset (Fin r → ℤ)) (QB : Finset (Fin s → ℤ))
        (hA : Invariant m b (mixedSet (strace P L A))) (hB : Invariant m b (mixedSet (strace P L B)))
        (hQA : Covers m QA (mixedSet (strace P L A))) (hQB : Covers m QB (mixedSet (strace P L B))),
        RationalIntegral m (mixedSet (strace P L A)) → RationalIntegral m (mixedSet (strace P L B)) →
        fullClass m b QA (strace_definableOver P L A) hA hQA =
          fullClass m b QB (strace_definableOver P L B) hB hQB) :
    TEq P m A B := by
  intro L b0 QA QB hA hB hQA hQB rA rB
  obtain ⟨b, hb, heq⟩ := h L b0
  rw [← fullClass_strace_mono P m A L hb QA hA (invariant_mono m hb hA) hQA (gA.nz L),
    ← fullClass_strace_mono P m B L hb QB hB (invariant_mono m hb hB) hQB (gB.nz L)]
  exact heq QA QB _ _ hQA hQB rA rB

/-- Compatibility of a bijection with congruence, at cofinally many cutoffs, both ways. -/
def StepCompat {r s : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)}
    {B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)} (F : Map A B) : Prop :=
  ∀ (L : ℕ) (b0 : Fin n → ℕ), ∃ b : Fin n → ℕ, (∀ i, b0 i ≤ b i) ∧
    (∀ a a' : A, DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 → a.val.2 = a'.val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 ∧ (F a).val.2 = (F a').val.2) ∧
    (∀ a a' : A,
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 → (F a).val.2 = (F a').val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 ∧ a.val.2 = a'.val.2)

/-- **A compatible bijection preserves the truncation class.** -/
theorem teq_of_step {r s : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)}
    {B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)} (gA : Good P m A) (gB : Good P m B)
    (F : Map A B) (hbij : Function.Bijective F) (hF : StepCompat P m F) : TEq P m A B := by
  refine teq_of_cofinal P m gA gB fun L b0 => ?_
  obtain ⟨b, hb, h1, h2⟩ := hF L b0
  exact ⟨b, hb, fun QA QB hA hB hQA hQB rA rB =>
    fullClass_eq_of_ambient P m b L F hbij h1 h2 hA hB QA QB hQA hQB rA rB⟩

end DiamondIntegral.Section8.Truncation
