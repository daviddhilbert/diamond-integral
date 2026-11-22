import «section 8».TruncScale
import «section 6».Covariance

/-! One ambient bijection and the truncation classes of the scaled traces.

Let `F : A → B` be a bijection of sets definable over the base of Section 8 in the ambient model,
with `A, B` invariant at the radii `ρ_i = π^{b_i/m − L}` and `F`, `F⁻¹` respecting congruence at
these radii. Then the scaled traces `X = t^L A(ℂ((t)))`, `Y = t^L B(ℂ((t)))` have equal truncation
classes at the cutoffs `b/m` (`fullClass_eq_of_ambient`). The induced map of rational points is
`phiPt`; the thickened graph is assembled from the trace of the graph of `F` and the concrete
congruence set. -/

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
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells

local instance stepStructure : LRV.Structure Carrier := canonicalInterpret
local instance stepModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

/-! ### Congruence of scaled concrete points -/

/-- Congruence modulo `𝔪_{b/m}` of concrete tuples. -/
def CongrS {n : ℕ} (m : ℕ+) (b : Fin n → ℕ) (x x' : Fin n → Ser) : Prop :=
  ∀ i, ((lev m (b i) : ℚ) : WithTop ℚ) < ordS (x i - x' i)

theorem congr_iff_congrS {n : ℕ} (m : ℕ+) (b : Fin n → ℕ) (x x' : Fin n → Ser) :
    Congr m b x x' ↔ CongrS m b x x' := by
  refine forall_congr' fun i => ?_
  rw [lt_ordS_iff]
  exact forall_congr' fun γ => imp_congr_right fun _ => sub_eq_zero.symm

theorem congrS_symm {n : ℕ} {m : ℕ+} {b : Fin n → ℕ} {x x' : Fin n → Ser} (h : CongrS m b x x') :
    CongrS m b x' x := by
  intro i
  rw [← neg_sub, ordS_neg]
  exact h i

theorem congrS_trans {n : ℕ} {m : ℕ+} {b : Fin n → ℕ} {x x' x'' : Fin n → Ser} (h : CongrS m b x x')
    (h' : CongrS m b x' x'') : CongrS m b x x'' := by
  intro i
  have he : x i - x'' i = (x i - x' i) + (x' i - x'' i) := by ring
  rw [he]
  exact lt_of_lt_of_le (lt_min (h i) (h' i)) (ordS_add _ _)

theorem lt_ordS_tPow_mul (L : ℕ) (β : ℚ) (y : Ser) :
    ((β : ℚ) : WithTop ℚ) < ordS (tPow L * y) ↔ (((β - L : ℚ)) : WithTop ℚ) < ordS y := by
  rw [lt_ordS_iff, lt_ordS_iff]
  constructor
  · intro h δ hδ
    have := h (δ + L) (by linarith)
    rwa [cf_tPow_mul, add_sub_cancel_right] at this
  · intro h γ hγ
    rw [cf_tPow_mul]
    exact h _ (by linarith)

/-- Congruence of concrete tuples at `b/m − L`. -/
def CongrV {n : ℕ} (m : ℕ+) (b : Fin n → ℕ) (L : ℕ) (y y' : Fin n → Ser) : Prop :=
  ∀ i, (((lev m (b i) - L : ℚ)) : WithTop ℚ) < ordS (y i - y' i)

theorem congrS_iff_congrV {n : ℕ} (m : ℕ+) (b : Fin n → ℕ) (L : ℕ) (x x' : Fin n → Ser) :
    CongrS m b x x' ↔ CongrV m b L (fun i => tInv L * x i) (fun i => tInv L * x' i) := by
  refine forall_congr' fun i => ?_
  have he : x i - x' i = tPow L * (tInv L * x i - tInv L * x' i) := by
    rw [mul_sub, tPow_mul_tInv, tPow_mul_tInv]
  rw [he, lt_ordS_tPow_mul]

/-! ### Radii in the ambient model -/

variable (P : PuiseuxAmbient)

local notation "π" => uniformizerValue P

/-- The radii `π^{b_i/m − L}`. -/
def rad {n : ℕ} (m : ℕ+) (b : Fin n → ℕ) (L : ℕ) : Fin n → Values.Gamma (M := P.N) :=
  fun i => qpow π (lev m (b i) - L)

theorem congruent_e_iff {n : ℕ} (m : ℕ+) (b : Fin n → ℕ) (L : ℕ) (y y' : Fin n → Ser) :
    DiamondIntegral.Section6.Congruent (rad P m b L) (fun i => eVF P (y i)) (fun i => eVF P (y' i)) ↔
      CongrV m b L y y' := by
  refine forall_congr' fun i => ?_
  change (qpow π (lev m (b i) - L)).val < Values.vfValueHom (eVF P (y i) - eVF P (y' i)) ↔ _
  rw [← eVF_sub]
  exact lt_value_eVF_iff P _ _

variable {n l l' : ℕ} (m : ℕ+) (b : Fin n → ℕ) (L : ℕ)

/-- Invariance of an ambient set at the radii `ρ`. -/
def AmbInvariant (ρ : Fin n → Values.Gamma (M := P.N)) (A : Set (Mixed P.N n l)) : Prop :=
  ∀ a ∈ A, ∀ x, DiamondIntegral.Section6.Congruent ρ a.1 x → (x, a.2) ∈ A

/-- The scaled trace `t^L A(ℂ((t)))`. -/
abbrev strace (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) : Set (Fin (n + l) → Carrier) :=
  scaleRaw L (traceRaw P A)

theorem mem_strace (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (p : (Fin n → Ser) × (Fin l → RV)) :
    p ∈ mixedSet (strace P L A) ↔ ePoint P (unscaleP L p) ∈ A.carrier := by
  rw [mem_mixedSet_scale, mem_mixedSet_trace]

theorem strace_definableOver (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) :
    DefinableOver {c | baseCarrier c} (mixedSorts n l) (strace P L A) :=
  scaleRaw_definableOver L (traceRaw_definableOver P A)

/-- **Invariance of scaled traces.** -/
theorem invariant_strace (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hA : AmbInvariant P (rad P m b L) A.carrier) : Invariant m b (mixedSet (strace P L A)) := by
  intro x x' u hx hc
  rw [mem_strace] at hx ⊢
  have hcv := (congrS_iff_congrV m b L x x').mp ((congr_iff_congrS m b x x').mp hc)
  exact hA _ hx _ ((congruent_e_iff P m b L _ _).mpr hcv)

/-! ### The inverse of a bijective map -/

section Inverse

variable {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
  {B : DefSet (rawMixedSpace (M := P.N) n l') (P.G.real : Set P.N)}

/-- The inverse of a bijective definable map. -/
def invMap (F : Map A B) (hF : Function.Bijective F) : Map B A where
  toFun := (Equiv.ofBijective F hF).symm
  graph_definable := by
    refine (F.graph_definable.swap _ _).congr _ _ fun y x => ?_
    constructor
    · rintro ⟨a, ha, hb⟩
      refine ⟨F a, hb, ?_⟩
      rw [← ha]
      exact congrArg Subtype.val ((Equiv.ofBijective F hF).symm_apply_apply a)
    · rintro ⟨c, hc, hx⟩
      refine ⟨(Equiv.ofBijective F hF).symm c, hx, ?_⟩
      rw [← hc]
      exact congrArg Subtype.val ((Equiv.ofBijective F hF).apply_symm_apply c)

theorem invMap_apply (F : Map A B) (hF : Function.Bijective F) (a : A) : invMap P F hF (F a) = a :=
  (Equiv.ofBijective F hF).symm_apply_apply a

theorem apply_invMap (F : Map A B) (hF : Function.Bijective F) (c : B) : F (invMap P F hF c) = c :=
  (Equiv.ofBijective F hF).apply_symm_apply c

end Inverse

/-! ### The induced map on concrete points -/

theorem isRational_tPow {x : Ser} (hx : IsRational m x) : IsRational m (tPow L * x) := by
  intro γ hγ
  rw [cf_tPow_mul] at hγ
  obtain ⟨z, hz⟩ := hx _ hγ
  refine ⟨z + (m : ℕ) * L, ?_⟩
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  push_cast
  rw [add_div, ← hz]
  field_simp
  ring

theorem rationalPoint_scale {p : (Fin n → Ser) × (Fin l → RV)} (h : RationalPoint m p) :
    RationalPoint m (scaleP L p) :=
  ⟨fun i => isRational_tPow m L (h.1 i), h.2⟩

theorem rationalPoint_unscale {p : (Fin n → Ser) × (Fin l → RV)} (h : RationalPoint m p) :
    RationalPoint m (unscaleP L p) :=
  ⟨fun i => isRational_tInv m L (h.1 i), h.2⟩

section Phi

variable {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
  {B : DefSet (rawMixedSpace (M := P.N) n l') (P.G.real : Set P.N)} (F : Map A B)

/-- **The induced map** `p ↦ t^L F(t^{-L} p)` on concrete points. -/
def phiPt (p : (Fin n → Ser) × (Fin l → RV)) : (Fin n → Ser) × (Fin l' → RV) :=
  if h : ePoint P (unscaleP L p) ∈ A.carrier then
    scaleP L (Classical.choose (exists_concrete_image P F (unscaleP L p) h))
  else (fun _ => 0, fun _ => none)

theorem phiPt_spec {p : (Fin n → Ser) × (Fin l → RV)} (h : ePoint P (unscaleP L p) ∈ A.carrier) :
    (F ⟨_, h⟩).val = ePoint P (unscaleP L (phiPt P L F p)) := by
  simp only [phiPt, h, ↓reduceDIte, unscaleP_scaleP]
  exact Classical.choose_spec (exists_concrete_image P F (unscaleP L p) h)

theorem phiPt_eq {p : (Fin n → Ser) × (Fin l → RV)} (h : ePoint P (unscaleP L p) ∈ A.carrier)
    {p' : (Fin n → Ser) × (Fin l' → RV)} (hp' : (F ⟨_, h⟩).val = ePoint P (unscaleP L p')) :
    phiPt P L F p = p' := by
  have h1 := (phiPt_spec P L F h).symm.trans hp'
  have h2 := ePoint_injective P h1
  rw [← scaleP_unscaleP L (phiPt P L F p), h2, scaleP_unscaleP]

theorem phiPt_mem {p : (Fin n → Ser) × (Fin l → RV)} (hp : p ∈ mixedSet (strace P L A)) :
    phiPt P L F p ∈ mixedSet (strace P L B) := by
  rw [mem_strace] at hp ⊢
  rw [← phiPt_spec P L F hp]
  exact (F ⟨_, hp⟩).property

theorem phiPt_rational {p : (Fin n → Ser) × (Fin l → RV)} (hp : p ∈ mixedSet (strace P L A))
    (hr : RationalPoint m p) : RationalPoint m (phiPt P L F p) := by
  rw [mem_strace] at hp
  have h := concrete_image_rational P F m (unscaleP L p) hp _ (phiPt_spec P L F hp)
    (rationalPoint_unscale m L hr)
  have h2 := rationalPoint_scale m L h
  rwa [scaleP_unscaleP] at h2

theorem phiPt_congr (hF : ∀ a a' : A, DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 →
      a.val.2 = a'.val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 ∧ (F a).val.2 = (F a').val.2)
    {p p' : (Fin n → Ser) × (Fin l → RV)} (hp : p ∈ mixedSet (strace P L A))
    (hp' : p' ∈ mixedSet (strace P L A)) (hc : CongrS m b p.1 p'.1) (hl : p.2 = p'.2) :
    CongrS m b (phiPt P L F p).1 (phiPt P L F p').1 ∧ (phiPt P L F p).2 = (phiPt P L F p').2 := by
  rw [mem_strace] at hp hp'
  have hcv := (congruent_e_iff P m b L _ _).mpr ((congrS_iff_congrV m b L _ _).mp hc)
  have hl' : (ePoint P (unscaleP L p)).2 = (ePoint P (unscaleP L p')).2 := by
    change (fun j => eRV P (p.2 j)) = fun j => eRV P (p'.2 j)
    rw [hl]
  obtain ⟨h1, h2⟩ := hF ⟨_, hp⟩ ⟨_, hp'⟩ hcv hl'
  rw [phiPt_spec P L F hp, phiPt_spec P L F hp'] at h1 h2
  refine ⟨(congrS_iff_congrV m b L _ _).mpr ((congruent_e_iff P m b L _ _).mp h1), ?_⟩
  funext j
  have h3 := congrArg Subtype.val (congrFun h2 j)
  exact Sum.inr_injective (P.e.injective h3)

theorem phiPt_congr_inv (hG : ∀ a a' : A,
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 → (F a).val.2 = (F a').val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 ∧ a.val.2 = a'.val.2)
    {p p' : (Fin n → Ser) × (Fin l → RV)} (hp : p ∈ mixedSet (strace P L A))
    (hp' : p' ∈ mixedSet (strace P L A)) (hc : CongrS m b (phiPt P L F p).1 (phiPt P L F p').1)
    (hl : (phiPt P L F p).2 = (phiPt P L F p').2) : CongrS m b p.1 p'.1 ∧ p.2 = p'.2 := by
  rw [mem_strace] at hp hp'
  have hcv : DiamondIntegral.Section6.Congruent (rad P m b L) (ePoint P (unscaleP L (phiPt P L F p))).1
      (ePoint P (unscaleP L (phiPt P L F p'))).1 :=
    (congruent_e_iff P m b L _ _).mpr ((congrS_iff_congrV m b L _ _).mp hc)
  have hl' : (ePoint P (unscaleP L (phiPt P L F p))).2 = (ePoint P (unscaleP L (phiPt P L F p'))).2 := by
    change (fun j => eRV P ((phiPt P L F p).2 j)) = fun j => eRV P ((phiPt P L F p').2 j)
    rw [hl]
  rw [← phiPt_spec P L F hp, ← phiPt_spec P L F hp'] at hcv hl'
  obtain ⟨h1, h2⟩ := hG ⟨_, hp⟩ ⟨_, hp'⟩ hcv hl'
  refine ⟨(congrS_iff_congrV m b L _ _).mpr ((congruent_e_iff P m b L _ _).mp h1), ?_⟩
  funext j
  have h3 := congrArg Subtype.val (congrFun h2 j)
  exact Sum.inr_injective (P.e.injective h3)

theorem phiPt_surj (hbij : Function.Bijective F) {p' : (Fin n → Ser) × (Fin l' → RV)}
    (hp' : p' ∈ mixedSet (strace P L B)) (hr : RationalPoint m p') :
    ∃ p ∈ mixedSet (strace P L A), RationalPoint m p ∧ phiPt P L F p = p' := by
  rw [mem_strace] at hp'
  obtain ⟨p0, hp0⟩ := exists_concrete_image P (invMap P F hbij) (unscaleP L p') hp'
  have hr0 := concrete_image_rational P (invMap P F hbij) m (unscaleP L p') hp' p0 hp0
    (rationalPoint_unscale m L hr)
  have hmem : ePoint P (unscaleP L (scaleP L p0)) ∈ A.carrier := by
    rw [unscaleP_scaleP, ← hp0]
    exact (invMap P F hbij ⟨_, hp'⟩).property
  refine ⟨scaleP L p0, (mem_strace P L A _).mpr hmem, rationalPoint_scale m L hr0, ?_⟩
  apply phiPt_eq P L F hmem
  have he : (⟨ePoint P (unscaleP L (scaleP L p0)), hmem⟩ : A) = invMap P F hbij ⟨_, hp'⟩ := by
    apply Subtype.ext
    change ePoint P (unscaleP L (scaleP L p0)) = _
    rw [unscaleP_scaleP, hp0]
  rw [he, apply_invMap]

end Phi

/-! ### From the pair layout to the mixed layout -/

section Layout

/-- The pair layout `(x, u, x', u')` inside the mixed layout `(x, x', u, u')`. -/
def pairPerm : Fin ((n + l) + (n + l')) → Fin ((n + n) + (l + l')) :=
  Fin.append (Fin.append (fun i => Fin.castAdd (l + l') (Fin.castAdd n i))
      (fun j => Fin.natAdd (n + n) (Fin.castAdd l' j)))
    (Fin.append (fun i => Fin.castAdd (l + l') (Fin.natAdd n i))
      (fun j => Fin.natAdd (n + n) (Fin.natAdd l j)))

theorem mixedRaw_join_perm (p : (Fin n → Ser) × (Fin l → RV)) (p' : (Fin n → Ser) × (Fin l' → RV)) :
    mixedRaw (joinP p p') ∘ pairPerm = Fin.append (mixedRaw p) (mixedRaw p') := by
  funext k
  refine Fin.addCases (fun a => ?_) (fun a => ?_) k
  · refine Fin.addCases (fun c => ?_) (fun c => ?_) a <;>
      simp only [pairPerm, mixedRaw, joinP, Fin.append_left, Fin.append_right, Function.comp_apply]
  · refine Fin.addCases (fun c => ?_) (fun c => ?_) a <;>
      simp only [pairPerm, mixedRaw, joinP, Fin.append_left, Fin.append_right, Function.comp_apply]

/-- A set in the pair layout, moved to the mixed layout. -/
def fromPair (Wp : Set (Fin ((n + l) + (n + l')) → Carrier)) : Set (Fin ((n + n) + (l + l')) → Carrier) :=
  {z | (∀ i, sortEval (mixedSorts (n + n) (l + l') i) (z i)) ∧ z ∘ pairPerm ∈ Wp}

theorem fromPair_definableOver {Wp : Set (Fin ((n + l) + (n + l')) → Carrier)}
    (hWp : {c | baseCarrier c}.Definable LRV Wp) :
    DefinableOver {c | baseCarrier c} (mixedSorts (n + n) (l + l')) (fromPair Wp) := by
  refine (definableOver_iff_normalized_raw _ _ _).mpr ⟨?_, fun z hz i => hz.1 i⟩
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical]
  exact (sorted_definable _).inter (hWp.preimage_comp pairPerm)

theorem mem_fromPair (Wp : Set (Fin ((n + l) + (n + l')) → Carrier)) (p : (Fin n → Ser) × (Fin l → RV))
    (p' : (Fin n → Ser) × (Fin l' → RV)) :
    joinP p p' ∈ mixedSet (fromPair Wp) ↔ Fin.append (mixedRaw p) (mixedRaw p') ∈ Wp := by
  change (_ ∧ mixedRaw (joinP p p') ∘ pairPerm ∈ Wp) ↔ _
  rw [mixedRaw_join_perm]
  exact ⟨fun h => h.2, fun h => ⟨mixedRaw_sorted _, h⟩⟩

end Layout

/-! ### The thickened graph -/

section Thickened

variable {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
  {B : DefSet (rawMixedSpace (M := P.N) n l') (P.G.real : Set P.N)} (F : Map A B)

/-- The scaled graph of `F`, as raw tuples of the concrete model. -/
def sgraph : Set (Fin ((n + l) + (n + l')) → Carrier) :=
  {g | (∀ i, sortEval (mixedSorts n l i) (g (Fin.castAdd (n + l') i))) ∧
    (∀ i, sortEval (mixedSorts n l' i) (g (Fin.natAdd (n + l) i))) ∧
    P.e ∘ Fin.append (unscaleRaw L (fun i => g (Fin.castAdd (n + l') i)))
      (unscaleRaw L (fun i => g (Fin.natAdd (n + l) i))) ∈ graphRaw P F}

theorem mem_sgraph (p : (Fin n → Ser) × (Fin l → RV)) (p' : (Fin n → Ser) × (Fin l' → RV)) :
    Fin.append (mixedRaw p) (mixedRaw p') ∈ sgraph P L F ↔
      ∃ h : ePoint P (unscaleP L p) ∈ A.carrier, (F ⟨_, h⟩).val = ePoint P (unscaleP L p') := by
  have h1 : (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.castAdd (n + l') i)) = mixedRaw p :=
    funext fun i => Fin.append_left _ _ i
  have h2 : (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.natAdd (n + l) i)) = mixedRaw p' :=
    funext fun i => Fin.append_right _ _ i
  have he : ∀ (u : Fin (n + l) → Carrier) (v : Fin (n + l') → Carrier),
      P.e ∘ Fin.append u v = Fin.append (P.e ∘ u) (P.e ∘ v) := by
    intro u v
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
  change (_ ∧ _ ∧ P.e ∘ Fin.append (unscaleRaw L (fun i => Fin.append (mixedRaw p) (mixedRaw p')
    (Fin.castAdd (n + l') i))) (unscaleRaw L (fun i => Fin.append (mixedRaw p) (mixedRaw p')
      (Fin.natAdd (n + l) i))) ∈ graphRaw P F) ↔ _
  rw [h1, h2, unscaleRaw_mixedRaw, unscaleRaw_mixedRaw, he, mem_graphRaw_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨fun i => by rw [Fin.append_left]; exact mixedRaw_sorted p i,
    fun i => by rw [Fin.append_right]; exact mixedRaw_sorted p' i, h⟩⟩

theorem sgraph_definable : {c | baseCarrier c}.Definable LRV (sgraph P L F) := by
  have hs1 := (sorted_definable (mixedSorts n l)).preimage_comp (Fin.castAdd (n + l') : Fin (n + l) → _)
  have hs2 := (sorted_definable (mixedSorts n l')).preimage_comp (Fin.natAdd (n + l) : Fin (n + l') → _)
  have hmap : {c : Carrier | baseCarrier c}.DefinableMap LRV
      (fun g : Fin ((n + l) + (n + l')) → Carrier => Fin.append (unscaleRaw L (fun i => g (Fin.castAdd (n + l') i)))
        (unscaleRaw L (fun i => g (Fin.natAdd (n + l) i)))) := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.append_left]
      exact (unscaleRaw_definable L i).comp (fun a => Set.DefinableFun.proj LRV)
    · simp only [Fin.append_right]
      exact (unscaleRaw_definable L j).comp (fun a => Set.DefinableFun.proj LRV)
  have hg := (graphTrace_definable P F).preimage_map hmap
  convert hs1.inter (hs2.inter hg) using 1
  ext g
  exact Iff.rfl

/-- The thickened graph in the pair layout. -/
def thickPair : Set (Fin ((n + l) + (n + l')) → Carrier) :=
  {z | ∃ w : Fin (n + l') → Carrier, Fin.append (fun i => z (Fin.castAdd (n + l') i)) w ∈ sgraph P L F ∧
    Fin.append w (fun i => z (Fin.natAdd (n + l) i)) ∈ congrSet (k := l') m b ∧
    (fun i => z (Fin.natAdd (n + l) i)) ∈ strace P L B}

theorem mem_thickPair (p : (Fin n → Ser) × (Fin l → RV)) (p' : (Fin n → Ser) × (Fin l' → RV)) :
    Fin.append (mixedRaw p) (mixedRaw p') ∈ thickPair P m b L F ↔
      p ∈ mixedSet (strace P L A) ∧ p' ∈ mixedSet (strace P L B) ∧
        CongrS m b (phiPt P L F p).1 p'.1 ∧ (phiPt P L F p).2 = p'.2 := by
  have h1 : (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.castAdd (n + l') i)) = mixedRaw p :=
    funext fun i => Fin.append_left _ _ i
  have h2 : (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.natAdd (n + l) i)) = mixedRaw p' :=
    funext fun i => Fin.append_right _ _ i
  change (∃ w, Fin.append (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.castAdd (n + l') i)) w ∈
    sgraph P L F ∧ Fin.append w (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.natAdd (n + l) i)) ∈
      congrSet (k := l') m b ∧
    (fun i => Fin.append (mixedRaw p) (mixedRaw p') (Fin.natAdd (n + l) i)) ∈ strace P L B) ↔ _
  rw [h1, h2]
  constructor
  · rintro ⟨w, hg, hc, hy⟩
    have hsort : ∀ i, sortEval (mixedSorts n l' i) (w i) := by
      intro i
      have := hg.2.1 i
      rwa [Fin.append_right] at this
    rw [← mixedRaw_decodeRaw hsort] at hg hc
    obtain ⟨hA, hF⟩ := (mem_sgraph P L F p _).mp hg
    have hphi := phiPt_eq P L F hA hF
    obtain ⟨hc1, hc2⟩ := (mem_congrSet_iff m b _ _).mp hc
    refine ⟨(mem_strace P L A p).mpr hA, hy, ?_, ?_⟩
    · rw [hphi]
      exact hc1
    · rw [hphi]
      exact funext hc2
  · rintro ⟨hA, hB, hc, hl⟩
    rw [mem_strace] at hA
    refine ⟨mixedRaw (phiPt P L F p), (mem_sgraph P L F p _).mpr ⟨hA, phiPt_spec P L F hA⟩,
      (mem_congrSet_iff m b _ _).mpr ⟨hc, fun j => congrFun hl j⟩, hB⟩

theorem thickPair_definable (hB : {c | baseCarrier c}.Definable LRV (strace P L B)) :
    {c | baseCarrier c}.Definable LRV (thickPair P m b L F) := by
  let jG : Fin ((n + l) + (n + l')) → Fin (((n + l) + (n + l')) + (n + l')) :=
    Fin.append (fun a => Fin.castAdd (n + l') (Fin.castAdd (n + l') a)) (fun c => Fin.natAdd ((n + l) + (n + l')) c)
  let jC : Fin ((n + l') + (n + l')) → Fin (((n + l) + (n + l')) + (n + l')) :=
    Fin.append (fun c => Fin.natAdd ((n + l) + (n + l')) c) (fun c => Fin.castAdd (n + l') (Fin.natAdd (n + l) c))
  let jY : Fin (n + l') → Fin (((n + l) + (n + l')) + (n + l')) :=
    fun c => Fin.castAdd (n + l') (Fin.natAdd (n + l) c)
  let D : Set (Fin (((n + l) + (n + l')) + (n + l')) → Carrier) :=
    {v | v ∘ jG ∈ sgraph P L F ∧ v ∘ jC ∈ congrSet (k := l') m b ∧ v ∘ jY ∈ strace P L B}
  have hD : {c | baseCarrier c}.Definable LRV D :=
    ((sgraph_definable P L F).preimage_comp jG).inter
      (((congrSet_definable m b).preimage_comp jC).inter (hB.preimage_comp jY))
  have he : thickPair P m b L F = (fun v => v ∘ Fin.castAdd (n + l')) '' D := by
    ext z
    constructor
    · rintro ⟨w, hg, hc, hy⟩
      refine ⟨Fin.append z w, ⟨?_, ?_, ?_⟩, ?_⟩
      · convert hg using 1
        funext k
        refine Fin.addCases (fun a => ?_) (fun c => ?_) k <;>
          simp only [jG, Fin.append_left, Fin.append_right, Function.comp_apply]
      · convert hc using 1
        funext k
        refine Fin.addCases (fun a => ?_) (fun c => ?_) k <;>
          simp only [jC, Fin.append_left, Fin.append_right, Function.comp_apply]
      · convert hy using 1
        funext k
        simp [jY, Fin.append_left]
      · funext k
        simp [Fin.append_left]
    · rintro ⟨v, ⟨hg, hc, hy⟩, rfl⟩
      refine ⟨fun c => v (Fin.natAdd ((n + l) + (n + l')) c), ?_, ?_, ?_⟩
      · convert hg using 1
        funext k
        refine Fin.addCases (fun a => ?_) (fun c => ?_) k <;>
          simp only [jG, Fin.append_left, Fin.append_right, Function.comp_apply]
      · convert hc using 1
        funext k
        refine Fin.addCases (fun a => ?_) (fun c => ?_) k <;>
          simp only [jC, Fin.append_left, Fin.append_right, Function.comp_apply]
      · convert hy using 1
        rfl
  rw [he]
  exact hD.image_comp (Fin.castAdd (n + l'))

end Thickened

/-! ### The step lemma -/

section Step

variable {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
  {B : DefSet (rawMixedSpace (M := P.N) n l') (P.G.real : Set P.N)} (F : Map A B)

theorem congrS_left {x x' : Fin (n + n) → Ser} (h : CongrS m (Fin.append b b) x x') :
    CongrS m b (fun j => x (Fin.castAdd n j)) (fun j => x' (Fin.castAdd n j)) := by
  intro j
  have := h (Fin.castAdd n j)
  rwa [Fin.append_left] at this

theorem congrS_right {x x' : Fin (n + n) → Ser} (h : CongrS m (Fin.append b b) x x') :
    CongrS m b (fun j => x (Fin.natAdd n j)) (fun j => x' (Fin.natAdd n j)) := by
  intro j
  have := h (Fin.natAdd n j)
  rwa [Fin.append_right] at this

theorem congrS_refl (x : Fin n → Ser) : CongrS m b x x := by
  intro i
  rw [sub_self, ordS_zero]
  exact WithTop.coe_lt_top _

theorem thick_invariant
    (hF : ∀ a a' : A, DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 → a.val.2 = a'.val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 ∧ (F a).val.2 = (F a').val.2)
    (hXinv : Invariant m b (mixedSet (strace P L A))) (hYinv : Invariant m b (mixedSet (strace P L B))) :
    Invariant m (Fin.append b b) (mixedSet (fromPair (thickPair P m b L F))) := by
  intro x x' u hx hc
  have hcS := (congr_iff_congrS m _ x x').mp hc
  rw [← join_left_right (x, u)] at hx
  rw [← join_left_right (x', u)]
  rw [mem_fromPair, mem_thickPair] at hx ⊢
  obtain ⟨hp, hp', hc0, hl0⟩ := hx
  have hp1 : leftP (k' := l') (x', u) ∈ mixedSet (strace P L A) :=
    hXinv _ _ _ hp ((congr_iff_congrS m b _ _).mpr (congrS_left m b hcS))
  have hp1' : rightP (k := l) (x', u) ∈ mixedSet (strace P L B) :=
    hYinv _ _ _ hp' ((congr_iff_congrS m b _ _).mpr (congrS_right m b hcS))
  obtain ⟨h1, h2⟩ := phiPt_congr P m b L F hF hp hp1 (congrS_left m b hcS) rfl
  refine ⟨hp1, hp1', congrS_trans (congrS_symm h1) (congrS_trans hc0 (congrS_right m b hcS)), ?_⟩
  rw [← h2, hl0]
  rfl

/-- **One ambient step preserves the truncation class.** Let `F : A → B` be a bijection of sets
definable over the base of Section 8, invariant at the radii `ρ_i = π^{b_i/m − L}`, such that `F` and
`F⁻¹` respect congruence at `ρ` (with equal labels). If the rational points of the scaled traces are
integral, the scaled traces have the same normalized truncation class at the cutoffs `b/m`. -/
theorem fullClass_eq_of_ambient (hbij : Function.Bijective F)
    (hF : ∀ a a' : A, DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 → a.val.2 = a'.val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 ∧ (F a).val.2 = (F a').val.2)
    (hG : ∀ a a' : A,
      DiamondIntegral.Section6.Congruent (rad P m b L) (F a).val.1 (F a').val.1 → (F a).val.2 = (F a').val.2 →
      DiamondIntegral.Section6.Congruent (rad P m b L) a.val.1 a'.val.1 ∧ a.val.2 = a'.val.2)
    (hXinv : Invariant m b (mixedSet (strace P L A))) (hYinv : Invariant m b (mixedSet (strace P L B)))
    (QX : Finset (Fin l → ℤ)) (QY : Finset (Fin l' → ℤ))
    (hQX : Covers m QX (mixedSet (strace P L A))) (hQY : Covers m QY (mixedSet (strace P L B)))
    (hlowX : RationalIntegral m (mixedSet (strace P L A))) (hlowY : RationalIntegral m (mixedSet (strace P L B))) :
    fullClass m b QX (strace_definableOver P L A) hXinv hQX =
      fullClass m b QY (strace_definableOver P L B) hYinv hQY := by
  have hBd : {c | baseCarrier c}.Definable LRV (strace P L B) := by
    obtain ⟨h, -⟩ := (definableOver_iff_normalized_raw _ _ _).mp (strace_definableOver P L B)
    rwa [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at h
  have hRI : ∀ {p : (Fin n → Ser) × (Fin l → RV)}, p ∈ mixedSet (strace P L A) → RI m p →
      RI m (phiPt P L F p) := by
    intro p hp hr
    have hrat := phiPt_rational P m L F hp ⟨fun i => (hr.1 i).1, hr.2⟩
    exact ⟨fun i => ⟨hrat.1 i, hlowY _ (phiPt_mem P L F hp) hrat.1 i⟩, hrat.2⟩
  refine fullClass_eq_of_thickened m b QX QY _ _ hXinv hYinv hQX hQY (phiPt P L F)
    (fun p hp hr => ⟨phiPt_mem P L F hp, hRI hp hr⟩) ?_ ?_ (fromPair (thickPair P m b L F))
    (fromPair_definableOver (thickPair_definable P m b L F hBd)) (thick_invariant P m b L F hF hXinv hYinv) ?_ ?_
  · intro p' hp' hr'
    obtain ⟨p, hp, hrat, rfl⟩ := phiPt_surj P m L F hbij hp' ⟨fun i => (hr'.1 i).1, hr'.2⟩
    exact ⟨p, hp, ⟨fun i => ⟨hrat.1 i, hlowX _ hp hrat.1 i⟩, hrat.2⟩, rfl⟩
  · intro p hp p' hp' hr hr'
    rw [truncOf_eq_iff m b hr hr', truncOf_eq_iff m b (hRI hp hr) (hRI hp' hr')]
    constructor
    · rintro ⟨hc, hl⟩
      obtain ⟨h1, h2⟩ := phiPt_congr P m b L F hF hp hp' hc (funext hl)
      exact ⟨h1, fun j => congrFun h2 j⟩
    · rintro ⟨hc, hl⟩
      obtain ⟨h1, h2⟩ := phiPt_congr_inv P m b L F hG hp hp' hc (funext hl)
      exact ⟨h1, fun j => congrFun h2 j⟩
  · intro p p' hW hr hr'
    rw [mem_fromPair, mem_thickPair] at hW
    obtain ⟨hp, hp', hc, hl⟩ := hW
    refine ⟨hp, hp', (truncOf_eq_iff m b hr' (hRI hp hr)).mpr ⟨congrS_symm hc, fun j => (congrFun hl j).symm⟩⟩
  · intro p hp hr
    rw [mem_fromPair, mem_thickPair]
    exact ⟨hp, phiPt_mem P L F hp, congrS_refl m b _, rfl⟩

end Step

end DiamondIntegral.Section8.Truncation
