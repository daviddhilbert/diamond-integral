import «section 8».LiftHm

/-! The truncation of the scaled lift of a measured RV object.

For a point `(x, t)` of `t^L 𝕃U` with `rv(t^{-L} x_i) = f_i(t)` of value `z_i/m`, the truncation
coordinates of `x_i` vanish below the index `z_i + mL`, equal the leading coefficient of `f_i(t)` at
that index, and are free above it. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells

local instance liftTruncStructure : LRV.Structure Carrier := canonicalInterpret
local instance liftTruncModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-! ### Leading terms -/

theorem rv_coeffs {y : Ser} {u : RationalRVUnits ℂ} (h : rvOfField y = some u) :
    (∀ δ < Multiplicative.toAdd u.1, cf y δ = 0) ∧ cf y (Multiplicative.toAdd u.1) = (u.2 : ℂ) := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [rvOfField_zero] at h
    cases h
  rw [rvOfField_of_ne hy] at h
  have h' := Option.some_injective _ h
  have hu1 : Multiplicative.toAdd u.1 = (y : HahnSeries ℚ ℂ).order := by
    rw [← h']
    rfl
  have hu2 : (u.2 : ℂ) = (y : HahnSeries ℚ ℂ).leadingCoeff := by
    rw [← h']
    rfl
  have hy' : (y : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  refine ⟨fun δ hδ => ?_, ?_⟩
  · rw [hu1] at hδ
    exact coeff_eq_zero_of_lt_order hδ
  · rw [hu1, hu2, leadingCoeff_eq]
    rfl

theorem rv_of_coeffs {y : Ser} {γ : ℚ} {c : ℂˣ} (h0 : ∀ δ < γ, cf y δ = 0) (h1 : cf y γ = c) :
    rvOfField y = some (Multiplicative.ofAdd γ, c) := by
  have hc : (y : HahnSeries ℚ ℂ).coeff γ ≠ 0 := by
    change cf y γ ≠ 0
    rw [h1]
    exact c.ne_zero
  have hy' : (y : HahnSeries ℚ ℂ) ≠ 0 := ne_zero_of_coeff_ne_zero hc
  have hy : y ≠ 0 := fun h => hy' (congrArg Subtype.val h)
  have hord : (y : HahnSeries ℚ ℂ).order = γ := by
    apply le_antisymm (order_le_of_coeff_ne_zero hc)
    by_contra hlt
    push Not at hlt
    have h2 := h0 _ hlt
    change (y : HahnSeries ℚ ℂ).coeff _ = 0 at h2
    rw [← leadingCoeff_eq] at h2
    exact leadingCoeff_ne_zero.mpr hy' h2
  rw [rvOfField_of_ne hy]
  congr 2
  apply Units.ext
  change (y : HahnSeries ℚ ℂ).leadingCoeff = c
  rw [leadingCoeff_eq, hord]
  exact h1

/-! ### Truncation coordinates of lift points -/

variable (P : PuiseuxAmbient) {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := P.N) (P.G.real : Set P.N) n)
variable (m : ℕ+) (L : ℕ) (b : Fin n → ℕ)

/-- The index of the leading coefficient in coordinate `i` for the value pattern `z`. -/
def lead (z : Fin n → ℤ) (i : Fin n) : ℕ := (z i + (m : ℕ) * L).toNat

theorem lev_lead (z : Fin n → ℤ) (i : Fin n) (hz : 0 ≤ z i + (m : ℕ) * L) :
    lev m (lead m L z i) = (z i : ℚ) / (m : ℕ) + L := by
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  rw [lev, lead]
  have h1 : (((z i + (m : ℕ) * L).toNat : ℕ) : ℚ) = ((z i + (m : ℕ) * L : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  rw [h1]
  push_cast
  field_simp

theorem lev_lt_lead_iff (z : Fin n → ℤ) (i : Fin n) (hz : 0 ≤ z i + (m : ℕ) * L) (j : ℕ) :
    lev m j - L < (z i : ℚ) / (m : ℕ) ↔ j < lead m L z i := by
  have h := lev_lead m L z i hz
  have e : (z i : ℚ) / (m : ℕ) = lev m (lead m L z i) - L := by linarith
  rw [e, sub_lt_sub_iff_right]
  exact (StrictMono.lt_iff_lt (fun _ _ h => lev_lt_lev (m := m) h))

/-- **Truncation coordinates of a point of the scaled lift.** -/
theorem cf_lift (x : Fin n → Ser) {u : Fin n → RationalRVUnits ℂ}
    (hu : ∀ i, rvOfField (tInv L * x i) = some (u i)) (z : Fin n → ℤ)
    (hz : ∀ i, Multiplicative.toAdd (u i).1 = (z i : ℚ) / (m : ℕ)) (hz0 : ∀ i, 0 ≤ z i + (m : ℕ) * L)
    (i : Fin n) (j : ℕ) :
    (j < lead m L z i → cf (x i) (lev m j) = 0) ∧ (j = lead m L z i → cf (x i) (lev m j) = ((u i).2 : ℂ)) := by
  obtain ⟨h0, h1⟩ := rv_coeffs (hu i)
  have he : x i = tPow L * (tInv L * x i) := (tPow_mul_tInv L _).symm
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · rw [he, cf_tPow_mul]
    apply h0
    rw [hz i]
    exact (lev_lt_lead_iff m L z i (hz0 i) j).mpr hj
  · rw [he, cf_tPow_mul, hj, lev_lead m L z i (hz0 i), add_sub_cancel_right, ← hz i]
    exact h1

/-! ### Products of residue lines -/

/-- The free truncation indices for the value pattern `z`. -/
def Free (z : Fin n → ℤ) : Type := {kk : Idx b // lead m L z kk.1 < (kk.2 : ℕ)}

instance (z : Fin n → ℤ) : Fintype (Free m L b z) := by
  unfold Free
  infer_instance

/-- The number of free truncation indices. -/
abbrev nfree (z : Fin n → ℤ) : ℕ := Fintype.card (Free m L b z)

/-- An enumeration of the free indices. -/
def εf (z : Fin n → ℤ) : Free m L b z ≃ Fin (nfree m L b z) := Fintype.equivFin _

/-- The weights of the free coordinates. -/
def wtf (z : Fin n → ℤ) : Fin (nfree m L b z) → ℚ := fun s => lev m ((εf m L b z).symm s).val.2

/-- **The product of the residue lines of the free coordinates.** -/
def Lines (z : Fin n → ℤ) : DefSet (rawRVSpace (M := Carrier) (nfree m L b z)) {c | baseCarrier c} :=
  rationalDescendedSet (wtf m L b z) Set.univ Set.definable_univ

theorem Lines_finite (z : Fin n → ℤ) :
    (Set.range (fun u : Lines m L b z => fun i => Values.vrv (u.val i))).Finite :=
  rationalDescendedSet_finite_values _ _ _

theorem mem_Lines (z : Fin n → ℤ) (r : Fin (nfree m L b z) → CanonicalRV.RVSort Carrier) :
    r ∈ (Lines m L b z).carrier ↔ ∀ s, taggedRVEquiv (r s) ∈ Line (wtf m L b z s) := by
  rw [Lines, rationalDescent_mem_image _ _ _ (fun _ _ => Iff.rfl)]
  constructor
  · rintro ⟨x, -, rfl⟩ s
    exact coeffRV_mem_line _ _
  · intro h
    refine ⟨fun s => lineCoeff (taggedRVEquiv (r s)), Set.mem_univ _, funext fun s => ?_⟩
    apply taggedRVEquiv.injective
    change linePoint (wtf m L b z s) (lineCoeff (taggedRVEquiv (r s))) = taggedRVEquiv (r s)
    exact coeffRV_lineCoeff (h s)

theorem Lines_theta (z : Fin n → ℤ) :
    theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
      (resSetClass canonicalInterpret_isCanonical (Lines m L b z) (Lines_finite m L b z))) =
      modifiedAffineLineClass ^ nfree m L b z := by
  have h := theta_diagonalRESClass (DiagonalConstructible.affineSpace (wtf m L b z))
  rw [dcClass_affineSpace] at h
  exact h

/-! ### Truncation pieces over a set of labels -/

variable {k : ℕ}

/-- The part of `T` whose labels lie in `D`. -/
def Tpiece (T : DefSet (rawRVSpace (M := Carrier) (Kt b k)) {c | baseCarrier c})
    (D : DefSet (rawRVSpace (M := Carrier) k) {c | baseCarrier c}) :
    DefSet (rawRVSpace (M := Carrier) (Kt b k)) {c | baseCarrier c} where
  carrier := {r | r ∈ T.carrier ∧ (fun j => r (εt b k (.inr j))) ∈ D.carrier}
  definable := by
    have hT : {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) (Kt b k)).preimage T.carrier) :=
      T.definable
    have hD : {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) k).preimage D.carrier) :=
      D.definable
    change {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) (Kt b k)).preimage _)
    convert hT.inter (hD.preimage_comp (fun j => εt b k (.inr j))) using 1
    ext z
    rw [Set.mem_inter_iff, Set.mem_preimage, rawRV_preimage_iff, rawRV_preimage_iff, rawRV_preimage_iff]
    constructor
    · rintro ⟨r, ⟨hr, hrD⟩, rfl⟩
      exact ⟨⟨r, hr, rfl⟩, ⟨_, hrD, rfl⟩⟩
    · rintro ⟨⟨r, hr, rfl⟩, ⟨d, hd, hdz⟩⟩
      refine ⟨r, ⟨hr, ?_⟩, rfl⟩
      have he : d = fun j => r (εt b k (.inr j)) := rvValues_injective hdz
      rw [← he]
      exact hd

theorem Tpiece_finite (T : DefSet (rawRVSpace (M := Carrier) (Kt b k)) {c | baseCarrier c})
    (hT : (Set.range (fun u : T => fun i => Values.vrv (u.val i))).Finite)
    (D : DefSet (rawRVSpace (M := Carrier) k) {c | baseCarrier c}) :
    (Set.range (fun u : Tpiece b T D => fun i => Values.vrv (u.val i))).Finite := by
  refine hT.subset ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨u.val, u.property.1⟩, rfl⟩

/-! ### The data of a point over a label piece -/

section Piece

open DiamondIntegral.Section7.ChartOfMeasured

local notation "π" => uniformizerValue P

/-- A label piece: the concrete label tuples with lattice labels, weight `w` and value pattern `z`. -/
def IsPiece (w : Values.Gamma (M := P.N)) (z : Fin n → ℤ) (D : DefSet (rawRVSpace (M := Carrier) U.object.arity) {c | baseCarrier c}) :
    Prop :=
  ∀ x, x ∈ D.carrier ↔ (fun i => P.e (x i).val) ∈ latticeFibre P (chartOf P.hc U) m w ∧
    ∀ i, codeValue ((chartOf P.hc U).coordinate (fun i => P.e (x i).val) i) = qpow π ((z i : ℚ) / (m : ℕ))

variable (hform : ∀ u, DiamondIntegral.Section6.gammaMapValue U.form u = 1)

include hform in
theorem labels_data {w : Values.Gamma (M := P.N)} {z : Fin n → ℤ}
    {D : DefSet (rawRVSpace (M := Carrier) U.object.arity) {c | baseCarrier c}} (hD : IsPiece P U m w z D)
    {t : Fin U.object.arity → RV} (ht : (fun j => rvTag (t j)) ∈ D.carrier) :
    ∃ hU : eRVs P t ∈ U.object.domain.carrier, ∃ u : Fin n → RationalRVUnits ℂ,
      (∀ i, fcv P U t hU i = some (u i)) ∧ ∀ i, Multiplicative.toAdd (u i).1 = (z i : ℚ) / (m : ℕ) := by
  rw [hD] at ht
  obtain ⟨hU, -, hci⟩ := chart_weight P U hform ht.1.1.1
  have hex : ∀ i, ∃ u, fcv P U t hU i = some u := fun i =>
    Option.ne_none_iff_exists'.mp (fcv_ne_none P U t hU i)
  choose u hu using hex
  refine ⟨hU, u, hu, fun i => ?_⟩
  have h1 := qpow_injective P ((hci i).symm.trans (ht.2 i))
  change rvq (fcv P U t hU i) = _ at h1
  rw [hu i] at h1
  exact h1

/-- Selection of the labels and the free coordinates. -/
def piz (z : Fin n → ℤ) : Fin (U.object.arity + nfree m L b z) → Fin (Kt b U.object.arity) :=
  Fin.append (fun j => εt b U.object.arity (.inr j))
    (fun s => εt b U.object.arity (.inl ((εf m L b z).symm s).val))

variable (Q : Finset (Fin U.object.arity → ℤ))
  (hA : Invariant m b (mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object))))
  (hQ : Covers m Q (mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object))))

theorem truncOf_label {k : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (j : Fin k) :
    truncOf m b p (εt b k (.inr j)) = rvTag (p.2 j) := by
  simp only [truncOf, Equiv.symm_apply_apply, Sum.elim_inr]

theorem truncOf_coeff {k : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (kk : Idx b) :
    truncOf m b p (εt b k (.inl kk)) = rvTag (truncPoint m b p.1 kk) := by
  simp only [truncOf, Equiv.symm_apply_apply, Sum.elim_inl]

include hform in
/-- **The class of a truncation piece.** -/
theorem piece_class {w : Values.Gamma (M := P.N)} {z : Fin n → ℤ}
    {D : DefSet (rawRVSpace (M := Carrier) U.object.arity) {c | baseCarrier c}} (hD : IsPiece P U m w z D)
    (hDf : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite)
    (hz0 : ∀ i, 0 ≤ z i + (m : ℕ) * L) (hzb : ∀ i, lead m L z i ≤ b i) :
    resSetClass canonicalInterpret_isCanonical
        (Tpiece b (fullTruncDefSet m b Q (strace_definableOver P L _) hA hQ) D)
        (Tpiece_finite b _ (fullTruncSet_finite_values m b Q _ hA hQ) D) =
      resSetClass canonicalInterpret_isCanonical D hDf *
        resSetClass canonicalInterpret_isCanonical (Lines m L b z) (Lines_finite m L b z) := by
  rw [← resSetClass_product]
  apply resSetClass_reindex _ _ _ _ (piz P U m L b z)
  · rintro r ⟨hrT, hrD⟩
    rw [resSetProduct_mem]
    refine ⟨?_, ?_⟩
    · convert hrD using 1
      funext j
      simp only [piz, Fin.append_left]
    · rw [mem_Lines]
      intro s'
      simp only [piz, Fin.append_right]
      obtain ⟨p, -, -, rfl⟩ := (mem_fullTruncSet_iff m b _ r).mp hrT
      rw [truncOf_coeff]
      exact coeffRV_mem_line _ _
  · rintro r ⟨hrT, hrD⟩ r' ⟨hr'T, -⟩ heq
    obtain ⟨⟨x, t⟩, hp, -, rfl⟩ := (mem_fullTruncSet_iff m b _ r).mp hrT
    obtain ⟨⟨x', t'⟩, hp', -, rfl⟩ := (mem_fullTruncSet_iff m b _ r').mp hr'T
    have hlab : t = t' := funext fun j => by
      have h := congrFun heq (Fin.castAdd _ j)
      simp only [piz, Fin.append_left, truncOf_label] at h
      exact taggedRVEquiv.symm.injective h
    subst hlab
    have hDp : (fun j => rvTag (t j)) ∈ D.carrier := by
      convert hrD using 1
      funext j
      exact (truncOf_label m b (x, t) j).symm
    obtain ⟨hU, u, hu, hz⟩ := labels_data P U m hform hD hDp
    obtain ⟨hU1, hx⟩ := (mem_lift P U L x t).mp hp
    obtain ⟨hU2, hx'⟩ := (mem_lift P U L x' t).mp hp'
    have hxu : ∀ i, rvOfField (tInv L * x i) = some (u i) := fun i => (hx i).trans (hu i)
    have hx'u : ∀ i, rvOfField (tInv L * x' i) = some (u i) := fun i => (hx' i).trans (hu i)
    funext a
    obtain ⟨c, rfl⟩ : ∃ c, a = εt b _ c := ⟨(εt b _).symm a, by simp⟩
    rcases c with kk | j
    · by_cases hf : lead m L z kk.1 < (kk.2 : ℕ)
      · have h := congrFun heq (Fin.natAdd _ (εf m L b z ⟨kk, hf⟩))
        simpa only [piz, Fin.append_right, Equiv.symm_apply_apply] using h
      · push Not at hf
        rw [truncOf_coeff, truncOf_coeff]
        simp only [truncPoint]
        rcases Nat.lt_or_eq_of_le hf with hlt | heq'
        · rw [(cf_lift m L x hxu z hz hz0 kk.1 kk.2).1 hlt, (cf_lift m L x' hx'u z hz hz0 kk.1 kk.2).1 hlt]
        · rw [(cf_lift m L x hxu z hz hz0 kk.1 kk.2).2 heq', (cf_lift m L x' hx'u z hz hz0 kk.1 kk.2).2 heq']
    · rw [truncOf_label, truncOf_label]
  · intro s hs
    rw [resSetProduct_mem] at hs
    obtain ⟨hsD, hsL⟩ := hs
    rw [mem_Lines] at hsL
    let t : Fin U.object.arity → RV := fun j => taggedRVEquiv (s (Fin.castAdd _ j))
    have htD : (fun j => rvTag (t j)) ∈ D.carrier := by
      convert hsD using 1
      funext j
      exact taggedRVEquiv.symm_apply_apply _
    obtain ⟨hU, u, hu, hz⟩ := labels_data P U m hform hD htD
    let c : Idx b → ℂ := fun kk =>
      if h : lead m L z kk.1 < (kk.2 : ℕ) then lineCoeff (taggedRVEquiv (s (Fin.natAdd _ (εf m L b z ⟨kk, h⟩))))
      else if (kk.2 : ℕ) = lead m L z kk.1 then ((u kk.1).2 : ℂ) else 0
    let x := polyRep m b c
    have hlead : ∀ i, c ⟨i, ⟨lead m L z i, Nat.lt_succ_of_le (hzb i)⟩⟩ = ((u i).2 : ℂ) := by
      intro i
      simp only [c, lt_irrefl, dite_false, if_true]
    have hrv : ∀ i, rvOfField (tInv L * x i) = some (u i) := by
      intro i
      have hui : u i = (Multiplicative.ofAdd ((z i : ℚ) / (m : ℕ)), (u i).2) :=
        Prod.ext (by show (u i).1 = Multiplicative.ofAdd ((z i : ℚ) / (m : ℕ)); rw [← hz i]; rfl) rfl
      rw [hui]
      apply rv_of_coeffs
      · intro δ hδ
        rw [cf_tInv_mul]
        by_cases hlev : ∃ j : Fin (b i + 1), δ + L = lev m j
        · obtain ⟨j, hj⟩ := hlev
          rw [hj, cf_polyRep_level]
          have hjl : (j : ℕ) < lead m L z i := by
            rw [← lev_lt_lead_iff m L z i (hz0 i)]
            linarith
          simp only [c, not_lt.mpr hjl.le, dite_false, hjl.ne, ite_false]
        · push Not at hlev
          exact cf_polyRep_of_not_level m b c i _ hlev
      · rw [cf_tInv_mul]
        have he : (z i : ℚ) / (m : ℕ) + L = lev m ((⟨lead m L z i, Nat.lt_succ_of_le (hzb i)⟩ :
            Fin (b i + 1)) : ℕ) := (lev_lead m L z i (hz0 i)).symm
        rw [he, cf_polyRep_level, hlead]
    have hlift : (x, t) ∈ mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object)) :=
      (mem_lift P U L x t).mpr ⟨hU, fun i => (hrv i).trans (hu i).symm⟩
    have hRI : RI m (x, t) := by
      refine ⟨fun i => ⟨polyRep_rational m b c i, polyRep_integral m b c i⟩, fun j => ?_⟩
      have h1 := ((hD _).mp htD).1.1.2 j
      exact label_rational_of_lattice P m (r := rvTag (t j)) h1
    refine ⟨truncOf m b (x, t), ⟨(mem_fullTruncSet_iff m b _ _).mpr ⟨_, hlift, hRI, rfl⟩, ?_⟩, ?_⟩
    · convert htD using 1
      funext j
      exact truncOf_label m b (x, t) j
    · funext a
      refine Fin.addCases (fun j => ?_) (fun s' => ?_) a
      · simp only [piz, Fin.append_left]
        rw [truncOf_label]
        exact taggedRVEquiv.symm_apply_apply _
      · simp only [piz, Fin.append_right]
        rw [truncOf_coeff]
        set kk := ((εf m L b z).symm s')
        have hf : lead m L z kk.val.1 < (kk.val.2 : ℕ) := kk.property
        change rvTag (truncPoint m b (polyRep m b c) kk.val) = _
        rw [truncPoint_polyRep]
        simp only [c, hf, dite_true]
        have hk : (⟨kk.val, hf⟩ : Free m L b z) = kk := rfl
        rw [hk, Equiv.apply_symm_apply]
        apply taggedRVEquiv.injective
        change coeffRV (lev m kk.val.2) (lineCoeff (taggedRVEquiv (s (Fin.natAdd _ s')))) = _
        exact coeffRV_lineCoeff (hsL s')

end Piece

/-! ### Counting the free coordinates -/

theorem card_free_fin (B ℓ : ℕ) (h : ℓ ≤ B) : Fintype.card {j : Fin (B + 1) // ℓ < (j : ℕ)} = B - ℓ := by
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun j : Fin (B + 1) => ℓ < (j : ℕ)) =
      (Finset.Ioc ℓ B).attachFin (fun j hj => by simp only [Finset.mem_Ioc] at hj; omega) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin, Finset.mem_Ioc]
    have := j.isLt
    omega
  rw [he, Finset.card_attachFin, Nat.card_Ioc]

theorem nfree_eq (z : Fin n → ℤ) (hzb : ∀ i, lead m L z i ≤ b i) :
    nfree m L b z = ∑ i, (b i - lead m L z i) := by
  let e : Free m L b z ≃ Σ i, {j : Fin (b i + 1) // lead m L z i < (j : ℕ)} :=
    { toFun := fun kk => ⟨kk.val.1, ⟨kk.val.2, kk.property⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.val⟩, p.2.property⟩
      left_inv := fun kk => rfl
      right_inv := fun p => rfl }
  rw [nfree, Fintype.card_congr e, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun i _ => card_free_fin (b i) (lead m L z i) (hzb i)

/-! ### Units -/

theorem exponent_eq (z : Fin n → ℤ) (hz0 : ∀ i, 0 ≤ z i + (m : ℕ) * L) (hzb : ∀ i, lead m L z i ≤ b i) :
    ((nfree m L b z : ℕ) : ℤ) - ((∑ i, b i : ℕ) : ℤ) = -(∑ i, z i) - ((n * ((m : ℕ) * L) : ℕ) : ℤ) := by
  rw [nfree_eq m L b z hzb]
  have hl : ∀ i, ((lead m L z i : ℕ) : ℤ) = z i + (m : ℕ) * L := fun i => Int.toNat_of_nonneg (hz0 i)
  push_cast [Nat.cast_sum]
  rw [Finset.sum_congr rfl fun i _ => (Nat.cast_sub (hzb i) : (((b i - lead m L z i : ℕ)) : ℤ) = _)]
  simp only [hl, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

theorem units_identity (N B C : ℕ) (e : ℤ) (h : (N : ℤ) - B = e - C) :
    (Lunit : Rloc) ^ N * Linv B = ((Lunit ^ e : Rlocˣ) : Rloc) * Linv C := by
  have h1 : (Lunit : Rloc) ^ N = ((Lunit ^ (N : ℤ) : Rlocˣ) : Rloc) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have h2 : ∀ k : ℕ, Linv k = ((Lunit ^ (-(k : ℤ)) : Rlocˣ) : Rloc) := by
    intro k
    rw [Linv, zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, inv_pow]
  rw [h1, h2, h2, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add]
  congr 2

/-! ### The class of the truncation of the scaled lift -/

section Full

open DiamondIntegral.Section7.ChartOfMeasured

local notation "π" => uniformizerValue P

variable (hform : ∀ u, DiamondIntegral.Section6.gammaMapValue U.form u = 1)
variable (Q : Finset (Fin U.object.arity → ℤ))
  (hA : Invariant m b (mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object))))
  (hQ : Covers m Q (mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object))))

theorem lattice_of_label_rational {r : RV} (h : LabelRational m r) :
    InLattice π m (codeValue (P.e (Sum.inr r))) := by
  rcases r with _ | u
  · rw [Galois.codeValue_rv_none]
    exact inLattice_one _ _
  · exact (Galois.inLattice_iff_fixed P m u).mpr ((labelFixed_iff m _).mpr h)

include hform in
/-- **The normalized class of the truncation of `t^L 𝕃U`.** -/
theorem fullClass_lift (hU : U.doublyBounded) (Z : Finset (Fin n → ℤ))
    (hZ : ∀ (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier),
      (∀ j, LabelRational m (t j)) → ∃ z ∈ Z, ∀ i, rvq (fcv P U t ht i) = (z i : ℚ) / (m : ℕ))
    (D : Values.Gamma (M := P.N) → (Fin n → ℤ) →
      DefSet (rawRVSpace (M := Carrier) U.object.arity) {c | baseCarrier c})
    (hDf : ∀ w z, (Set.range (fun u : D w z => fun i => Values.vrv (u.val i))).Finite)
    (hD : ∀ w z, IsPiece P U m w z (D w z))
    (hz0 : ∀ z ∈ Z, ∀ i, 0 ≤ z i + (m : ℕ) * L) (hzb : ∀ z ∈ Z, ∀ i, lead m L z i ≤ b i) :
    fullClass m b Q (strace_definableOver P L _) hA hQ =
      (∑ w ∈ weights P (chartOf P.hc U) (chartOf_bounded P.hc U hU) m, ∑ z ∈ Z,
        algebraMap _ Rloc (theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
          (resSetClass canonicalInterpret_isCanonical (D w z) (hDf w z)))) *
          ((Lunit ^ (-(∑ i, z i)) : Rlocˣ) : Rloc)) * Linv (n * ((m : ℕ) * L)) := by
  set W := weights P (chartOf P.hc U) (chartOf_bounded P.hc U hU) m
  let T := fullTruncDefSet m b Q (strace_definableOver P L (SpecialTransformations.Section4.rvLift U.object)) hA hQ
  let I := ↥(W ×ˢ Z)
  have hd : Pairwise (fun i j : I => Disjoint (Tpiece b T (D i.1.1 i.1.2)).carrier (Tpiece b T (D j.1.1 j.1.2)).carrier) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun r hri hrj => hij ?_
    have h1 := (hD _ _ _).mp hri.2
    have h2 := (hD _ _ _).mp hrj.2
    apply Subtype.ext
    apply Prod.ext
    · exact h1.1.2.symm.trans h2.1.2
    · funext i'
      have h3 := qpow_injective P ((h1.2 i').symm.trans (h2.2 i'))
      have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
      field_simp at h3
      exact_mod_cast h3
  have hcov : ∀ r, r ∈ T.carrier ↔ ∃ i : I, r ∈ (Tpiece b T (D i.1.1 i.1.2)).carrier := by
    intro r
    constructor
    · intro hr
      obtain ⟨⟨x, t⟩, hp, hRI, rfl⟩ := (mem_fullTruncSet_iff m b _ r).mp hr
      obtain ⟨ht, -⟩ := (mem_lift P U L x t).mp hp
      obtain ⟨z, hz, hzv⟩ := hZ t ht hRI.2
      have hdom : (fun j => P.e (rvTag (t j)).val) ∈ (chartOf P.hc U).domain := ⟨eRVs P t, ht, rfl⟩
      have hlat : (fun j => P.e (rvTag (t j)).val) ∈ latticeDomain P (chartOf P.hc U) m :=
        ⟨hdom, fun j => lattice_of_label_rational P m (hRI.2 j)⟩
      let w := (chartOf P.hc U).correctedWeight (fun j => P.e (rvTag (t j)).val)
      have hw : w ∈ W := (mem_weights P _ _ m w).mpr ⟨_, hlat, rfl⟩
      have hlabD : (fun j => rvTag (t j)) ∈ (D w z).carrier := by
        refine (hD w z _).mpr ⟨⟨hlat, rfl⟩, fun i => ?_⟩
        obtain ⟨ht', -, hci⟩ := chart_weight P U hform hdom
        rw [hci i]
        exact congrArg (qpow π) (hzv i)
      refine ⟨⟨(w, z), Finset.mem_product.mpr ⟨hw, hz⟩⟩, hr, ?_⟩
      convert hlabD using 1
      funext j
      exact truncOf_label m b (x, t) j
    · rintro ⟨i, hr, -⟩
      exact hr
  have hpart := resSetClass_finite_partition canonicalInterpret_isCanonical T
    (fullTruncSet_finite_values m b Q _ hA hQ) (fun i : I => Tpiece b T (D i.1.1 i.1.2))
    (fun i => Tpiece_finite b T (fullTruncSet_finite_values m b Q _ hA hQ) _) hd hcov
  unfold fullClass
  rw [hpart, map_sum, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
  rw [Finset.sum_coe_sort (W ×ˢ Z) (fun p => algebraMap EquivariantVariety.ModifiedRing Rloc
      (theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
        (resSetClass canonicalInterpret_isCanonical (Tpiece b T (D p.1 p.2))
          (Tpiece_finite b T (fullTruncSet_finite_values m b Q _ hA hQ) _)))) * Linv (∑ i, b i)),
    Finset.sum_product]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun z hz => ?_
  change algebraMap EquivariantVariety.ModifiedRing Rloc (theta_5_14_concrete
      (RESDimensionFreeReduction.quotient originalPuiseuxGround
        (resSetClass canonicalInterpret_isCanonical (Tpiece b T (D w z))
          (Tpiece_finite b T (fullTruncSet_finite_values m b Q _ hA hQ) _)))) * Linv (∑ i, b i) = _
  rw [piece_class P U m L b hform Q hA hQ (hD w z) (hDf w z) (hz0 z hz) (hzb z hz), map_mul, map_mul, map_mul,
    Lines_theta, map_pow, ← Lunit_val, mul_assoc,
    units_identity _ _ _ _ (exponent_eq m L b z (hz0 z hz) (hzb z hz)), mul_assoc]

end Full

end DiamondIntegral.Section8.Truncation
