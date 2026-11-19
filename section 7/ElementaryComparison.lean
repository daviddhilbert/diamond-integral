import «section 7».ElementaryBlowups
import «section 7».RVMaps

/-! Lemma 7.5 (`elementary:blowups:preserves:iso:vol`): elementary blowups of
isomorphic objects, in possibly different coordinates, have blowups of length one
with isomorphic results.

Let `F : U → V` be a measured isomorphism, `τ_U` and `τ_V` apertures of
elementary blowups of `U` and `V` in coordinates `j` and `j'`, with depths
`γ_U = vrv τ_U` and `γ' = vrv (τ_V ∘ F)`. On the definable piece where
`γ_U ≤ γ'` the endpoint graph of `U^♭` is blown up again in coordinate `j` with
the ratio aperture `ρ = (τ_V ∘ F) / τ_U`, of depth `γ' - γ_U ∈ [0, Δ_V]`. The
result is isomorphic to the corresponding piece of `V^♭`:

* `(u, s) ↦ (F u, s)` on the old shell;
* `(u, τ_U(u), s') ↦ (F u, τ_U(u) s')` from the new shell onto the rest of the
  shell of `V^♭`;
* `(u, τ_U(u), ρ(u)) ↦ (F u, τ_V(F u))` on the new endpoint.

Total weights are preserved because `F` preserves them and
`vrv (τ_U(u) s') = γ_U(u) + vrv s'`. Equal depths give a depth-zero blowup
whose endpoint `ρ(u)` has valuation zero but need not be `1`. The other piece is
symmetric, and an empty locus gives the identity. Every multiplier is a
coordinate or the value of a definable function on the actual domain; no
definable point of an RV fibre is chosen. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.ElementaryComparison
open DiamondIntegral.Section4
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions FiniteTupleBlocks
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.RVMaps

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### Joined maps -/

omit [LRV.Structure M] hM in
theorem join_mem_range {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) (i : Fin (n + m)) :
    join n m u y i ∈ Set.range u ∪ Set.range y := by
  induction m with
  | zero => exact Or.inr ⟨i, rfl⟩
  | succ m ih =>
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact Or.inl ⟨0, rfl⟩
    · rcases ih (Fin.tail u) i' with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Or.inl ⟨a.succ, ha⟩
      · exact Or.inr ⟨a, ha⟩

omit [LRV.Structure M] hM in
theorem index_cases (m : ℕ) (i : Fin (1 + m)) :
    (∃ i', i = headIndex 1 m i') ∨ i = tailIndex 1 m 0 := by
  have h := join_mem_range 1 m (headIndex 1 m) (tailIndex 1 m) i
  have hi : join 1 m (headIndex 1 m) (tailIndex 1 m) i = i :=
    congrFun (join_reconstruct 1 m (id : Fin (1 + m) → Fin (1 + m))) i
  rw [hi] at h
  rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact Or.inl ⟨a, ha.symm⟩
  · right
    rw [← ha]
    congr 1
    exact Subsingleton.elim a 0

theorem scalarDef_component {n m : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {G : (Fin n → M) → (Fin m → M)}
    (hG : TupleDef B I G) (i : Fin m) : ScalarDef B I (fun u => G u i) := by
  have hJ : DefinableOverBase B (fun _ : Fin m => .rv) (G '' I) :=
    BoundedClasses.graph_image_definable I G hG
  exact scalarDef_comp (g := fun v => v i) hG (scalarDef_coord hJ i) (fun u hu => ⟨u, hu, rfl⟩)

/-- The joined map `u ↦ (G u, h u)`. -/
def joinMap {n m : ℕ} (G : (Fin n → M) → (Fin m → M)) (h : (Fin n → M) → M) :
    (Fin n → M) → (Fin (1 + m) → M) := fun u => join 1 m (G u) ![h u]

theorem tupleDef_joinMap {n m : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {G : (Fin n → M) → (Fin m → M)}
    {h : (Fin n → M) → M} (hG : TupleDef B I G) (hh : ScalarDef B I h) :
    TupleDef B I (joinMap G h) := by
  apply tupleDef_of_scalar hI
  intro i
  rcases index_cases m i with ⟨i', rfl⟩ | rfl
  · simpa only [joinMap, join_head] using scalarDef_component hI hG i'
  · simpa only [joinMap, join_tail, Matrix.cons_val_zero] using hh

/-! ### RV arithmetic -/

theorem codeValue_rvOne : codeValue (iRVOne : M) = 1 := by
  have h1 : NonzeroRV (iRVOne : M) := ⟨rv_one_mem hM, RVCalc.rv_one_ne_zero hM⟩
  have h := GammaGroupNames.codeValue_mul (iRVOne : M) iRVOne h1 h1
  rw [rv_mul_one_any hM h1.1] at h
  have h' : codeValue (iRVOne : M) * 1 = codeValue (iRVOne : M) * codeValue (iRVOne : M) := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel h').symm

theorem inv_nonzero {a : M} (ha : NonzeroRV a) : NonzeroRV (iRVInv hM a) := by
  refine ⟨iRVInv_mem hM ha.1, fun h0 => ?_⟩
  have h := iRVInv_mul_cancel hM ha.1 ha.2
  rw [h0] at h
  have hz : iRVMul (iRVZero : M) a = iRVZero :=
    (rv_mul_eq_zero_of_model hM (rv_zero_mem hM) ha.1).mpr (Or.inl rfl)
  rw [hz] at h
  exact RVCalc.rv_one_ne_zero hM h.symm

theorem codeValue_inv {a : M} (ha : NonzeroRV a) : codeValue (iRVInv hM a) = (codeValue a)⁻¹ := by
  have h := GammaGroupNames.codeValue_mul (iRVInv hM a) a (inv_nonzero ha) ha
  rw [iRVInv_mul_cancel hM ha.1 ha.2, codeValue_rvOne] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- The quotient `g / h` in `RV`. -/
def rvDiv (g h : M) : M := iRVMul g (iRVInv hM h)

theorem rvDiv_nonzero {g h : M} (hg : NonzeroRV g) (hh : NonzeroRV h) : NonzeroRV (rvDiv (hM := hM) g h) :=
  BlowupChart.nonzero_mul hg (inv_nonzero hh)

theorem codeValue_rvDiv {g h : M} (hg : NonzeroRV g) (hh : NonzeroRV h) :
    codeValue (rvDiv (hM := hM) g h) = codeValue g * (codeValue h)⁻¹ := by
  rw [rvDiv, GammaGroupNames.codeValue_mul _ _ hg (inv_nonzero hh), codeValue_inv hh]

theorem rvDiv_mul {g h : M} (hg : iRV g) (hh : NonzeroRV h) :
    iRVMul (rvDiv (hM := hM) g h) h = g := by
  rw [rvDiv, rv_mul_assoc_of_model hM hg (iRVInv_mem hM hh.1) hh.1, iRVInv_mul_cancel hM hh.1 hh.2,
    rv_mul_one_any_right hM hg]

theorem mul_eq_iff_rvDiv {r g h : M} (hr : iRV r) (hg : iRV g) (hh : NonzeroRV h) :
    iRVMul r h = g ↔ r = rvDiv (hM := hM) g h := by
  constructor
  · intro he
    apply AnnularBlowup.rvMul_right_cancel hr (rv_mul_mem hM hg (iRVInv_mem hM hh.1)) hh
    rw [he]
    exact (rvDiv_mul hg hh).symm
  · rintro rfl
    exact rvDiv_mul hg hh

theorem rvMul_comm {a b : M} (ha : iRV a) (hb : iRV b) : iRVMul a b = iRVMul b a :=
  rv_mul_comm_of_model hM ha hb

/-- Quotients of definable scalar maps are definable. -/
theorem scalarDef_rvDiv {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {g h : (Fin n → M) → M}
    (hg : ScalarDef B I g) (hh : ScalarDef B I h) (hgr : ∀ u ∈ I, iRV (g u))
    (hhn : ∀ u ∈ I, NonzeroRV (h u)) :
    ScalarDef B I (fun u => rvDiv (hM := hM) (g u) (h u)) := by
  let I' : Set (Fin (1 + n) → M) :=
    {z | z ∘ headIndex 1 n ∈ I ∧ z ∈ sortedUniverse (fun _ : Fin (1 + n) => .rv)}
  have hI' : DefinableOverBase B (fun _ : Fin (1 + n) => .rv) I' :=
    hI.preimage_real (fun _ : Fin (1 + n) => .rv) (headIndex 1 n)
  have hmap : Set.MapsTo (fun z : Fin (1 + n) → M => z ∘ headIndex 1 n) I' I := fun z hz => hz.1
  let Φ : (Fin (1 + n) → M) → (Fin 3 → M) :=
    fun z => ![z (tailIndex 1 n 0), h (z ∘ headIndex 1 n), g (z ∘ headIndex 1 n)]
  have hΦ : TupleDef B I' Φ := by
    apply tupleDef_of_scalar hI'
    intro i
    fin_cases i
    · exact scalarDef_coord hI' _
    · exact scalarDef_comp (tupleDef_coord hI' (headIndex 1 n)) hh hmap
    · exact scalarDef_comp (tupleDef_coord hI' (headIndex 1 n)) hg hmap
  have hpre := RVStrictBoundedComparison.preimage_definable B I' Φ hΦ _
    (RVVariableMultiplication.graph_definable B)
  unfold ScalarDef
  convert hpre using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hz, he⟩
    have ht : z (tailIndex 1 n 0) = rvDiv (hM := hM) (g (z ∘ headIndex 1 n)) (h (z ∘ headIndex 1 n)) :=
      (congrFun he 0).symm
    have hdr : iRV (rvDiv (hM := hM) (g (z ∘ headIndex 1 n)) (h (z ∘ headIndex 1 n))) :=
      rv_mul_mem hM (hgr _ hz) (iRVInv_mem hM (hhn _ hz).1)
    have hs : z ∈ sortedUniverse (fun _ : Fin (1 + n) => .rv) := by
      intro i
      rcases index_cases n i with ⟨i', rfl⟩ | rfl
      · exact hI.proper _ hz i'
      · rw [ht]
        exact hdr
    refine ⟨⟨hz, hs⟩, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hs _
      · exact (hhn _ hz).1
      · exact hgr _ hz
    · change iRVMul (z (tailIndex 1 n 0)) (h (z ∘ headIndex 1 n)) = g (z ∘ headIndex 1 n)
      rw [ht]
      exact rvDiv_mul (hgr _ hz) (hhn _ hz)
  · rintro ⟨⟨hz, hs⟩, hrv, he⟩
    refine ⟨hz, ?_⟩
    have he' : iRVMul (z (tailIndex 1 n 0)) (h (z ∘ headIndex 1 n)) = g (z ∘ headIndex 1 n) := he
    have ht := (mul_eq_iff_rvDiv (hs _) (hgr _ hz) (hhn _ hz)).mp he'
    funext i
    fin_cases i
    exact ht.symm

/-! ### Points, weights and inverse maps -/

theorem blown_weight (r : Chart B (1 + k)) (j : Fin (1 + k)) (u : Fin r.arity → M) (hu : u ∈ r.domain)
    (s : M) (hs : NonzeroRV s) :
    r.volume u * ∏ l, codeValue (blownCoordinate r j u s l) = r.correctedWeight u * codeValue s := by
  simp only [Chart.correctedWeight]
  rw [prod_split j, prod_split j (fun l => codeValue (r.coordinate u l)), blownCoordinate_at,
    GammaGroupNames.codeValue_mul _ _ hs (r.coordinate_proper _ hu j)]
  have h : ∀ i, blownCoordinate r j u s (skip j i) = r.coordinate u (skip j i) := by
    intro i
    simp only [blownCoordinate, Function.update_of_ne (skip_ne j i)]
  simp only [h]
  ac_rfl

theorem endpoint_weight (r : Chart B (1 + k)) (j : Fin (1 + k)) (hfin : InactiveFinite r j)
    (τ : Aperture r) (w : Fin (1 + r.arity) → M) (hw : w ∈ (graphChart r τ).domain) :
    (endpointChart r j hfin τ).correctedWeight w =
      r.correctedWeight (w ∘ headIndex 1 r.arity) * codeValue (w (aIdx r)) := by
  unfold endpointChart
  rw [pieceChart_weight]
  exact blown_weight r j _ hw.1 _ (graph_aperture_nonzero r τ w hw)

/-- The raw point `(u, t)`. -/
abbrev gpt {n : ℕ} (u : Fin n → M) (t : M) : Fin (1 + n) → M := join 1 n u ![t]

omit hM in
theorem gpt_head {n : ℕ} (u : Fin n → M) (t : M) : gpt u t ∘ headIndex 1 n = u :=
  funext (join_head 1 n u ![t])

omit hM in
theorem gpt_tail {n : ℕ} (u : Fin n → M) (t : M) : gpt u t ∘ tailIndex 1 n = ![t] :=
  funext (join_tail 1 n u ![t])

omit hM in
theorem gpt_last {n : ℕ} (u : Fin n → M) (t : M) : gpt u t (tailIndex 1 n 0) = t :=
  join_tail 1 n u ![t] 0

omit hM in
theorem gpt_injective {n : ℕ} {u u' : Fin n → M} {t t' : M} (h : gpt u t = gpt u' t') : u = u' ∧ t = t' :=
  ⟨by rw [← gpt_head u t, h, gpt_head], by rw [← gpt_last u t, h, gpt_last]⟩

theorem mem_graph_iff (r : Chart B k) (τ : Aperture r) (u : Fin r.arity → M) (t : M) :
    gpt u t ∈ (graphChart r τ).domain ↔ u ∈ r.domain ∧ t = τ.aperture u := by
  change (gpt u t ∘ headIndex 1 r.arity ∈ r.domain ∧ ![τ.aperture (gpt u t ∘ headIndex 1 r.arity)] =
    gpt u t ∘ tailIndex 1 r.arity) ↔ _
  rw [gpt_head, gpt_tail]
  constructor
  · rintro ⟨hu, he⟩
    exact ⟨hu, (congrFun he 0).symm⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨hu, rfl⟩

theorem graph_eq (r : Chart B k) (τ : Aperture r) {w : Fin (1 + r.arity) → M}
    (hw : w ∈ (graphChart r τ).domain) :
    w = gpt (w ∘ headIndex 1 r.arity) (τ.aperture (w ∘ headIndex 1 r.arity)) :=
  graph_canonical r τ hw

theorem mem_shell_iff (r : Chart B k) (τ : Aperture r) (u : Fin r.arity → M) (s : M) :
    gpt (gpt u (τ.aperture u)) s ∈ shellDomain r τ ↔
      u ∈ r.domain ∧ NonzeroRV s ∧ 1 < codeValue s ∧ codeValue s ≤ codeValue (τ.aperture u) := by
  rw [shell_iff]
  change gpt (gpt u (τ.aperture u)) s ∘ headIndex 1 (1 + r.arity) ∈ (graphChart r τ).domain ∧
      Proper (gpt (gpt u (τ.aperture u)) s ∘ tailIndex 1 (1 + r.arity)) ∧
        1 < codeValue (gpt (gpt u (τ.aperture u)) s (tailIndex 1 (1 + r.arity) 0)) ∧
          codeValue (gpt (gpt u (τ.aperture u)) s (tailIndex 1 (1 + r.arity) 0)) ≤
            codeValue ((gpt (gpt u (τ.aperture u)) s ∘ headIndex 1 (1 + r.arity)) (tailIndex 1 r.arity 0)) ↔ _
  rw [gpt_head, gpt_tail, gpt_last, gpt_last, mem_graph_iff]
  constructor
  · rintro ⟨⟨hu, _⟩, hp, h1, h2⟩
    exact ⟨hu, ⟨(hp 0).1, (hp 0).2⟩, h1, h2⟩
  · rintro ⟨hu, hs, h1, h2⟩
    refine ⟨⟨hu, rfl⟩, fun i => ?_, h1, h2⟩
    fin_cases i
    exact ⟨hs.1, hs.2⟩

theorem shell_eq (r : Chart B k) (τ : Aperture r) {w : Fin (1 + (1 + r.arity)) → M}
    (hw : w ∈ shellDomain r τ) :
    w = gpt (gpt (w ∘ xIdx r) (τ.aperture (w ∘ xIdx r))) (w (sIdx r)) :=
  shell_canonical r τ hw

theorem isoMap_symm_isoMap {k' : ℕ} {a b : Chart B k'} (F : Iso a b) {u : Fin a.arity → M}
    (hu : u ∈ a.domain) : isoMap (RVMeasuredIsomorphisms.symm F) (isoMap F u) = u := by
  rw [isoMap_on F ⟨u, hu⟩]
  have h := isoMap_on (RVMeasuredIsomorphisms.symm F) (F.equiv ⟨u, hu⟩)
  rw [h]
  change (F.equiv.symm (F.equiv ⟨u, hu⟩)).val = u
  rw [Equiv.symm_apply_apply]

theorem isoMap_isoMap_symm {k' : ℕ} {a b : Chart B k'} (F : Iso a b) {v : Fin b.arity → M}
    (hv : v ∈ b.domain) : isoMap F (isoMap (RVMeasuredIsomorphisms.symm F) v) = v := by
  rw [isoMap_on (RVMeasuredIsomorphisms.symm F) ⟨v, hv⟩]
  have h := isoMap_on F ((RVMeasuredIsomorphisms.symm F).equiv ⟨v, hv⟩)
  rw [h]
  change (F.equiv (F.equiv.symm ⟨v, hv⟩)).val = v
  rw [Equiv.apply_symm_apply]

theorem isoMap_mem {k' : ℕ} {a b : Chart B k'} (F : Iso a b) {u : Fin a.arity → M}
    (hu : u ∈ a.domain) : isoMap F u ∈ b.domain := (isoMap_bijOn F).1 hu

/-- The endpoint graph inherits the finite-to-one inactive projection. -/
theorem endpoint_inactiveFinite (r : Chart B (1 + k)) (j : Fin (1 + k)) (hfin : InactiveFinite r j)
    (τ : Aperture r) : InactiveFinite (endpointChart r j hfin τ) j := by
  intro t
  apply ((hfin t).image (fun u => gpt u (τ.aperture u))).subset
  rintro w ⟨hw, he⟩
  refine ⟨w ∘ headIndex 1 r.arity, ⟨hw.1, ?_⟩, (graph_eq r τ hw).symm⟩
  rw [← he]
  exact (inactive_blownCoordinate r j _ _).symm

/-! ### The ratio aperture and the second blowup -/

section Comparison
variable (D E : AnnularDatum B k) (F : Iso D.chart E.chart)

/-- The ratio aperture `(τ_V ∘ F) / τ_U` on the endpoint graph of `U^♭`. -/
def ratio (w : Fin (1 + D.chart.arity) → M) : M :=
  rvDiv (hM := hM) (E.aperture.aperture (isoMap F (w ∘ headIndex 1 D.chart.arity))) (w (aIdx D.chart))

theorem baseMap_tupleDef :
    TupleDef B (graphChart D.chart D.aperture).domain
      (fun w : Fin (1 + D.chart.arity) → M => isoMap F (w ∘ headIndex 1 D.chart.arity)) :=
  tupleDef_comp (G := isoMap F) (tupleDef_coord (graphChart D.chart D.aperture).domain_definable _)
    (isoMap_graph F) (fun _ hw => hw.1)

theorem ratio_scalarDef : ScalarDef B (graphChart D.chart D.aperture).domain (ratio D E F) := by
  apply scalarDef_rvDiv (graphChart D.chart D.aperture).domain_definable
  · exact scalarDef_comp (baseMap_tupleDef D E F) E.aperture.graph_definable
      (fun _ hw => isoMap_mem F hw.1)
  · exact scalarDef_coord (graphChart D.chart D.aperture).domain_definable _
  · exact fun w hw => (E.aperture.nonzero _ (isoMap_mem F hw.1)).1
  · exact graph_aperture_nonzero D.chart D.aperture

variable (hle : ∀ u ∈ D.chart.domain,
  codeValue (D.aperture.aperture u) ≤ codeValue (E.aperture.aperture (isoMap F u)))

theorem codeValue_ratio {w : Fin (1 + D.chart.arity) → M} (hw : w ∈ (graphChart D.chart D.aperture).domain) :
    codeValue (ratio D E F w) =
      codeValue (E.aperture.aperture (isoMap F (w ∘ headIndex 1 D.chart.arity))) *
        (codeValue (D.aperture.aperture (w ∘ headIndex 1 D.chart.arity)))⁻¹ := by
  rw [ratio, codeValue_rvDiv (E.aperture.nonzero _ (isoMap_mem F hw.1))
    (graph_aperture_nonzero D.chart D.aperture w hw), graph_aperture D.chart D.aperture hw]

include hle in
/-- The ratio aperture: definable, nonzero, with depth in `[0, Δ_V]`. -/
def ratioAperture : Aperture (endpointChart D.chart D.coordinate D.finite D.aperture) where
  aperture := ratio D E F
  graph_definable := ratio_scalarDef D E F
  nonzero := fun w hw => rvDiv_nonzero (E.aperture.nonzero _ (isoMap_mem F hw.1))
    (graph_aperture_nonzero D.chart D.aperture w hw)
  nonnegative := fun w hw => by
    rw [codeValue_ratio D E F hw]
    exact le_mul_inv_iff_mul_le.mpr (by rw [one_mul]; exact hle _ hw.1)
  bound := E.aperture.bound
  bounded := fun w hw => by
    rw [codeValue_ratio D E F hw]
    refine (mul_le_of_le_one_right' (inv_le_one'.mpr (D.aperture.nonnegative _ hw.1))).trans ?_
    exact E.aperture.bounded _ (isoMap_mem F hw.1)

include hle in
/-- The second blowup: the endpoint graph of `U^♭`, blown up again in the same
coordinate with the ratio aperture. -/
def secondDatum : AnnularDatum B k where
  chart := endpointChart D.chart D.coordinate D.finite D.aperture
  coordinate := D.coordinate
  finite := endpoint_inactiveFinite D.chart D.coordinate D.finite D.aperture
  aperture := ratioAperture D E F hle
  bounded := endpoint_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded

end Comparison

/-! ### The endpoint comparison -/

omit [LRV.Structure M] hM in
theorem cancel_gamma {G : Type*} [CommGroup G] (a t s : G) : a * t * (s * t⁻¹) = a * s := by
  rw [mul_comm s t⁻¹, ← mul_assoc, mul_assoc a t t⁻¹, mul_inv_cancel, mul_one]

section Endpoint
variable (D E : AnnularDatum B k) (F : Iso D.chart E.chart)
  (hle : ∀ u ∈ D.chart.domain,
    codeValue (D.aperture.aperture u) ≤ codeValue (E.aperture.aperture (isoMap F u)))

/-- The base point of a point of the second endpoint graph. -/
abbrev base2 (z : Fin (1 + (1 + D.chart.arity)) → M) : Fin D.chart.arity → M := z ∘ xIdx D.chart

theorem endpoint2_eq {z : Fin (1 + (1 + D.chart.arity)) → M}
    (hz : z ∈ (graphChart (secondDatum D E F hle).chart (secondDatum D E F hle).aperture).domain) :
    base2 D z ∈ D.chart.domain ∧
      z = gpt (gpt (base2 D z) (D.aperture.aperture (base2 D z)))
        (ratio D E F (gpt (base2 D z) (D.aperture.aperture (base2 D z)))) := by
  have hw : z ∘ headIndex 1 (1 + D.chart.arity) ∈ (graphChart D.chart D.aperture).domain := hz.1
  have h1 := graph_eq (secondDatum D E F hle).chart (secondDatum D E F hle).aperture hz
  have h2 := graph_eq D.chart D.aperture hw
  refine ⟨hw.1, ?_⟩
  have hb : base2 D z = (z ∘ headIndex 1 (1 + D.chart.arity)) ∘ headIndex 1 D.chart.arity := rfl
  rw [hb, ← h2]
  exact h1

theorem mem_endpoint2 {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    gpt (gpt u (D.aperture.aperture u)) (ratio D E F (gpt u (D.aperture.aperture u))) ∈
      (graphChart (secondDatum D E F hle).chart (secondDatum D E F hle).aperture).domain :=
  (mem_graph_iff (secondDatum D E F hle).chart (secondDatum D E F hle).aperture _ _).mpr
    ⟨(mem_graph_iff D.chart D.aperture u _).mpr ⟨hu, rfl⟩, rfl⟩

theorem base2_gpt (u : Fin D.chart.arity → M) (t s : M) : base2 D (gpt (gpt u t) s) = u := by
  change (gpt (gpt u t) s ∘ headIndex 1 (1 + D.chart.arity)) ∘ headIndex 1 D.chart.arity = u
  rw [gpt_head, gpt_head]

/-- `(u, τ_U(u), ρ(u)) ↦ (F u, τ_V(F u))`. -/
def endpointMap (z : Fin (1 + (1 + D.chart.arity)) → M) : Fin (1 + E.chart.arity) → M :=
  gpt (isoMap F (base2 D z)) (E.aperture.aperture (isoMap F (base2 D z)))

/-- The new endpoint is isomorphic to the endpoint of `V^♭`. -/
def endpointIso :
    Iso (endpointChart (secondDatum D E F hle).chart (secondDatum D E F hle).coordinate
        (secondDatum D E F hle).finite (secondDatum D E F hle).aperture)
      (endpointChart E.chart E.coordinate E.finite E.aperture) := by
  have hI := (graphChart (secondDatum D E F hle).chart (secondDatum D E F hle).aperture).domain_definable
  have hbase : Set.MapsTo (base2 D)
      (graphChart (secondDatum D E F hle).chart (secondDatum D E F hle).aperture).domain D.chart.domain :=
    fun z hz => (endpoint2_eq D E F hle hz).1
  have hG : TupleDef B (graphChart (secondDatum D E F hle).chart (secondDatum D E F hle).aperture).domain
      (fun z => isoMap F (base2 D z)) :=
    tupleDef_comp (G := isoMap F) (tupleDef_coord hI (xIdx D.chart)) (isoMap_graph F) hbase
  refine isoOfMap _ _ (endpointMap D E F) ?_ ?_ ?_
  · exact tupleDef_joinMap hI hG (scalarDef_comp hG E.aperture.graph_definable
      (fun z hz => isoMap_mem F (hbase hz)))
  · refine ⟨fun z hz => ?_, fun z hz z' hz' he => ?_, fun y hy => ?_⟩
    · exact (mem_graph_iff E.chart E.aperture _ _).mpr ⟨isoMap_mem F (hbase hz), rfl⟩
    · have hu := (gpt_injective he).1
      have huu := (isoMap_bijOn F).2.1 (hbase hz) (hbase hz') hu
      rw [(endpoint2_eq D E F hle hz).2, (endpoint2_eq D E F hle hz').2, huu]
    · have hv : y ∘ headIndex 1 E.chart.arity ∈ E.chart.domain := hy.1
      let v := y ∘ headIndex 1 E.chart.arity
      let u := isoMap (RVMeasuredIsomorphisms.symm F) v
      have hu : u ∈ D.chart.domain := isoMap_mem (RVMeasuredIsomorphisms.symm F) hv
      refine ⟨_, mem_endpoint2 D E F hle hu, ?_⟩
      change endpointMap D E F _ = y
      rw [endpointMap, base2_gpt, isoMap_isoMap_symm F hv]
      exact (graph_eq E.chart E.aperture hy).symm
  · intro z hz
    obtain ⟨hu, hz'⟩ := endpoint2_eq D E F hle hz
    have hw : gpt (base2 D z) (D.aperture.aperture (base2 D z)) ∈ (graphChart D.chart D.aperture).domain :=
      (mem_graph_iff D.chart D.aperture _ _).mpr ⟨hu, rfl⟩
    have hy : endpointMap D E F z ∈ (graphChart E.chart E.aperture).domain :=
      (mem_graph_iff E.chart E.aperture _ _).mpr ⟨isoMap_mem F hu, rfl⟩
    rw [endpoint_weight _ _ _ _ z hz, endpoint_weight _ _ _ _ _ hy]
    conv_lhs => rw [hz']
    change (endpointChart D.chart D.coordinate D.finite D.aperture).correctedWeight
        (gpt (gpt (base2 D z) (D.aperture.aperture (base2 D z)))
          (ratio D E F (gpt (base2 D z) (D.aperture.aperture (base2 D z)))) ∘ headIndex 1 (1 + D.chart.arity)) *
        codeValue (gpt (gpt (base2 D z) (D.aperture.aperture (base2 D z)))
          (ratio D E F (gpt (base2 D z) (D.aperture.aperture (base2 D z)))) (tailIndex 1 (1 + D.chart.arity) 0)) =
      E.chart.correctedWeight (endpointMap D E F z ∘ headIndex 1 E.chart.arity) *
        codeValue (endpointMap D E F z (tailIndex 1 E.chart.arity 0))
    have hR : endpointMap D E F z ∘ headIndex 1 E.chart.arity = isoMap F (base2 D z) := gpt_head _ _
    have hR2 : endpointMap D E F z (tailIndex 1 E.chart.arity 0) =
        E.aperture.aperture (isoMap F (base2 D z)) := gpt_last _ _
    have hA : gpt (base2 D z) (D.aperture.aperture (base2 D z)) (aIdx D.chart) =
        D.aperture.aperture (base2 D z) := gpt_last _ _
    rw [gpt_head, gpt_last, endpoint_weight _ _ _ _ _ hw, gpt_head, hA, codeValue_ratio D E F hw,
      gpt_head, hR, hR2, ← isoMap_weight F _ hu]
    exact cancel_gamma _ _ _

end Endpoint

/-! ### The shell comparisons -/

/-- The inverse of a measured isomorphism on raw points. -/
abbrev finv {k' : ℕ} {a b : Chart B k'} (F : Iso a b) : (Fin b.arity → M) → (Fin a.arity → M) :=
  isoMap (RVMeasuredIsomorphisms.symm F)

section Shell
variable (D E : AnnularDatum B k) (F : Iso D.chart E.chart)
  (hle : ∀ u ∈ D.chart.domain,
    codeValue (D.aperture.aperture u) ≤ codeValue (E.aperture.aperture (isoMap F u)))

theorem shellE_base_tupleDef :
    TupleDef B (shellDomain E.chart E.aperture) (fun y => finv F (y ∘ xIdx E.chart)) :=
  tupleDef_comp (G := finv F)
    (tupleDef_coord (VariableApertureRayCancellation.annularChart (graphChart E.chart E.aperture)
      (aIdx E.chart)).domain_definable (xIdx E.chart))
    (isoMap_graph (RVMeasuredIsomorphisms.symm F)) (fun _ hy => (shell_points E.chart E.aperture hy).1)

/-- The shallow part of the shell of `V^♭`: `vrv s ≤ vrv τ_U (F⁻¹ v)`. -/
def shallow : Set (Fin (1 + (1 + E.chart.arity)) → M) :=
  {y | y ∈ shellDomain E.chart E.aperture ∧
    codeValue (y (sIdx E.chart)) ≤ codeValue (D.aperture.aperture (finv F (y ∘ xIdx E.chart)))}

theorem shallow_definable :
    DefinableOverBase B (fun _ : Fin (1 + (1 + E.chart.arity)) => .rv) (shallow D E F) := by
  have hI := (VariableApertureRayCancellation.annularChart (graphChart E.chart E.aperture)
    (aIdx E.chart)).domain_definable
  apply le_definable hI (scalarDef_coord hI _)
    (scalarDef_comp (shellE_base_tupleDef D E F) D.aperture.graph_definable
      (fun y hy => isoMap_mem (RVMeasuredIsomorphisms.symm F) (shell_points E.chart E.aperture hy).1))
  · exact fun y hy => (shell_points E.chart E.aperture hy).2.1
  · exact fun y hy => D.aperture.nonzero _
      (isoMap_mem (RVMeasuredIsomorphisms.symm F) (shell_points E.chart E.aperture hy).1)

/-- The shell of `V^♭` as an object. -/
abbrev shellE : Obj B (1 + k) := shellBounded E.chart E.coordinate E.finite E.aperture E.bounded

theorem shellDomain_tupleDef_base (r : Chart B (1 + k)) (τ : Aperture r) :
    TupleDef B (shellDomain r τ) (fun y => y ∘ xIdx r) :=
  tupleDef_coord (VariableApertureRayCancellation.annularChart (graphChart r τ) (aIdx r)).domain_definable
    (xIdx r)

/-- `(u, τ_U(u), s) ↦ (F u, τ_V(F u), s)`. -/
def shallowMap (y : Fin (1 + (1 + D.chart.arity)) → M) : Fin (1 + (1 + E.chart.arity)) → M :=
  gpt (gpt (isoMap F (y ∘ xIdx D.chart)) (E.aperture.aperture (isoMap F (y ∘ xIdx D.chart))))
    (y (sIdx D.chart))

theorem gpt2_xIdx {n : ℕ} (u : Fin n → M) (t s : M) :
    gpt (gpt u t) s ∘ (fun i => headIndex 1 (1 + n) (headIndex 1 n i)) = u := by
  change (gpt (gpt u t) s ∘ headIndex 1 (1 + n)) ∘ headIndex 1 n = u
  rw [gpt_head, gpt_head]

theorem gpt2_s {n : ℕ} (u : Fin n → M) (t s : M) : gpt (gpt u t) s (tailIndex 1 (1 + n) 0) = s :=
  gpt_last _ _

theorem gpt2_sIdx {k' : ℕ} (r : Chart B k') (u : Fin r.arity → M) (t s : M) :
    gpt (gpt u t) s (sIdx r) = s := gpt_last _ _

theorem gpt2_xIdxR {k' : ℕ} (r : Chart B k') (u : Fin r.arity → M) (t s : M) :
    gpt (gpt u t) s ∘ xIdx r = u := gpt2_xIdx u t s

/-- The shell of `U^♭` is isomorphic to the shallow part of the shell of `V^♭`. -/
def shallowIso :
    Iso (shellChart D.chart D.coordinate D.finite D.aperture)
      (piece (shellE E) (shallow D E F) (shallow_definable D E F)).toChart := by
  have hI := (VariableApertureRayCancellation.annularChart (graphChart D.chart D.aperture)
    (aIdx D.chart)).domain_definable
  have hbase : Set.MapsTo (fun y => y ∘ xIdx D.chart) (shellDomain D.chart D.aperture) D.chart.domain :=
    fun _ hy => (shell_points D.chart D.aperture hy).1
  have hG : TupleDef B (shellDomain D.chart D.aperture) (fun y => isoMap F (y ∘ xIdx D.chart)) :=
    tupleDef_comp (G := isoMap F) (shellDomain_tupleDef_base D.chart D.aperture) (isoMap_graph F) hbase
  refine isoOfMap _ _ (shallowMap D E F) ?_ ?_ ?_
  · exact tupleDef_joinMap hI (tupleDef_joinMap hI hG
      (scalarDef_comp hG E.aperture.graph_definable (fun y hy => isoMap_mem F (hbase hy))))
      (scalarDef_coord hI _)
  · refine ⟨fun y hy => ?_, fun y hy y' hy' he => ?_, fun y' hy' => ?_⟩
    · have hp := shell_points D.chart D.aperture hy
      have hs := (mem_shell_iff D.chart D.aperture _ _).mp ((shell_eq D.chart D.aperture hy) ▸ hy)
      have hmem : shallowMap D E F y ∈ shellDomain E.chart E.aperture :=
        (mem_shell_iff E.chart E.aperture _ _).mpr ⟨isoMap_mem F hp.1, hs.2.1, hs.2.2.1,
          hs.2.2.2.trans (hle _ hp.1)⟩
      refine ⟨hmem, hmem, ?_⟩
      change codeValue (shallowMap D E F y (sIdx E.chart)) ≤
        codeValue (D.aperture.aperture (finv F (shallowMap D E F y ∘ xIdx E.chart)))
      rw [shallowMap, gpt2_sIdx, gpt2_xIdxR,
        show finv F (isoMap F (y ∘ xIdx D.chart)) = y ∘ xIdx D.chart from isoMap_symm_isoMap F hs.1]
      exact hs.2.2.2
    · have h1 := gpt_injective he
      have h2 := gpt_injective h1.1
      have huu : y ∘ xIdx D.chart = y' ∘ xIdx D.chart := (isoMap_bijOn F).2.1 (hbase hy) (hbase hy') h2.1
      rw [shell_eq D.chart D.aperture hy, shell_eq D.chart D.aperture hy', huu, h1.2]
    · obtain ⟨_, hy'S, hle'⟩ := hy'
      have hp := shell_points E.chart E.aperture hy'S
      have hs := (mem_shell_iff E.chart E.aperture _ _).mp ((shell_eq E.chart E.aperture hy'S) ▸ hy'S)
      let u := finv F (y' ∘ xIdx E.chart)
      have hu : u ∈ D.chart.domain := isoMap_mem (RVMeasuredIsomorphisms.symm F) hp.1
      have hmem : gpt (gpt u (D.aperture.aperture u)) (y' (sIdx E.chart)) ∈ shellDomain D.chart D.aperture :=
        (mem_shell_iff D.chart D.aperture _ _).mpr ⟨hu, hs.2.1, hs.2.2.1, hle'⟩
      refine ⟨_, hmem, ?_⟩
      change shallowMap D E F _ = y'
      rw [shallowMap, gpt2_sIdx, gpt2_xIdxR,
        show isoMap F u = y' ∘ xIdx E.chart from isoMap_isoMap_symm F hp.1]
      exact (shell_eq E.chart E.aperture hy'S).symm
  · intro y hy
    have hp := shell_points D.chart D.aperture hy
    have hmem : shallowMap D E F y ∈ shellDomain E.chart E.aperture := by
      have hs := (mem_shell_iff D.chart D.aperture _ _).mp ((shell_eq D.chart D.aperture hy) ▸ hy)
      exact (mem_shell_iff E.chart E.aperture _ _).mpr ⟨isoMap_mem F hp.1, hs.2.1, hs.2.2.1,
        hs.2.2.2.trans (hle _ hp.1)⟩
    change (shellChart D.chart D.coordinate D.finite D.aperture).correctedWeight y =
      (shellChart E.chart E.coordinate E.finite E.aperture).correctedWeight (shallowMap D E F y)
    rw [shell_weight D.chart D.coordinate D.finite D.aperture y hy,
      shell_weight E.chart E.coordinate E.finite E.aperture _ hmem]
    change _ = E.chart.correctedWeight (shallowMap D E F y ∘ xIdx E.chart) *
      codeValue (shallowMap D E F y (sIdx E.chart))
    rw [shallowMap, gpt2_sIdx, gpt2_xIdxR, ← isoMap_weight F _ (hbase hy)]

end Shell

/-! ### The deep shell comparison -/

section Deep
variable (D E : AnnularDatum B k) (F : Iso D.chart E.chart)
  (hle : ∀ u ∈ D.chart.domain,
    codeValue (D.aperture.aperture u) ≤ codeValue (E.aperture.aperture (isoMap F u)))

/-- The base point of a point of the new shell. -/
abbrev base3 (x : Fin (1 + (1 + (1 + D.chart.arity))) → M) : Fin D.chart.arity → M :=
  (x ∘ xIdx (endpointChart D.chart D.coordinate D.finite D.aperture)) ∘ headIndex 1 D.chart.arity

/-- `(u, τ_U(u), ρ(u), s') ↦ (F u, τ_V(F u), τ_U(u) s')`. -/
def deepMap (x : Fin (1 + (1 + (1 + D.chart.arity))) → M) : Fin (1 + (1 + E.chart.arity)) → M :=
  gpt (gpt (isoMap F (base3 D x)) (E.aperture.aperture (isoMap F (base3 D x))))
    (iRVMul (D.aperture.aperture (base3 D x)) (x (sIdx (endpointChart D.chart D.coordinate D.finite D.aperture))))

theorem shell3_eq {x : Fin (1 + (1 + (1 + D.chart.arity))) → M}
    (hx : x ∈ shellDomain (secondDatum D E F hle).chart (secondDatum D E F hle).aperture) :
    base3 D x ∈ D.chart.domain ∧
      x = gpt (gpt (gpt (base3 D x) (D.aperture.aperture (base3 D x)))
        (ratio D E F (gpt (base3 D x) (D.aperture.aperture (base3 D x)))))
          (x (sIdx (endpointChart D.chart D.coordinate D.finite D.aperture))) := by
  have hw := (shell_points (secondDatum D E F hle).chart (secondDatum D E F hle).aperture hx).1
  have h1 := shell_eq (secondDatum D E F hle).chart (secondDatum D E F hle).aperture hx
  have h2 := graph_eq D.chart D.aperture hw
  have hxw : x ∘ xIdx (secondDatum D E F hle).chart = gpt (base3 D x) (D.aperture.aperture (base3 D x)) := h2
  refine ⟨hw.1, ?_⟩
  calc x = gpt (gpt (x ∘ xIdx (secondDatum D E F hle).chart)
        (ratio D E F (x ∘ xIdx (secondDatum D E F hle).chart))) (x (sIdx (secondDatum D E F hle).chart)) := h1
    _ = _ := by rw [hxw]; rfl

theorem mem_shell3 {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) {s : M} (hs : NonzeroRV s)
    (h1 : 1 < codeValue s) (h2 : codeValue s ≤ codeValue (ratio D E F (gpt u (D.aperture.aperture u)))) :
    gpt (gpt (gpt u (D.aperture.aperture u)) (ratio D E F (gpt u (D.aperture.aperture u)))) s ∈
      shellDomain (secondDatum D E F hle).chart (secondDatum D E F hle).aperture :=
  (mem_shell_iff (secondDatum D E F hle).chart (secondDatum D E F hle).aperture _ s).mpr
    ⟨(mem_graph_iff D.chart D.aperture u _).mpr ⟨hu, rfl⟩, hs, h1, h2⟩

theorem base3_gpt (u : Fin D.chart.arity → M) (t r s : M) : base3 D (gpt (gpt (gpt u t) r) s) = u := by
  change ((gpt (gpt (gpt u t) r) s ∘ headIndex 1 (1 + (1 + D.chart.arity))) ∘
    headIndex 1 (1 + D.chart.arity)) ∘ headIndex 1 D.chart.arity = u
  rw [gpt_head, gpt_head, gpt_head]

/-- The new shell is isomorphic to the deep part of the shell of `V^♭`. -/
def deepIso :
    Iso (shellChart (secondDatum D E F hle).chart (secondDatum D E F hle).coordinate
        (secondDatum D E F hle).finite (secondDatum D E F hle).aperture)
      (cpiece (shellE E) (shallow D E F) (shallow_definable D E F)).toChart := by
  have hI := (VariableApertureRayCancellation.annularChart
    (graphChart (secondDatum D E F hle).chart (secondDatum D E F hle).aperture)
    (aIdx (secondDatum D E F hle).chart)).domain_definable
  have hbase : Set.MapsTo (base3 D)
      (shellDomain (secondDatum D E F hle).chart (secondDatum D E F hle).aperture) D.chart.domain :=
    fun _ hx => (shell3_eq D E F hle hx).1
  have hB : TupleDef B (shellDomain (secondDatum D E F hle).chart (secondDatum D E F hle).aperture)
      (base3 D) := tupleDef_coord hI _
  have hG := tupleDef_comp (G := isoMap F) hB (isoMap_graph F) hbase
  have hτ := scalarDef_comp hB D.aperture.graph_definable hbase
  have hσ := scalarDef_comp hG E.aperture.graph_definable (fun x hx => isoMap_mem F (hbase hx))
  refine isoOfMap _ _ (deepMap D E F) ?_ ?_ ?_
  · exact tupleDef_joinMap hI (tupleDef_joinMap hI hG hσ) (scalarDef_mul hI hτ (scalarDef_coord hI _))
  · refine ⟨fun x hx => ?_, fun x hx x' hx' he => ?_, fun y hy => ?_⟩
    · obtain ⟨hu, hxe⟩ := shell3_eq D E F hle hx
      have hs := (mem_shell_iff (secondDatum D E F hle).chart (secondDatum D E F hle).aperture _ _).mp
        (hxe ▸ hx)
      have hw : gpt (base3 D x) (D.aperture.aperture (base3 D x)) ∈ (graphChart D.chart D.aperture).domain :=
        (mem_graph_iff D.chart D.aperture _ _).mpr ⟨hu, rfl⟩
      have hr := codeValue_ratio D E F hw
      rw [gpt_head] at hr
      have hτ1 := D.aperture.nonnegative _ hu
      have hs2 : codeValue (x (sIdx (endpointChart D.chart D.coordinate D.finite D.aperture))) ≤
          codeValue (E.aperture.aperture (isoMap F (base3 D x))) *
            (codeValue (D.aperture.aperture (base3 D x)))⁻¹ := hr ▸ hs.2.2.2
      have htn := BlowupChart.nonzero_mul (D.aperture.nonzero _ hu) hs.2.1
      have hcv := GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hu) hs.2.1
      have hdeep : deepMap D E F x ∈ shellDomain E.chart E.aperture := by
        refine (mem_shell_iff E.chart E.aperture _ _).mpr ⟨isoMap_mem F hu, htn, ?_, ?_⟩
        · rw [hcv]
          exact one_lt_mul_of_le_of_lt' hτ1 hs.2.2.1
        · rw [hcv, mul_comm]
          exact le_mul_inv_iff_mul_le.mp hs2
      refine ⟨hdeep, fun hsh => ?_⟩
      have h := hsh.2
      change codeValue (deepMap D E F x (sIdx E.chart)) ≤
        codeValue (D.aperture.aperture (finv F (deepMap D E F x ∘ xIdx E.chart))) at h
      rw [deepMap, gpt2_sIdx, gpt2_xIdxR,
        show finv F (isoMap F (base3 D x)) = base3 D x from isoMap_symm_isoMap F hu, hcv] at h
      exact absurd h (not_le.mpr (lt_mul_of_one_lt_right' _ hs.2.2.1))
    · obtain ⟨hu, hxe⟩ := shell3_eq D E F hle hx
      obtain ⟨hu', hxe'⟩ := shell3_eq D E F hle hx'
      have hs := (mem_shell_iff (secondDatum D E F hle).chart (secondDatum D E F hle).aperture _ _).mp
        (hxe ▸ hx)
      have hs' := (mem_shell_iff (secondDatum D E F hle).chart (secondDatum D E F hle).aperture _ _).mp
        (hxe' ▸ hx')
      have h1 := gpt_injective he
      have h2 := gpt_injective h1.1
      have huu : base3 D x = base3 D x' := (isoMap_bijOn F).2.1 hu hu' h2.1
      have hmul := h1.2
      rw [huu] at hmul
      have hss := AnnularBlowup.rvMul_right_cancel hs.2.1.1 hs'.2.1.1 (D.aperture.nonzero _ hu')
        (by rw [rvMul_comm hs.2.1.1 (D.aperture.nonzero _ hu').1,
          rvMul_comm hs'.2.1.1 (D.aperture.nonzero _ hu').1]; exact hmul)
      rw [hxe, hxe', huu, hss]
    · obtain ⟨hyS, hnot⟩ := hy
      have hp := shell_points E.chart E.aperture hyS
      have hs := (mem_shell_iff E.chart E.aperture _ _).mp ((shell_eq E.chart E.aperture hyS) ▸ hyS)
      let v := y ∘ xIdx E.chart
      let t := y (sIdx E.chart)
      let u := finv F v
      have hu : u ∈ D.chart.domain := isoMap_mem (RVMeasuredIsomorphisms.symm F) hp.1
      have hfu : isoMap F u = v := isoMap_isoMap_symm F hp.1
      have hlt : codeValue (D.aperture.aperture u) < codeValue t :=
        lt_of_not_ge (fun hle' => hnot ⟨hyS, hle'⟩)
      have hτn := D.aperture.nonzero _ hu
      let s' := rvDiv (hM := hM) t (D.aperture.aperture u)
      have hs'n : NonzeroRV s' := rvDiv_nonzero hs.2.1 hτn
      have hcs : codeValue s' = codeValue t * (codeValue (D.aperture.aperture u))⁻¹ :=
        codeValue_rvDiv hs.2.1 hτn
      have hw : gpt u (D.aperture.aperture u) ∈ (graphChart D.chart D.aperture).domain :=
        (mem_graph_iff D.chart D.aperture _ _).mpr ⟨hu, rfl⟩
      have hr := codeValue_ratio D E F hw
      rw [gpt_head, hfu] at hr
      have hmem := mem_shell3 D E F hle hu hs'n
        (by rw [hcs]; exact lt_mul_inv_iff_mul_lt.mpr (by rw [one_mul]; exact hlt))
        (by rw [hcs, hr]; exact mul_le_mul_left hs.2.2.2 _)
      refine ⟨_, hmem, ?_⟩
      change deepMap D E F _ = y
      rw [deepMap, base3_gpt,
        gpt2_sIdx (endpointChart D.chart D.coordinate D.finite D.aperture) (gpt u (D.aperture.aperture u)), hfu,
        rvMul_comm hτn.1 hs'n.1, rvDiv_mul hs.2.1.1 hτn]
      exact (shell_eq E.chart E.aperture hyS).symm
  · intro x hx
    obtain ⟨hu, hxe⟩ := shell3_eq D E F hle hx
    have hs := (mem_shell_iff (secondDatum D E F hle).chart (secondDatum D E F hle).aperture _ _).mp
      (hxe ▸ hx)
    have hw : gpt (base3 D x) (D.aperture.aperture (base3 D x)) ∈ (graphChart D.chart D.aperture).domain :=
      (mem_graph_iff D.chart D.aperture _ _).mpr ⟨hu, rfl⟩
    have hdeep : deepMap D E F x ∈ shellDomain E.chart E.aperture := by
      have hr := codeValue_ratio D E F hw
      rw [gpt_head] at hr
      have hs2 : codeValue (x (sIdx (endpointChart D.chart D.coordinate D.finite D.aperture))) ≤
          codeValue (E.aperture.aperture (isoMap F (base3 D x))) *
            (codeValue (D.aperture.aperture (base3 D x)))⁻¹ := hr ▸ hs.2.2.2
      have hcv := GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hu) hs.2.1
      refine (mem_shell_iff E.chart E.aperture _ _).mpr ⟨isoMap_mem F hu,
        BlowupChart.nonzero_mul (D.aperture.nonzero _ hu) hs.2.1, ?_, ?_⟩
      · rw [hcv]
        exact one_lt_mul_of_le_of_lt' (D.aperture.nonnegative _ hu) hs.2.2.1
      · rw [hcv, mul_comm]
        exact le_mul_inv_iff_mul_le.mp hs2
    change (shellChart (secondDatum D E F hle).chart (secondDatum D E F hle).coordinate
        (secondDatum D E F hle).finite (secondDatum D E F hle).aperture).correctedWeight x =
      (shellChart E.chart E.coordinate E.finite E.aperture).correctedWeight (deepMap D E F x)
    rw [shell_weight _ _ _ _ x hx, shell_weight E.chart E.coordinate E.finite E.aperture _ hdeep]
    have hxw : x ∘ xIdx (secondDatum D E F hle).chart = gpt (base3 D x) (D.aperture.aperture (base3 D x)) := by
      conv_lhs => rw [hxe]
      exact gpt2_xIdxR _ _ _ _
    have hew : (secondDatum D E F hle).chart.correctedWeight (gpt (base3 D x) (D.aperture.aperture (base3 D x))) =
        D.chart.correctedWeight (base3 D x) * codeValue (D.aperture.aperture (base3 D x)) := by
      have h := endpoint_weight D.chart D.coordinate D.finite D.aperture _ hw
      rw [gpt_head, show gpt (base3 D x) (D.aperture.aperture (base3 D x)) (aIdx D.chart) =
        D.aperture.aperture (base3 D x) from gpt_last _ _] at h
      exact h
    rw [hxw, hew]
    change _ = E.chart.correctedWeight (deepMap D E F x ∘ xIdx E.chart) *
      codeValue (deepMap D E F x (sIdx E.chart))
    rw [deepMap, gpt2_sIdx, gpt2_xIdxR, ← isoMap_weight F _ hu,
      GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hu) hs.2.1, mul_assoc]
    rfl

end Deep

/-! ### Lemma 7.5 -/

/-- The one-sided comparison: if `γ_U ≤ γ_V ∘ F` everywhere, then a blowup of
length one of `U^♭` (at its endpoint graph, with the ratio aperture) has the class
of `V^♭`. -/
theorem step_of_le (D E : AnnularDatum B k) (F : Iso D.chart E.chart)
    (hle : ∀ u ∈ D.chart.domain,
      codeValue (D.aperture.aperture u) ≤ codeValue (E.aperture.aperture (isoMap F u))) :
    Step (cls D.annularObject) (cls E.annularObject) := by
  have h1 := step_add_left (cls (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded))
    (step_elem (secondDatum D E F hle))
  refine step_congr ?_ ?_ h1
  · rw [cls_annular]
    rfl
  · rw [cls_annular (secondDatum D E F hle), cls_annular E,
      cls_partition (shellE E) (shallow D E F) (shallow_definable D E F),
      ← cls_eq_of_iso (a := shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
        (shallowIso D E F hle),
      ← cls_eq_of_iso (a := shellBounded (secondDatum D E F hle).chart (secondDatum D E F hle).coordinate
          (secondDatum D E F hle).finite (secondDatum D E F hle).aperture (secondDatum D E F hle).bounded)
        (deepIso D E F hle),
      cls_eq_of_iso (a := endpointBounded (secondDatum D E F hle).chart (secondDatum D E F hle).coordinate
          (secondDatum D E F hle).finite (secondDatum D E F hle).aperture (secondDatum D E F hle).bounded)
        (b := endpointBounded E.chart E.coordinate E.finite E.aperture E.bounded)
        (endpointIso D E F hle)]
    abel

/-- The inverse of `F` between the complementary pieces. -/
def complIso (D E : AnnularDatum B k) (F : Iso D.chart E.chart) (I : Set (Fin D.chart.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I) :
    Iso (cresChart E.chart (image F I) (image_definable F I hI)) (cresChart D.chart I hI) := by
  refine isoOfMap _ _ (finv (a := D.chart) (b := E.chart) F) ?_ ?_ ?_
  · exact graph_diff_definable _ _ _ (isoMap_graph (RVMeasuredIsomorphisms.symm F)) (image_definable F I hI)
  · refine ⟨fun v hv => ⟨isoMap_mem (RVMeasuredIsomorphisms.symm F) hv.1, fun hi => hv.2 ?_⟩,
      fun v hv v' hv' he => (isoMap_bijOn (RVMeasuredIsomorphisms.symm F)).2.1 hv.1 hv'.1 he,
      fun u hu => ⟨isoMap (a := D.chart) (b := E.chart) F u, ⟨isoMap_mem F hu.1, fun hv => ?_⟩,
        isoMap_symm_isoMap F hu.1⟩⟩
    · exact ⟨_, ⟨isoMap_mem (RVMeasuredIsomorphisms.symm F) hv.1, hi⟩, isoMap_isoMap_symm F hv.1⟩
    · obtain ⟨u', hu', he⟩ := hv
      have := (isoMap_bijOn F).2.1 hu'.1 hu.1 he
      exact hu.2 (this ▸ hu'.2)
  · exact fun v hv => isoMap_weight (RVMeasuredIsomorphisms.symm F) v hv.1

/-- Lemma 7.5 (`elementary:blowups:preserves:iso:vol`) on classes: elementary
blowups of isomorphic objects, in possibly different coordinates, have blowups of
length one with a common class. -/
theorem elementaryDiamond : ElementaryDiamond B k := by
  intro D E h
  obtain ⟨F⟩ := cls_eq_iff.mp h
  change Iso D.chart E.chart at F
  have hτ : ScalarDef B D.chart.domain D.aperture.aperture := D.aperture.graph_definable
  have hσF : ScalarDef B D.chart.domain (fun u => E.aperture.aperture (isoMap F u)) :=
    scalarDef_comp (isoMap_graph F) E.aperture.graph_definable (fun _ hu => isoMap_mem F hu)
  let I := {u | u ∈ D.chart.domain ∧
    codeValue (D.aperture.aperture u) ≤ codeValue (E.aperture.aperture (isoMap F u))}
  have hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I :=
    le_definable D.chart.domain_definable hτ hσF (fun u hu => D.aperture.nonzero u hu)
      (fun u hu => E.aperture.nonzero _ (isoMap_mem F hu))
  have hJ := image_definable F I hI
  have hA1 := step_of_le (datumRes D I hI) (datumRes E (image F I) hJ) (restrictIso F I hI)
    (fun u hu => by
      have he : isoMap (restrictIso F I hI) u = isoMap F u := isoMap_on (restrictIso F I hI) ⟨u, hu⟩
      rw [he]
      exact hu.2.2)
  have hA2 := step_of_le (datumCres E (image F I) hJ) (datumCres D I hI) (complIso D E F I hI)
    (fun v hv => by
      have he : isoMap (complIso D E F I hI) v = finv F v :=
        (isoMap_on (complIso D E F I hI) ⟨v, hv⟩).trans rfl
      rw [he]
      have hu := isoMap_mem (RVMeasuredIsomorphisms.symm F) hv.1
      have hnot : finv F v ∉ I := fun hi =>
        hv.2 ⟨_, ⟨hu, hi⟩, isoMap_isoMap_symm F hv.1⟩
      have hlt : codeValue (E.aperture.aperture (isoMap F (finv F v))) <
          codeValue (D.aperture.aperture (finv F v)) := lt_of_not_ge (fun hle => hnot ⟨hu, hle⟩)
      rw [isoMap_isoMap_symm F hv.1] at hlt
      exact hlt.le)
  refine ⟨cls (datumRes E (image F I) hJ).annularObject + cls (datumCres D I hI).annularObject, ?_, ?_⟩
  · rw [cls_annular_split D I hI]
    exact step_add hA1 (step_refl _)
  · rw [cls_annular_split E (image F I) hJ]
    exact step_add (step_refl _) hA2

/-- Lemma 7.5 for objects: if `U ≅ V` and `U^♭`, `V^♭` are elementary blowups of
`U`, `V`, in possibly different coordinates, then there are blowups of `U^♭`,
`V^♭` of length one with isomorphic results. -/
theorem lemma_7_5 (D E : AnnularDatum B k) (h : Nonempty (Iso D.source.toChart E.source.toChart)) :
    ∃ w : Cls B (1 + k), Step (cls D.annularObject) w ∧ Step (cls E.annularObject) w :=
  elementaryDiamond D E (cls_eq_iff.mpr h)

end DiamondIntegral.Section7.ElementaryComparison
