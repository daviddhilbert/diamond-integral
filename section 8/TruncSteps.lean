import «section 8».TruncChain
import «section 6».SpecialCovariantChains
import «section 6».InvariantValueBounds
import «section 6».MixedFocusCovariance
import «section 6».CentripetalUniformFocusBounds

/-! The steps of a special covariant chain respect congruence at cofinally many cutoffs.

* `regularize_compat`: `(x, u) ↦ (x, rv x, u)` once the cutoffs exceed a named upper bound of the
  valuations (then `rv x` is determined by the truncation);
* `zeroCentered_compat`: the translation by the center on the core once the cutoffs exceed `v(c)`;
* `centripetal_compat`: `x_j ↦ x_j − λ(x̂) (+ cλ(x̂))` with anisotropic cutoffs: first `β_j` above
  `v(cλ)`, then `β_i` (`i ≠ j`) from the uniform covariance of the focus for the radius `π^{β_j}`.
  The focus at a moved point is evaluated through the source point with the same active coordinate,
  which lies in the source by its invariance (no RV-pullback hypothesis is needed). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section6
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells

local instance stepsStructure : LRV.Structure Carrier := canonicalInterpret
local instance stepsModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient) {n : ℕ} (m : ℕ+)

local notation "π" => uniformizerValue P

/-! ### Named values -/

theorem rad_gt {L : ℕ} {b : Fin n → ℕ} {q : ℚ} (h : ∀ i, q ≤ lev m (b i) - L) (i : Fin n) :
    (qpow π q).val ≤ (rad P m b L i).val :=
  (Hm.qpow_le_iff P).mpr (h i)

/-- **The value of a named nonzero field element is a rational power of `π`.** -/
theorem vf_point_rational {c : VFType (M := P.N)} (hc0 : c ≠ 0)
    (hc : (P.G.real : Set P.N).Definable₁ LRV {c.val}) :
    ∃ q : ℚ, Values.vfValueHom c = (qpow π q).val := by
  have hne : ({y : Fin 1 → P.N | y 0 ∈ ({c.val} : Set P.N)} : Set (Fin 1 → P.N)).Nonempty :=
    ⟨fun _ => c.val, rfl⟩
  obtain ⟨c0, hc0'⟩ := concrete_witness P hc hne
  have he : P.e (c0 0) = c.val := hc0'
  have hvf : sortEval .vf (c0 0) := (e_sort P .vf (c0 0)).mp (he ▸ c.property)
  obtain ⟨g, hg⟩ : ∃ g : Ser, c0 0 = Sum.inl g := by
    rcases h : c0 0 with g | r
    · exact ⟨g, rfl⟩
    · rw [h] at hvf
      exact hvf.elim
  have hcg : c = eVF P g := Subtype.ext (by rw [← he, hg]; rfl)
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hc0
    rw [hcg, eVF_eq, map_zero]
  exact ⟨_, hcg ▸ value_eVF P g hg0⟩

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-! ### Regularization -/

include hv in
theorem regularize_compat {r : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N))
    (hA : ProperInvariant (P.G.real : Set P.N) A.carrier) (hVF : VFDoublyBounded A.carrier) :
    StepCompat P m (regularization A) := by
  intro L b0
  obtain ⟨δ, hδ, -, -, hup⟩ := properInvariant_uniform_named_upper_vf_bound P.G.model00 P.hc
    (DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := P.N)) P.G.uncountable
    P.G.saturated hv P.G.small_real (Hm.base_nontrivial P) hA hVF
  obtain ⟨q, rfl⟩ := named_rational P hδ
  obtain ⟨b, hb, hbq⟩ := exists_cutoff m q L b0
  refine ⟨b, hb, fun a a' hc hl => ⟨hc, ?_⟩, fun a a' hc hl => ⟨hc, ?_⟩⟩
  · simp only [regularization_apply, regularize]
    rw [hl]
    congr 1
    funext i
    exact rv_eq_of_close_at_radius (qpow π q) (hup a'.val a'.property i)
      (lt_of_le_of_lt (rad_gt P m hbq i) (hc i))
  · funext j
    have := congrFun hl (Fin.natAdd n j)
    simpa only [regularization_apply, regularize, Fin.append_right] using this

/-! ### Zero-centred translations -/

theorem lt_value_of_close {g : Values.GammaTop (M := P.N)} {x y : VFType (M := P.N)}
    (hxy : g < Values.vfValueHom (x - y)) (hx : g < Values.vfValueHom x) : g < Values.vfValueHom y := by
  have h := vfValue_min_le_sub x (x - y)
  rw [sub_sub_cancel] at h
  exact lt_of_lt_of_le (lt_min hx hxy) h

theorem zeroCentered_compat {r : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N))
    (D : ZeroCenteredData A) : StepCompat P m D.bijection := by
  intro L b0
  obtain ⟨q, hq⟩ := vf_point_rational P D.center_nonzero D.center_definable
  obtain ⟨b, hb, hbq⟩ := exists_cutoff m (q + 1) L b0
  have hlt : ∀ i, Values.vfValueHom D.center < (rad P m b L i).val := by
    intro i
    rw [hq]
    exact (Hm.qpow_lt_iff P).mpr (by linarith [hbq i])
  have key : ∀ (x x' : Fin n → VF P.N), Congruent (rad P m b L) x x' → ∀ i,
      vfValue D.center < vfValue (x i) → vfValue D.center < vfValue (x' i) :=
    fun x x' hc i h => lt_value_of_close P (lt_trans (hlt i) (hc i)) h
  have hcore : ∀ (p p' : Mixed P.N n r), Congruent (rad P m b L) p.1 p'.1 → D.core p = D.core p' := by
    intro p p' hc
    funext i
    exact decide_eq_decide.mpr ⟨key p.1 p'.1 hc i, key p'.1 p.1 hc.symm i⟩
  have hdiff : ∀ (p p' : Mixed P.N n r), D.core p = D.core p' → ∀ i,
      (D.point p).1 i - (D.point p').1 i = p.1 i - p'.1 i := by
    intro p p' he i
    change (p.1 i + D.shift (D.core p) i) - (p'.1 i + D.shift (D.core p') i) = _
    rw [he, add_sub_add_right_eq_sub]
  refine ⟨b, hb, fun a a' hc hl => ?_, fun a a' hc hl => ?_⟩
  · have he := hcore a.val a'.val hc
    refine ⟨fun i => ?_, ?_⟩
    · change (rad P m b L i).val < Values.vfValueHom ((D.point a.val).1 i - (D.point a'.val).1 i)
      rw [hdiff a.val a'.val he i]
      exact hc i
    · change D.tags a.val.2 (D.core a.val) = D.tags a'.val.2 (D.core a'.val)
      rw [hl, he]
  · change D.tags a.val.2 (D.core a.val) = D.tags a'.val.2 (D.core a'.val) at hl
    have hu : a.val.2 = a'.val.2 := funext fun j => by
      simpa only [ZeroCenteredData.tags, Fin.append_right] using congrFun hl (Fin.natAdd n j)
    have he : D.core a.val = D.core a'.val := funext fun i => by
      apply branchTag_injective P.G.model00
      simpa only [ZeroCenteredData.tags, Fin.append_left] using congrFun hl (Fin.castAdd r i)
    refine ⟨fun i => ?_, hu⟩
    have := hc i
    change (rad P m b L i).val < Values.vfValueHom ((D.point a.val).1 i - (D.point a'.val).1 i) at this
    rw [hdiff a.val a'.val he i] at this
    exact this

/-! ### Centripetal steps -/

theorem qpow_add' (a c : ℚ) : qpow π (a + c) = qpow π a * qpow π c :=
  ι_injective (by rw [ι_mul, ι_qpow, ι_qpow, ι_qpow, add_smul])

theorem vfValue_eq_of_rv_eq {x y : VF P.N} (h : rv P.N x = rv P.N y) : vfValue x = vfValue y := by
  change Values.vrv (CanonicalRV.encodedRv x) = Values.vrv (CanonicalRV.encodedRv y)
  congr 1

theorem value_mul_lt {x y : VF P.N} {a c d : ℚ} (hx : vfValue x = (qpow π a).val)
    (hy : vfValue y ≤ (qpow π c).val) (h : a + c < d) : vfValue (x * y) < (qpow π d).val := by
  change Values.vfValueHom (x * y) < _
  rw [map_mul]
  change vfValue x * vfValue y < _
  rw [hx]
  calc (qpow π a).val * vfValue y ≤ (qpow π a).val * (qpow π c).val := mul_le_mul_right hy _
    _ = (qpow π (a + c)).val := by rw [qpow_add']; rfl
    _ < (qpow π d).val := (Hm.qpow_lt_iff P).mpr h

theorem value_mul_ge {x y : VF P.N} (hx : 1 ≤ vfValue x) : vfValue y ≤ vfValue (x * y) := by
  change Values.vfValueHom y ≤ Values.vfValueHom (x * y)
  rw [map_mul]
  calc Values.vfValueHom y = 1 * Values.vfValueHom y := (one_mul _).symm
    _ ≤ Values.vfValueHom x * Values.vfValueHom y := mul_le_mul_left hx _

theorem value_add_gt' {g : Values.GammaTop (M := P.N)} {x y : VF P.N}
    (hx : g < vfValue x) (hy : g < vfValue y) : g < vfValue (x + y) := by
  have h := vfValue_min_le_sub x (-y)
  rw [sub_neg_eq_add, vfValue_neg] at h
  exact lt_of_lt_of_le (lt_min hx hy) h

theorem value_sub_gt' {g : Values.GammaTop (M := P.N)} {x y : VF P.N}
    (hx : g < vfValue x) (hy : g < vfValue y) : g < vfValue (x - y) :=
  lt_of_lt_of_le (lt_min hx hy) (vfValue_min_le_sub x y)

include hv in
/-- **Centripetal steps respect congruence at anisotropic cutoffs.** -/
theorem centripetal_compat {r : ℕ} (A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N))
    (D : CentripetalData (G := Gv) A) : StepCompat P m D.bijection := by
  intro L b0
  let lin := DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := P.N)
  obtain ⟨δu, hδu, -, -, hup⟩ := properInvariant_uniform_named_upper_vf_bound P.G.model00 P.hc lin
    P.G.uncountable P.G.saturated hv P.G.small_real (Hm.base_nontrivial P) D.sourceProper D.sourceDoublyBounded
  obtain ⟨qu, rfl⟩ := named_rational P hδu
  obtain ⟨qc, hqc⟩ := vf_point_rational P D.coefficient_nonzero D.coefficient_definable
  have hqc0 : 0 ≤ qc := by
    have h1 := D.coefficient_nonnegative
    change (1 : Values.GammaTop (M := P.N)) ≤ Values.vfValueHom D.coefficient at h1
    rw [hqc] at h1
    have h2 : (qpow π 0 : Values.Gamma (M := P.N)) ≤ qpow π qc := by
      rw [Hm.qpow_zero' P]
      exact h1
    exact (Hm.qpow_le_iff P).mp h2
  obtain ⟨qA, hqA⟩ := amb_invariant P Gv hv m A D.sourceProper
  obtain ⟨b1, hb1, hb1q⟩ := exists_cutoff m (max (qc + qu + 1) qA) L b0
  set ρ : Values.Gamma (M := P.N) := qpow π (lev m (b1 D.coordinate) - L) with hρdef
  have hρ : (P.G.real : Set P.N).Definable LRV {z : Fin 1 → P.N | z 0 ∈ Values.gammaPullback {ρ}} :=
    (DiamondIntegral.Section6.gamma_real_codes_iff P.hc (P.G.real : Set P.N) {ρ}).mp (qpow_definable P _)
  obtain ⟨δ, hδ, -, hcov⟩ := continuous_mixed_focus_uniform_named_covariance P.G.model00 P.hc lin
    P.G.uncountable P.G.saturated hv P.G.small_real (Hm.base_nontrivial P) D.focusMap
    (focusActive_properInvariant A D.sourceProper D.activeTags) D.focusMap_continuous ρ hρ
  obtain ⟨qδ, rfl⟩ := named_rational P hδ
  obtain ⟨b2, hb2, hb2q⟩ := exists_cutoff m (max qδ qA) L b0
  let b : Fin n → ℕ := Function.update b2 D.coordinate (b1 D.coordinate)
  have hbj : b D.coordinate = b1 D.coordinate := Function.update_self _ _ _
  have hbi : ∀ i, i ≠ D.coordinate → b i = b2 i := fun i hi => Function.update_of_ne hi _ _
  have hb0 : ∀ i, b0 i ≤ b i := by
    intro i
    by_cases hi : i = D.coordinate
    · rw [hi, hbj]; exact hb1 _
    · rw [hbi i hi]; exact hb2 i
  have hradj : rad P m b L D.coordinate = ρ := by simp only [rad, hbj, hρdef]
  have hqAb : ∀ i, qA ≤ lev m (b i) - L := by
    intro i
    by_cases hi : i = D.coordinate
    · rw [hi, hbj]; exact le_trans (le_max_right _ _) (hb1q _)
    · rw [hbi i hi]; exact le_trans (le_max_right _ _) (hb2q i)
  have hinvA := hqA L b hqAb
  have hδb : ∀ i, i ≠ D.coordinate → (qpow π qδ).val ≤ (rad P m b L i).val := by
    intro i hi
    have he : rad P m b L i = qpow π (lev m (b2 i) - L) := by simp only [rad, hbi i hi]
    rw [he]
    exact (Hm.qpow_le_iff P).mpr (le_trans (le_max_left _ _) (hb2q i))
  have hρbig : qc + qu < lev m (b1 D.coordinate) - L := by
    have := le_trans (le_max_left _ _) (hb1q D.coordinate)
    linarith
  have hquρ : (qpow π qu).val ≤ ρ.val := (Hm.qpow_le_iff P).mpr (by linarith)
  -- the focus at two close points
  have hfocus : ∀ (x x' : Fin n → VF P.N) (u : Fin r → RVInfinity P.N), (x, u) ∈ A.carrier →
      (x', u) ∈ A.carrier → u ∈ D.activeTags.carrier →
      (∀ i, i ≠ D.coordinate → (rad P m b L i).val < vfValue (x i - x' i)) →
      ρ.val < vfValue (D.focus (Function.update x D.coordinate 0) u -
        D.focus (Function.update x' D.coordinate 0) u) := by
    intro x x' u hx hx' hu hc
    let c := Function.update x' D.coordinate (x D.coordinate)
    have hxc : Congruent (rad P m b L) x c := by
      intro i
      by_cases hi : i = D.coordinate
      · rw [hi]
        simp only [c, Function.update_self, sub_self]
        exact gamma_lt_value_zero _
      · simp only [c, Function.update_of_ne hi]
        exact hc i hi
    have hcA : (c, u) ∈ A.carrier := hinvA (x, u) hx c hxc
    have hClose : Congruent (fun _ => qpow π qδ) x c := by
      intro i
      by_cases hi : i = D.coordinate
      · rw [hi]
        simp only [c, Function.update_self, sub_self]
        exact gamma_lt_value_zero _
      · simp only [c, Function.update_of_ne hi]
        exact lt_of_le_of_lt (hδb i hi) (hc i hi)
    have h := (hcov u).2 x ⟨hx, hu⟩ c ⟨hcA, hu⟩ hClose 0
    rw [totalFocusFibre_at D.focusMap u x ⟨hx, hu⟩, totalFocusFibre_at D.focusMap u c ⟨hcA, hu⟩] at h
    rw [D.focusMap_eq ⟨(x, u), hx, hu⟩, D.focusMap_eq ⟨(c, u), hcA, hu⟩] at h
    simpa only [c, Function.update_idem] using h
  have hcf : ∀ p : Mixed P.N n r, D.extendedFocus p = 0 → D.core p = false := by
    intro p hp
    unfold CentripetalData.core
    rw [hp, mul_zero, decide_eq_false_iff_not, value_zero]
    exact not_lt.mpr (Values.le_infinity _)
  have hpt : ∀ p : Mixed P.N n r, D.extendedFocus p = 0 → (D.point p).1 = p.1 := by
    intro p hp
    simp only [CentripetalData.point, hp, hcf p hp, sub_zero, Bool.false_eq_true, ite_false, add_zero]
    exact Function.update_eq_self _ _
  refine ⟨b, hb0, ?_, ?_⟩
  · intro a a' hc hl
    have ha := a.property
    have ha' : (a'.val.1, a.val.2) ∈ A.carrier := by rw [hl]; exact a'.property
    by_cases hu : a.val.2 ∈ D.activeTags.carrier
    · have hu' : a'.val.2 ∈ D.activeTags.carrier := hl ▸ hu
      have hlam : D.extendedFocus a.val = D.focus (Function.update a.val.1 D.coordinate 0) a.val.2 :=
        D.extendedFocus_active ha hu
      have hlam' : D.extendedFocus a'.val = D.focus (Function.update a'.val.1 D.coordinate 0) a'.val.2 :=
        D.extendedFocus_active a'.property hu'
      have hclose := hfocus a.val.1 a'.val.1 a.val.2 ha ha' hu (fun i _ => hc i)
      have hlam'' := hlam'
      rw [← hl] at hlam''
      rw [← hlam'', ← hlam] at hclose
      have hvl : vfValue (D.extendedFocus a.val) = vfValue (a.val.1 D.coordinate) := by
        rw [hlam]; exact vfValue_eq_of_rv_eq P (D.focusRV a.val ha hu)
      have hvl' : vfValue (D.extendedFocus a'.val) = vfValue (a'.val.1 D.coordinate) := by
        rw [hlam']; exact vfValue_eq_of_rv_eq P (D.focusRV a'.val a'.property hu')
      have hlu : vfValue (D.extendedFocus a.val) ≤ (qpow π qu).val := hvl ▸ hup a.val ha D.coordinate
      have hlu' : vfValue (D.extendedFocus a'.val) ≤ (qpow π qu).val :=
        hvl' ▸ hup a'.val a'.property D.coordinate
      have hK : vfValue (D.coefficient * D.extendedFocus a.val) < ρ.val := value_mul_lt P hqc hlu hρbig
      have hKK : vfValue (D.coefficient * D.extendedFocus a.val) =
          vfValue (D.coefficient * D.extendedFocus a'.val) := by
        have hr := rv_eq_of_close_at_radius ρ (le_trans hlu' hquρ) hclose
        change Values.vfValueHom (D.coefficient * D.extendedFocus a.val) =
          Values.vfValueHom (D.coefficient * D.extendedFocus a'.val)
        rw [map_mul, map_mul]
        change Values.vfValueHom D.coefficient * vfValue (D.extendedFocus a.val) =
          Values.vfValueHom D.coefficient * vfValue (D.extendedFocus a'.val)
        rw [vfValue_eq_of_rv_eq P hr]
      have hA01 : ρ.val < vfValue ((a.val.1 D.coordinate - D.extendedFocus a.val) -
          (a'.val.1 D.coordinate - D.extendedFocus a'.val)) := by
        have he : (a.val.1 D.coordinate - D.extendedFocus a.val) - (a'.val.1 D.coordinate - D.extendedFocus a'.val) =
            (a.val.1 D.coordinate - a'.val.1 D.coordinate) - (D.extendedFocus a.val - D.extendedFocus a'.val) := by
          ring
        rw [he]
        have hcj := hc D.coordinate
        rw [hradj] at hcj
        exact value_sub_gt' P hcj hclose
      have hcore : D.core a.val = D.core a'.val := by
        unfold CentripetalData.core
        apply decide_eq_decide.mpr
        rw [← hKK]
        by_cases h0 : vfValue (a.val.1 D.coordinate - D.extendedFocus a.val) ≤ ρ.val
        · have h01' : ρ.val < vfValue ((a'.val.1 D.coordinate - D.extendedFocus a'.val) -
              (a.val.1 D.coordinate - D.extendedFocus a.val)) := by
            change ρ.val < Values.vfValueHom _
            rw [vfValue_sub_comm]
            exact hA01
          have hr := rv_eq_of_close_at_radius ρ h0 h01'
          rw [vfValue_eq_of_rv_eq P hr]
        · push Not at h0
          have h1 : ρ.val < vfValue (a'.val.1 D.coordinate - D.extendedFocus a'.val) :=
            lt_value_of_close P hA01 h0
          exact iff_of_true (lt_trans hK h0) (lt_trans hK h1)
      refine ⟨fun i => ?_, ?_⟩
      · change (rad P m b L i).val < vfValue ((D.point a.val).1 i - (D.point a'.val).1 i)
        by_cases hi : i = D.coordinate
        · rw [hi, hradj]
          simp only [CentripetalData.point, Function.update_self]
          rw [hcore]
          cases hcv : D.core a'.val
          · simp only [Bool.false_eq_true, ite_false, add_zero]
            exact hA01
          · simp only [ite_true]
            have he : (a.val.1 D.coordinate - D.extendedFocus a.val + D.coefficient * D.extendedFocus a.val) -
                (a'.val.1 D.coordinate - D.extendedFocus a'.val + D.coefficient * D.extendedFocus a'.val) =
                ((a.val.1 D.coordinate - D.extendedFocus a.val) - (a'.val.1 D.coordinate - D.extendedFocus a'.val)) +
                  D.coefficient * (D.extendedFocus a.val - D.extendedFocus a'.val) := by ring
            rw [he]
            exact value_add_gt' P hA01 (lt_of_lt_of_le hclose (value_mul_ge P D.coefficient_nonnegative))
        · simp only [CentripetalData.point, Function.update_of_ne hi]
          exact hc i
      · change Fin.append (fun _ : Fin 1 => branchTag (D.core a.val)) a.val.2 =
          Fin.append (fun _ : Fin 1 => branchTag (D.core a'.val)) a'.val.2
        rw [hcore, hl]
    · have hu' : a'.val.2 ∉ D.activeTags.carrier := hl ▸ hu
      have h0 : D.extendedFocus a.val = 0 := D.extendedFocus_inactive hu
      have h0' : D.extendedFocus a'.val = 0 := D.extendedFocus_inactive hu'
      refine ⟨fun i => ?_, ?_⟩
      · change (rad P m b L i).val < vfValue ((D.point a.val).1 i - (D.point a'.val).1 i)
        rw [hpt _ h0, hpt _ h0']
        exact hc i
      · change Fin.append (fun _ : Fin 1 => branchTag (D.core a.val)) a.val.2 =
          Fin.append (fun _ : Fin 1 => branchTag (D.core a'.val)) a'.val.2
        rw [hcf _ h0, hcf _ h0', hl]
  · intro a a' hc hl
    change Fin.append (fun _ : Fin 1 => branchTag (D.core a.val)) a.val.2 =
      Fin.append (fun _ : Fin 1 => branchTag (D.core a'.val)) a'.val.2 at hl
    have hu : a.val.2 = a'.val.2 := funext fun k => by
      simpa only [Fin.append_right] using congrFun hl (Fin.natAdd 1 k)
    have hcore : D.core a.val = D.core a'.val := branchTag_injective P.G.model00 (by
      simpa only [Fin.append_left] using congrFun hl (Fin.castAdd r 0))
    have hother : ∀ i, i ≠ D.coordinate → (rad P m b L i).val < vfValue (a.val.1 i - a'.val.1 i) := by
      intro i hi
      have := hc i
      change _ < vfValue ((D.point a.val).1 i - (D.point a'.val).1 i) at this
      simpa only [CentripetalData.point, Function.update_of_ne hi] using this
    refine ⟨fun i => ?_, hu⟩
    by_cases hi : i = D.coordinate
    · rw [hi, hradj]
      have hcj := hc D.coordinate
      change _ < vfValue ((D.point a.val).1 D.coordinate - (D.point a'.val).1 D.coordinate) at hcj
      simp only [CentripetalData.point, Function.update_self] at hcj
      rw [hcore, hradj] at hcj
      by_cases hact : a.val.2 ∈ D.activeTags.carrier
      · have hact' : a'.val.2 ∈ D.activeTags.carrier := hu ▸ hact
        have ha' : (a'.val.1, a.val.2) ∈ A.carrier := by rw [hu]; exact a'.property
        have hclose := hfocus a.val.1 a'.val.1 a.val.2 a.property ha' hact hother
        have e' := D.extendedFocus_active a'.property hact'
        rw [← hu] at e'
        rw [← e', ← D.extendedFocus_active a.property hact] at hclose
        cases hcv : D.core a'.val
        · simp only [hcv, Bool.false_eq_true, ite_false, add_zero] at hcj
          have he : a.val.1 D.coordinate - a'.val.1 D.coordinate =
              ((a.val.1 D.coordinate - D.extendedFocus a.val) - (a'.val.1 D.coordinate - D.extendedFocus a'.val)) +
                (D.extendedFocus a.val - D.extendedFocus a'.val) := by ring
          rw [he]
          exact value_add_gt' P hcj hclose
        · simp only [hcv, ite_true] at hcj
          have he : a.val.1 D.coordinate - a'.val.1 D.coordinate =
              ((a.val.1 D.coordinate - D.extendedFocus a.val + D.coefficient * D.extendedFocus a.val) -
                (a'.val.1 D.coordinate - D.extendedFocus a'.val + D.coefficient * D.extendedFocus a'.val) +
                (D.extendedFocus a.val - D.extendedFocus a'.val)) -
                D.coefficient * (D.extendedFocus a.val - D.extendedFocus a'.val) := by ring
          rw [he]
          exact value_sub_gt' P (value_add_gt' P hcj hclose)
            (lt_of_lt_of_le hclose (value_mul_ge P D.coefficient_nonnegative))
      · have hact' : a'.val.2 ∉ D.activeTags.carrier := hu ▸ hact
        have h0 : D.extendedFocus a.val = 0 := D.extendedFocus_inactive hact
        have h0' : D.extendedFocus a'.val = 0 := D.extendedFocus_inactive hact'
        simp only [h0, h0', hcf _ h0', mul_zero, sub_zero, Bool.false_eq_true, ite_false, add_zero] at hcj
        exact hcj
    · exact hother i hi

/-! ### Chains -/

include hv in
/-- Both ends of a special covariant chain are proper invariant. -/
theorem chain_proper {r s : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)}
    {B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)} {f : Map A B}
    (h : SpecialCovariantChain (G := Gv) A B f) :
    ProperInvariant (P.G.real : Set P.N) A.carrier ∧ ProperInvariant (P.G.real : Set P.N) B.carrier := by
  let lin := DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := P.N)
  have hH := h.properHomeomorphism P.G.model00 P.hc lin P.G.uncountable P.G.saturated hv P.G.small_real
    (Hm.base_nontrivial P)
  refine ⟨?_, hH.covariant.target_properInvariant P.G.model00 P.hc lin P.G.uncountable P.G.saturated hv
    P.G.small_real (Hm.base_nontrivial P) hH.bijective.2⟩
  refine hH.inverseCovariant.target_properInvariant P.G.model00 P.hc lin P.G.uncountable P.G.saturated hv
    P.G.small_real (Hm.base_nontrivial P) fun a => ⟨f a, Map.inverse_apply f hH.bijective a⟩

include hv in
/-- **Special covariant chains preserve normalized truncation classes** (the first step of the
proof of Lemma `inv:dir:com`, with compatible cutoffs chosen for each step and its inverse). -/
theorem chain_teq {r s : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n r) (P.G.real : Set P.N)}
    {B : DefSet (rawMixedSpace (M := P.N) n s) (P.G.real : Set P.N)} {f : Map A B}
    (h : SpecialCovariantChain (G := Gv) A B f) : TEq P m A B := by
  induction h with
  | identity A hA => exact teq_refl P m A
  | regularize A hA hVF =>
      obtain ⟨hA', hB'⟩ := chain_proper P Gv hv (SpecialCovariantChain.regularize (G := Gv) A hA hVF)
      exact teq_of_step P m (good_of_proper P m Gv hv A hA') (good_of_proper P m Gv hv _ hB')
        (regularization A) (regularization_bijective A) (regularize_compat P m Gv hv A hA hVF)
  | centripetal A D =>
      obtain ⟨hA', hB'⟩ := chain_proper P Gv hv (SpecialCovariantChain.centripetal (G := Gv) A D)
      exact teq_of_step P m (good_of_proper P m Gv hv A hA') (good_of_proper P m Gv hv _ hB')
        D.bijection (D.bijective P.G.model00) (centripetal_compat P m Gv hv A D)
  | zeroCentered A D =>
      obtain ⟨hA', hB'⟩ := chain_proper P Gv hv (SpecialCovariantChain.zeroCentered (G := Gv) A D)
      exact teq_of_step P m (good_of_proper P m Gv hv A hA') (good_of_proper P m Gv hv _ hB')
        D.bijection (D.bijective P.G.model00) (zeroCentered_compat P m A D)
  | comp hf hg ihf ihg =>
      obtain ⟨hA', hB'⟩ := chain_proper P Gv hv hf
      obtain ⟨-, hC'⟩ := chain_proper P Gv hv hg
      exact teq_trans P m (good_of_proper P m Gv hv _ hA') (good_of_proper P m Gv hv _ hB')
        (good_of_proper P m Gv hv _ hC') ihf ihg

end DiamondIntegral.Section8.Truncation
