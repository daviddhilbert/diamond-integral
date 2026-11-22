import «section 8».LiftClass
import «section 8».MilnorFiber
import «section 8».Jets
import «section 8».TruncClasses

/-! **Lemma `inv:dir:com` for `𝒳_f`, and the first equality of (z:coeff:change).**

* `milnor_trace`: the concrete trace of the ambient Milnor fibre `𝒳_f` is the concrete `𝒳_f`;
* `milnor_zeta_coeff`: the `m`-th coefficient of `Z_f(T) = Σ η h_m ∫^◇[𝒳_f] T^m` is the normalized
  class `Θ(𝒳̃_f[m])` of the truncation of `𝒳_f`;
* `z_coeff_change`: with the jet identification, it is `[𝒳_m] [𝔸]^{-md}`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section4
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells
open DiamondIntegral.Section8.Milnor

local instance l86Structure : LRV.Structure Carrier := canonicalInterpret
local instance l86Model : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient) {d : ℕ}

/-! ### The trace of the ambient Milnor fibre -/

theorem eval_eVF (f : MvPolynomial (Fin d) ℂ) (x : Fin d → Ser) :
    MvPolynomial.eval (fun i => eVF P (x i)) (fN P f) =
      eVF P (MvPolynomial.eval x (MvPolynomial.map puiseuxConstant f)) := by
  rw [eVF_eq, MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left]
  rfl

theorem tS_eq_tSeries : tS = tSeries := by
  apply Subtype.ext
  change (puiseuxRoot (k := ℂ) 1 : HahnSeries ℚ ℂ) = (tSeries : HahnSeries ℚ ℂ)
  rw [puiseuxRoot_coe, tSeries_coe]
  norm_num

theorem rv_eVF_iff (y y' : Ser) :
    rv P.N (eVF P y) = rv P.N (eVF P y') ↔ rvOfField y = rvOfField y' := by
  change CanonicalRV.encodedRv (eVF P y) = CanonicalRV.encodedRv (eVF P y') ↔ _
  rw [encodedRv_eVF, encodedRv_eVF]
  constructor
  · intro h
    exact Sum.inr_injective (P.e.injective (congrArg Subtype.val h))
  · intro h
    rw [h]

theorem unscaleP_zero {k : ℕ} (p : (Fin d → Ser) × (Fin k → RV)) : unscaleP 0 p = p := by
  refine Prod.ext (funext fun i => ?_) rfl
  change tInv 0 * p.1 i = p.1 i
  rw [tInv, tPow, pow_zero, inv_one, one_mul]

/-- **The trace of the ambient `𝒳_f` is the concrete `𝒳_f`.** -/
theorem milnor_trace (f : MvPolynomial (Fin d) ℂ) :
    mixedSet (strace P 0 (milnorDefSet P f)) = mixedSet (rawMilnor f) := by
  ext p
  rw [mem_strace, mem_mixedSet_milnor, unscaleP_zero]
  change ePoint P p ∈ milnorSet P f ↔ _
  simp only [milnorSet, Set.mem_ofPred_eq]
  refine and_congr (forall_congr' fun i => ?_) ?_
  · have h := lt_value_eVF_iff P 0 (p.1 i)
    rw [Hm.qpow_zero' P] at h
    exact h
  · change rv P.N (MvPolynomial.eval (fun i => eVF P (p.1 i)) (fN P f)) = rv P.N (tN P) ↔ _
    have ht : tN P = eVF P tS := by rw [tS_eq_tSeries, eVF_eq]
    rw [eval_eVF, ht, rv_eVF_iff]

/-! ### Lift data and the integral -/

section Final

open SpecialTransformations.Section9
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondSurjectivity
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section7.Theorem726 DiamondIntegral.Section7.DiamondRing DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.BoundedClasses

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hntB : ∃ x : P.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include hv hntB in
/-- **Lift data** for an object of positive degree (Lemma 6.21 over the VF-generated base). -/
theorem exists_liftData {k : ℕ} (A : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) (k + 1)) :
    ∃ (ω : Map A.carrier (DefSet.univ (rawGammaPresentation (M := P.N)) (P.G.real : Set P.N))),
      (∀ p, (ω p).val = (A.form p).val) ∧ Nonempty (MeasuredRVLiftData (G := Gv) A.carrier ω) := by
  let ω := gammaFormExtension A.form
  have hGraph := gammaFormExtension_graph_definable A.form
  let C : Fin 1 → DefSet (rawMixedSpace (M := P.N) (k + 1) A.labels) (P.G.real : Set P.N) := fun _ => A.carrier
  have hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ} := by
    intro i γ
    have he : {p | p ∈ (C i).carrier ∧ ω p = γ} = A.levelSet γ := by
      ext p
      constructor
      · rintro ⟨hp, hγ⟩
        refine ⟨hp, ?_⟩
        have h := gammaFormExtension_at A.form ⟨p, hp⟩
        exact h.symm.trans hγ
      · rintro ⟨hp, hγ⟩
        refine ⟨hp, ?_⟩
        exact (gammaFormExtension_at A.form ⟨p, hp⟩).trans hγ
    exact he.symm ▸ A.levelSet_geometry γ
  obtain ⟨_, hT⟩ := lemma_6_21_vfGenerated (G := Gv) P.G.model00 P.hc
    (DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := P.N)) P.G.uncountable
    P.G.saturated hv P.G.real P.G.fieldBase P.G.small_real (Hm.base_nontrivial P) hntB A.carrier C
    (fun _ => le_rfl) (fun _ => A.proper) (fun p hp => ⟨0, hp⟩) ω hGraph hLevels
  obtain ⟨L, _, _⟩ := hT 0 A.finiteRV
  exact ⟨_, fun p => gammaFormExtension_at A.form p, ⟨L⟩⟩

/-- The form of the lift object is `1` when the form of the source is `1`. -/
theorem lift_form_one {k : ℕ} (A : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) k)
    (hA1 : ∀ p, gammaMapValue A.form p = 1)
    (ω : Map A.carrier (DefSet.univ (rawGammaPresentation (M := P.N)) (P.G.real : Set P.N)))
    (hω : ∀ p, (ω p).val = (A.form p).val) (L : MeasuredRVLiftData (G := Gv) A.carrier ω) :
    ∀ u, gammaMapValue (liftDataObject L).form u = 1 := by
  intro u
  obtain ⟨x, hx⟩ := SpecialTransformations.Section4.tupleRV_surjective (L.object.value u)
  let q : SpecialTransformations.Section4.rvLift L.object := ⟨(x, u.val), ⟨u, rfl, hx.symm⟩⟩
  obtain ⟨p, hp⟩ := (L.special.bijective P.G.model00).2 q
  have hlab : L.labelMap p = u := by
    apply Subtype.ext
    rw [L.label_eq p, hp]
  change gammaMapValue L.rvForm u = 1
  rw [← hlab]
  unfold gammaMapValue
  rw [L.form_preserves p, hω p]
  exact hA1 p

include hntB in
/-- **`∫^◇[A]` is the class of the lift object of any lift data of `A`.** -/
theorem integral_lift {k : ℕ} (A : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) (k + 1))
    (ω : Map A.carrier (DefSet.univ (rawGammaPresentation (M := P.N)) (P.G.real : Set P.N)))
    (hω : ∀ p, (ω p).val = (A.form p).val) (L : MeasuredRVLiftData (G := Gv) A.carrier ω) :
    theorem_7_26_graded Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real P.G.small_real
        (Hm.base_nontrivial P) P.G.fieldBase hntB
        (ringClass Gv P.hc (unitObj Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv
          P.G.real P.G.small_real (Hm.base_nontrivial P)) A) =
      RelativeAnnularQuotient.quotient (base P) (RVBoundedRing.objectClass
        (objOf P.hc P.G.real (liftDataObject L) (liftDataObject_doublyBounded L))) := by
  let lin := DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := P.N)
  set U := liftDataObject L
  have hU := liftDataObject_doublyBounded L
  have hE := DiamondGroupoid.isomorphic_equivalence (G := Gv) (S := (P.G.real : Set P.N)) (n := k + 1)
    P.G.model00 P.hc P.G.uncountable.le P.G.saturated P.G.small_real hv
  have h1 := isomorphic_of_liftData P.G.model00 P.hc lin P.G.uncountable P.G.saturated hv P.G.small_real
    (Hm.base_nontrivial P) A hω L (measuredRVLift_properInvariant P.G.model00 P.hc P.G.uncountable
      P.G.saturated hv U hU)
  have ha : Isomorphic Gv A (liftOf Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real
      P.G.small_real (Hm.base_nontrivial P) (objOf P.hc P.G.real U hU)) := by
    refine hE.trans h1 ?_
    let e : MeasuredRVIso U (dbObj P.hc P.G.model00 P.G.uncountable P.G.saturated P.G.real P.G.small_real
        (Hm.base_nontrivial P) (objOf P.hc P.G.real U hU)).1 :=
      (measuredIso_chartOf P.hc U).symm.comp (DiamondIntegral.Section7.MeasuredRVBridge.measuredIso P.hc
        (DiamondIntegral.Section7.StrictCharts.strictIso P.G.model00 (chartOf P.hc U)))
    obtain ⟨F, -⟩ := DiamondIntegral.Section6.DiamondLiftHomomorphism.lemma_6_33_diamond (G := Gv) P.G.model00 P.hc lin P.G.uncountable P.G.saturated hv
      P.G.real P.G.fieldBase P.G.small_real (Hm.base_nontrivial P) hntB e hU
      (dbObj P.hc P.G.model00 P.G.uncountable P.G.saturated P.G.real P.G.small_real
        (Hm.base_nontrivial P) (objOf P.hc P.G.real U hU)).2 _ _
    exact ⟨F⟩
  change Ideal.quotEquivOfEq (RelativeAnnularConverse.ideal_eq_manuscriptIdeal (B := base P)).symm
    (integralRing Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real P.G.small_real
      (Hm.base_nontrivial P) P.G.fieldBase hntB _ _ (ringClass Gv P.hc _ A)) = _
  rw [integralRing_ringClass, vfClass_iso P.hc ha, intQ_lift, Ideal.quotEquivOfEq_mk]
  rfl

include hntB in
/-- **The coefficients of the zeta function of an object with form `1`**: for an object `A` of
`μVF^◇[n]` with constant form `1`, whose trace at scale `0` is invariant at the cutoff `c`, with
labels covered by `Q`, nonzero labels and integral rational points, `η h_m ∫^◇[A]` is the normalized
class of the truncation of the trace of `A` at `(m, c)`. -/
theorem zeta_coeff_of_form_one {k : ℕ} (A : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) (k + 1))
    (hA1 : ∀ p, gammaMapValue A.form p = 1) (m : ℕ+) (c : Fin (k + 1) → ℕ) (Q : Finset (Fin A.labels → ℤ))
    (hA0 : Invariant m c (mixedSet (strace P 0 A.carrier)))
    (hQ0 : Covers m Q (mixedSet (strace P 0 A.carrier)))
    (hnz0 : LabelsNonzero (mixedSet (strace P 0 A.carrier)))
    (hlow0 : RationalIntegral m (mixedSet (strace P 0 A.carrier))) :
    PowerSeries.coeff (m : ℕ) (zetaQ P (theorem_7_26_graded Gv P.G.model00 P.hc P.G.uncountable
      P.G.saturated hv P.G.real P.G.small_real (Hm.base_nontrivial P) P.G.fieldBase hntB
      (ringClass Gv P.hc (unitObj Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real
        P.G.small_real (Hm.base_nontrivial P)) A))) =
      fullClass m c Q (strace_definableOver P 0 A.carrier) hA0 hQ0 := by
  obtain ⟨ω, hω, ⟨L⟩⟩ := exists_liftData P Gv hv hntB A
  set U := liftDataObject L
  have hU := liftDataObject_doublyBounded L
  have hform := lift_form_one P Gv A hA1 ω hω L
  rw [integral_lift P Gv hv hntB A ω hω L, zetaQ_quotient]
  unfold zeta
  rw [PowerSeries.coeff_mk]
  obtain ⟨L0, b0, hlift⟩ := lift_class P U hU hform m
  have hPB : ProperInvariant (P.G.real : Set P.N) (SpecialTransformations.Section4.rvLift U.object).carrier :=
    measuredRVLift_properInvariant P.G.model00 P.hc P.G.uncountable P.G.saturated hv U hU
  have gA := good_of_proper P m Gv hv _ A.proper
  have gB := good_of_proper P m Gv hv _ hPB
  have hteq := chain_teq P m Gv hv L.special
  obtain ⟨NA, hNA⟩ := gA.low
  obtain ⟨NB, hNB⟩ := gB.low
  set Lc := max L0 (max NA NB)
  obtain ⟨b2, hb12, hinvA⟩ := invariant_of_good P m gA Lc
    (fun i => max (bL m c Lc i) (b0 + (m : ℕ) * Lc))
  obtain ⟨b, hb2, hinvB⟩ := invariant_of_good P m gB Lc b2
  have hinvA' := invariant_mono m hb2 hinvA
  obtain ⟨QB, hQB⟩ := gB.cov Lc
  have h0L : mixedSet (strace P (0 + Lc) A.carrier) = mixedSet (strace P Lc A.carrier) := by
    rw [zero_add]
  have hQ1 : Covers m Q (mixedSet (strace P (0 + Lc) A.carrier)) := by
    have h := covers_scale m (L := Lc) hQ0 hlow0
    rwa [mixedSet_scale_strace] at h
  have hQA : Covers m Q (mixedSet (strace P Lc A.carrier)) := h0L ▸ hQ1
  have hrA := hNA Lc (le_trans (le_max_left _ _) (le_max_right _ _))
  have hrB := hNB Lc (le_trans (le_max_right _ _) (le_max_right _ _))
  have e1 := hteq Lc b Q QB hinvA' hinvB hQA hQB hrA hrB
  have hbb : ∀ i, b0 + (m : ℕ) * Lc ≤ b i := fun i => le_trans (le_max_right _ _) ((hb12 i).trans (hb2 i))
  have e2 := hlift Lc (le_max_left _ _) b hbb QB hinvB hQB
  have hA1' : Invariant m (bL m c Lc) (mixedSet (strace P (0 + Lc) A.carrier)) := by
    have h := invariant_scale m c Lc hA0
    rwa [mixedSet_scale_strace] at h
  have e3 := fullClass_strace_shift P m c A.carrier 0 Lc Q hA0 hQ0 hnz0 hlow0 hA1' hQ1
  have hbL : ∀ i, bL m c Lc i ≤ b i := fun i => le_trans (le_max_left _ _) ((hb12 i).trans (hb2 i))
  have hALc : Invariant m (bL m c Lc) (mixedSet (strace P Lc A.carrier)) := h0L ▸ hA1'
  have e4 : fullClass m b Q (strace_definableOver P Lc _) hinvA' hQA =
      fullClass m (bL m c Lc) Q (strace_definableOver P (0 + Lc) _) hA1' hQ1 := by
    rw [fullClass_strace_mono P m A.carrier Lc hbL Q hALc hinvA' hQA (gA.nz Lc)]
    exact fullClass_congr m _ h0L.symm _ _ _ _ _ _ _
  apply Linv_cancel ((k + 1) * ((m : ℕ) * Lc))
  rw [← e2, ← e1, e4, e3]

include hntB in
/-- **The first equality of (z:coeff:change)**: `η h_m ∫^◇[𝒳_f] = Θ(𝒳̃_f[m])`, the normalized class
of the truncation of the concrete Milnor fibre at `β = (1,…,1)`. -/
theorem milnor_zeta_coeff {k : ℕ} (f : MvPolynomial (Fin (k + 1)) ℂ) (m : ℕ+) :
    PowerSeries.coeff (m : ℕ) (milnorZeta P Gv hv hntB f) =
      truncClass m (bOne m) Fin.elim0 (rawMilnor_definableOver f) := by
  have hmt := milnor_trace P f
  have hA0 : Invariant m (bOne m) (mixedSet (strace P 0 (milnorDefSet P f))) := by
    rw [hmt]
    exact milnor_invariant_conc f m
  have hQ0 : Covers m {Fin.elim0} (mixedSet (strace P 0 (milnorDefSet P f))) := fun p _ _ _ =>
    ⟨Fin.elim0, Finset.mem_singleton_self _, fun j => j.elim0⟩
  have hlow0 : RationalIntegral m (mixedSet (strace P 0 (milnorDefSet P f))) := by
    intro p hp _ i
    rw [hmt, mem_mixedSet_milnor] at hp
    exact isIntegral_of_ordS (le_of_lt (hp.1 i))
  have e := zeta_coeff_of_form_one P Gv hv hntB (milnorObject P f) (fun p => rfl) m (bOne m) {Fin.elim0}
    hA0 hQ0 (fun p _ j => j.elim0) hlow0
  change PowerSeries.coeff (m : ℕ) (zetaQ P _) = _
  rw [e, fullClass_congr m _ hmt _ _ (rawMilnor_definableOver f) _ (milnor_invariant_conc f m) _
    (fun p _ _ _ => ⟨Fin.elim0, Finset.mem_singleton_self _, fun j => j.elim0⟩),
    fullClass_eq_sum m (bOne m) _ _ _ _ (fun p _ j => j.elim0), Finset.sum_singleton]

include hntB in
/-- **(z:coeff:change)**: `η h_m ∫^◇[𝒳_f] = Θ(𝒳̃_f[m]) = [𝒳_m] [𝔸]^{-md}`. -/
theorem z_coeff_change {k : ℕ} (f : MvPolynomial (Fin (k + 1)) ℂ) (m : ℕ+) :
    PowerSeries.coeff (m : ℕ) (milnorZeta P Gv hv hntB f) =
      algebraMap _ Rloc (jetClass f m) * Linv ((m : ℕ) * (k + 1)) := by
  rw [milnor_zeta_coeff P Gv hv hntB f m, z_coeff_change_jets]

end Final

end DiamondIntegral.Section8.Truncation
