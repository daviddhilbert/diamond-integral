import «section 7».Lemma720EHU

/-! Lemma 7.20, step 14: definability of the uniform cell data over the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
open IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Final
variable {B : DefSet (rawMixedSpace (M := M) 1 a) S} (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M)) (T₂ : StandardContractionStage (G := G) B)
  (hD₂ : SameLabelShearDisplacement T₂.lift (Fin.last 0))
/-- Raw membership of a label tuple in the second-stage target. -/
def TargetRaw (c : Fin T₂.arity → M) : Prop :=
  Sum.elim (Fin.elim0 : Fin 0 → M) c ∈ mixedValues '' T₂.contracted.carrier

theorem targetRaw_iff (c : Fin T₂.arity → M) :
    TargetRaw T₂ c ↔ ∃ s : T₂.contracted, c = rvValues s.val.2 := by
  constructor
  · rintro ⟨q, hq, hqc⟩
    exact ⟨⟨q, hq⟩, (funext fun j => (congrFun hqc (.inr j)).symm)⟩
  · rintro ⟨s', rfl⟩
    exact ⟨s'.val, s'.property, (target_codes T₂ s').symm⟩

theorem targetRaw_definable : S.Definable LRV {c | TargetRaw T₂ c} := by
  have hT : S.Definable LRV (mixedValues '' T₂.contracted.carrier) := by
    rw [← preimage_eq_image]; exact T₂.contracted.definable
  have h := hT.preimage_comp (Sum.elim (Fin.elim0 : Fin 0 → Fin T₂.arity) id)
  have he : ∀ c : Fin T₂.arity → M, c ∘ (Fin.elim0 : Fin 0 → Fin T₂.arity) = (Fin.elim0 : Fin 0 → M) :=
    fun c => funext fun i => i.elim0
  simp only [Sum.comp_elim, Function.comp_id, he] at h
  exact h

theorem Dof_nonempty (s : T₂.contracted) (h0 : s.val.2 T₂.leading ≠ rvZero M) :
    (Dof T₂ hD₂ s.val.2).Nonempty := by
  obtain ⟨z₀, hz₀⟩ := rv_surjective (s.val.2 T₂.leading)
  refine ⟨cOf T₂ hD₂ s.val.2 + z₀, ?_⟩
  change rv M (cOf T₂ hD₂ s.val.2 + z₀ - cOf T₂ hD₂ s.val.2) = _
  rw [add_sub_cancel_left, hz₀]

variable (hc : CanonicalStructure.IsCanonical (M := M))
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
  (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M)
include hc hv hQ hlead

theorem def_eps : S.Definable LRV {z : Fin (2 + T₂.arity) → M | ∃ s : T₂.contracted, ∃ x ∈ Dof T₂ hD₂ s.val.2,
    z = Fin.append ![x.val, (εU ε lead Q T₂ s.val.2 x).val] (rvValues s.val.2)} := by
  let φ : (Fin T₂.arity ⊕ Fin 1) ⊕ Fin 1 → Fin (2 + T₂.arity) :=
    Sum.elim (Sum.elim (fun j => Fin.natAdd 2 j) (fun _ => Fin.castAdd T₂.arity 0)) (fun _ => Fin.castAdd T₂.arity 1)
  have hE := (EHU_definable ε lead Q T₂ hD₂ hc hQ).preimage_comp φ
  convert hE using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨s, x, hx, rfl⟩
    have he : (Fin.append ![x.val, (εU ε lead Q T₂ s.val.2 x).val] (rvValues s.val.2)) ∘ φ =
        Sum.elim (Sum.elim (rvValues s.val.2) (fun _ : Fin 1 => x.val))
          (fun _ : Fin 1 => (εU ε lead Q T₂ s.val.2 x).val) := by
      funext i
      rcases i with (i | i) | i
      · simp only [φ, Function.comp_apply, Sum.elim_inl, Fin.append_right]
      · simp only [φ, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, Fin.append_left]
        rfl
      · simp only [φ, Function.comp_apply, Sum.elim_inr, Fin.append_left]
        rfl
    rw [he]
    exact (EHU_iff ε lead Q T₂ hD₂ hv hlead s x _).mpr ⟨hx, rfl⟩
  · intro h
    obtain ⟨s, x, hvx⟩ := EHU_target ε lead Q T₂ hD₂ h
    have h' := h
    rw [hvx] at h'
    obtain ⟨hx, he⟩ := (EHU_iff ε lead Q T₂ hD₂ hv hlead s x _).mp h'
    refine ⟨s, x, hx, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      fin_cases j
      · have := congrFun hvx (.inl (.inr 0))
        exact this
      · have := he
        exact this
    · rw [Fin.append_right]
      have := congrFun hvx (.inl (.inl j))
      exact this

include hD₂ in
theorem tU_val (s : T₂.contracted) : (tU lead T₂ s.val.2).val = s.val.2 (T₂.oldLabels lead) := by
  have h0 : s.val.2 T₂.leading ≠ rvZero M := lead_ne_zero T₂ s.val s.property
  obtain ⟨x, hx⟩ := Dof_nonempty T₂ hD₂ s h0
  have hne : wOf T₂ s.val.2 lead ≠ rvZero M := hlead _ (mkPoint_mem_of_Dof T₂ hD₂ s hx)
  rw [tU, dite_cond_eq_true (eq_true hne)]
  rfl

include hD₂ in
theorem def_t : S.Definable LRV {z : Fin (1 + T₂.arity) → M | ∃ s : T₂.contracted,
    z = Fin.append ![(tU lead T₂ s.val.2).val.val] (rvValues s.val.2)} := by
  have h1 := (targetRaw_definable T₂).preimage_comp (fun j => Fin.natAdd 1 j : Fin T₂.arity → Fin (1 + T₂.arity))
  have h2 := (Set.DefinableFun.proj LRV : S.DefinableFun LRV
      (fun z : Fin (1 + T₂.arity) → M => z (Fin.castAdd T₂.arity 0))).ofPred_eq
    (Set.DefinableFun.proj LRV : S.DefinableFun LRV
      (fun z : Fin (1 + T₂.arity) → M => z (Fin.natAdd 1 (T₂.oldLabels lead))))
  convert h1.inter h2 using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(targetRaw_iff T₂ _).mpr ⟨s, funext fun j => by simp only [Function.comp_apply, Fin.append_right]⟩, ?_⟩
    simp only [Fin.append_left, Fin.append_right]
    rw [tU_val lead Q T₂ hD₂ hc hv hQ hlead s]
    rfl
  · rintro ⟨ht, heq⟩
    obtain ⟨s, hs⟩ := (targetRaw_iff T₂ _).mp ht
    refine ⟨s, funext fun i => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      fin_cases j
      change z (Fin.castAdd T₂.arity 0) = (tU lead T₂ s.val.2).val.val
      rw [heq, tU_val lead Q T₂ hD₂ hc hv hQ hlead s]
      exact congrFun hs (T₂.oldLabels lead)
    · rw [Fin.append_right]
      exact congrFun hs j

theorem EHU3_iff (s : T₂.contracted) (x e : M) :
    EHU3 ε lead Q T₂ hD₂ (rvValues s.val.2) x e ↔
      ∃ xv : VF M, xv.val = x ∧ xv ∈ Dof T₂ hD₂ s.val.2 ∧ e = (εU ε lead Q T₂ s.val.2 xv).val := by
  constructor
  · intro h
    have hx : iVF x := h.2.1.choose_spec.2.1
    exact ⟨⟨x, hx⟩, rfl, (EHU_iff ε lead Q T₂ hD₂ hv hlead s ⟨x, hx⟩ e).mp h⟩
  · rintro ⟨xv, rfl, hx, he⟩
    exact (EHU_iff ε lead Q T₂ hD₂ hv hlead s xv e).mpr ⟨hx, he⟩

theorem K0raw_iff (s : T₂.contracted) :
    K0raw ε lead Q T₂ hD₂ (rvValues s.val.2) ↔ ∀ a ∈ Dof T₂ hD₂ s.val.2, ∀ a' ∈ Dof T₂ hD₂ s.val.2,
      εU ε lead Q T₂ s.val.2 a = εU ε lead Q T₂ s.val.2 a' := by
  constructor
  · intro h a ha a' ha'
    have := h ![a.val, a'.val, (εU ε lead Q T₂ s.val.2 a).val, (εU ε lead Q T₂ s.val.2 a').val]
      ((EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mpr ⟨a, rfl, ha, rfl⟩)
      ((EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mpr ⟨a', rfl, ha', rfl⟩)
    exact Subtype.ext this
  · intro h w h0 h1
    obtain ⟨a, ha0, ha, he⟩ := (EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mp h0
    obtain ⟨a', ha1, ha', he'⟩ := (EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mp h1
    rw [he, he', h a ha a' ha']

include hD₂ in
theorem K1raw_iff (s : T₂.contracted) :
    K1raw ε lead Q T₂ hD₂ (rvValues s.val.2) ↔ ∀ a ∈ Dof T₂ hD₂ s.val.2, ∀ a' ∈ Dof T₂ hD₂ s.val.2,
      Values.vrv (tU lead T₂ s.val.2).val < vfValue (εU ε lead Q T₂ s.val.2 a - εU ε lead Q T₂ s.val.2 a') := by
  have ht := tU_val lead Q T₂ hD₂ hc hv hQ hlead s
  have hne : s.val.2 (T₂.oldLabels lead) ≠ rvZero M := by
    rw [← ht]; exact (tU lead T₂ s.val.2).property
  have hNZ : NonzeroRV (s.val.2 (T₂.oldLabels lead)).val :=
    ⟨(s.val.2 (T₂.oldLabels lead)).property, fun h => hne (Subtype.ext h)⟩
  have hball (e e' : VF M) : ball (rvValues s.val.2 (T₂.oldLabels lead)) e.val e'.val ↔
      Values.vrv (tU lead T₂ s.val.2).val < vfValue (e - e') := by
    rw [ht]
    change ball (s.val.2 (T₂.oldLabels lead)).val e.val e'.val ↔ _
    rw [ball_iff_value _ hNZ, codeValue_rv_val _ hne]
  constructor
  · intro h a ha a' ha'
    have := h ![a.val, a'.val, (εU ε lead Q T₂ s.val.2 a).val, (εU ε lead Q T₂ s.val.2 a').val]
      ((EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mpr ⟨a, rfl, ha, rfl⟩)
      ((EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mpr ⟨a', rfl, ha', rfl⟩)
    exact (hball _ _).mp this
  · intro h w h0 h1
    obtain ⟨a, ha0, ha, he⟩ := (EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mp h0
    obtain ⟨a', ha1, ha', he'⟩ := (EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mp h1
    change ball (rvValues s.val.2 (T₂.oldLabels lead)) (w 2) (w 3)
    rw [he, he']
    exact (hball _ _).mpr (h a ha a' ha')

include hD₂ in
theorem kindU_eq (s : T₂.contracted) :
    kindU ε lead Q T₂ hD₂ s.val.2 =
      if K0raw ε lead Q T₂ hD₂ (rvValues s.val.2) then 0
      else if K1raw ε lead Q T₂ hD₂ (rvValues s.val.2) then 1 else 2 := by
  rw [kindU, kindOf]
  simp only [K0raw_iff ε lead Q T₂ hD₂ hc hv hQ hlead s, K1raw_iff ε lead Q T₂ hD₂ hc hv hQ hlead s]

include hD₂ in
theorem def_kind (i : Fin 3) : S.Definable LRV {z : Fin T₂.arity → M | ∃ s : T₂.contracted,
    kindU ε lead Q T₂ hD₂ s.val.2 = i ∧ z = rvValues s.val.2} := by
  have hT := targetRaw_definable T₂ (S := S)
  have h0 := K0raw_definable ε lead Q T₂ hD₂ hc hQ
  have h1 := K1raw_definable ε lead Q T₂ hD₂ hc hQ
  have hset : {z : Fin T₂.arity → M | ∃ s : T₂.contracted, kindU ε lead Q T₂ hD₂ s.val.2 = i ∧ z = rvValues s.val.2} =
      {z | TargetRaw T₂ z ∧ (if K0raw ε lead Q T₂ hD₂ z then 0
        else if K1raw ε lead Q T₂ hD₂ z then 1 else 2) = i} := by
    ext z
    constructor
    · rintro ⟨s, hk, rfl⟩
      refine ⟨(targetRaw_iff T₂ _).mpr ⟨s, rfl⟩, ?_⟩
      rw [← kindU_eq ε lead Q T₂ hD₂ hc hv hQ hlead s]
      exact hk
    · rintro ⟨ht, hk⟩
      obtain ⟨s, rfl⟩ := (targetRaw_iff T₂ _).mp ht
      refine ⟨s, ?_, rfl⟩
      rw [kindU_eq ε lead Q T₂ hD₂ hc hv hQ hlead s]
      exact hk
  rw [hset]
  fin_cases i
  · convert hT.inter h0 using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    by_cases hk0 : K0raw ε lead Q T₂ hD₂ z <;> by_cases hk1 : K1raw ε lead Q T₂ hD₂ z <;> simp [hk0, hk1]
  · convert hT.inter (h0.compl.inter h1) using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    by_cases hk0 : K0raw ε lead Q T₂ hD₂ z <;> by_cases hk1 : K1raw ε lead Q T₂ hD₂ z <;> simp [hk0, hk1]
  · convert hT.inter (h0.compl.inter h1.compl) using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    by_cases hk0 : K0raw ε lead Q T₂ hD₂ z <;> by_cases hk1 : K1raw ε lead Q T₂ hD₂ z <;> simp [hk0, hk1]

include hD₂ in
/-- The raw equation for the second paradigm, as an equation in `RV`. -/
theorem raw_eqn_iff (s : T₂.contracted) (a a' : VF M) (τ₁ : RVInfinity M) :
    RVSlopeGraph.multiply (difference (εU ε lead Q T₂ s.val.2 a).val (εU ε lead Q T₂ s.val.2 a').val) τ₁.val =
        RVSlopeGraph.multiply (rvValues s.val.2 (T₂.oldLabels lead)) (difference a'.val a.val) ↔
      rv M (εU ε lead Q T₂ s.val.2 a - εU ε lead Q T₂ s.val.2 a') * τ₁ =
        (tU lead T₂ s.val.2).val * rv M (a' - a) := by
  rw [difference_vf, difference_vf]
  change RVSlopeGraph.multiply (rv M _).val τ₁.val = RVSlopeGraph.multiply (s.val.2 (T₂.oldLabels lead)).val
    (rv M (a' - a)).val ↔ _
  rw [RVSlopeGraph.multiply_rv, RVSlopeGraph.multiply_rv, ← RVOperations.mul_val, ← RVOperations.mul_val,
    tU_val lead Q T₂ hD₂ hc hv hQ hlead s]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

include hD₂ in
theorem T1raw_iff (s : T₂.contracted) (hk0 : ¬ K0raw ε lead Q T₂ hD₂ (rvValues s.val.2)) {σ : RV M}
    (hσ : HasSlope (Dof T₂ hD₂ s.val.2) (εU ε lead Q T₂ s.val.2) σ) (τ₁ : M) :
    T1raw ε lead Q T₂ hD₂ (rvValues s.val.2) τ₁ ↔
      τ₁ = (σ.val⁻¹ * (rv M (-1) * (tU lead T₂ s.val.2).val)).val := by
  have hσ0 : σ.val ≠ 0 := by rw [← rvZero_eq_zero]; exact σ.property
  -- the candidate satisfies the equation
  have hsol : ∀ a ∈ Dof T₂ hD₂ s.val.2, ∀ a' ∈ Dof T₂ hD₂ s.val.2,
      rv M (εU ε lead Q T₂ s.val.2 a - εU ε lead Q T₂ s.val.2 a') * (σ.val⁻¹ * (rv M (-1) * (tU lead T₂ s.val.2).val)) =
        (tU lead T₂ s.val.2).val * rv M (a' - a) := by
    intro a ha a' ha'
    rw [hσ a ha a' ha', rv_sub_swap a a']
    calc σ.val * rv M (a - a') * (σ.val⁻¹ * (rv M (-1) * (tU lead T₂ s.val.2).val))
        = (σ.val * σ.val⁻¹) * (rv M (a - a') * (rv M (-1) * (tU lead T₂ s.val.2).val)) := by ac_rfl
      _ = (tU lead T₂ s.val.2).val * (rv M (-1) * rv M (a - a')) := by
          rw [mul_inv_cancel₀ hσ0, one_mul]; ac_rfl
  constructor
  · rintro ⟨hrv, hall⟩
    rw [K0raw_iff ε lead Q T₂ hD₂ hc hv hQ hlead s] at hk0
    push_neg at hk0
    obtain ⟨a, ha, a', ha', hne⟩ := hk0
    have haa : a ≠ a' := fun h => hne (by rw [h])
    have h := hall ![a.val, a'.val, (εU ε lead Q T₂ s.val.2 a).val, (εU ε lead Q T₂ s.val.2 a').val]
      ((EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mpr ⟨a, rfl, ha, rfl⟩)
      ((EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mpr ⟨a', rfl, ha', rfl⟩)
      (fun h => haa (Subtype.ext h))
    have h' := (raw_eqn_iff ε lead Q T₂ hD₂ hc hv hQ hlead s a a' ⟨τ₁, hrv⟩).mp h
    rw [← hsol a ha a' ha'] at h'
    have hr0 : rv M (εU ε lead Q T₂ s.val.2 a - εU ε lead Q T₂ s.val.2 a') ≠ 0 := by
      rw [← rvZero_eq_zero]
      intro h0
      exact hne (sub_eq_zero.mp ((rv_eq_zero_iff _).mp h0))
    have := mul_left_cancel₀ hr0 h'
    exact congrArg Subtype.val this
  · rintro rfl
    refine ⟨(σ.val⁻¹ * (rv M (-1) * (tU lead T₂ s.val.2).val)).property, fun w h0 h1 hne => ?_⟩
    obtain ⟨a, ha0, ha, he⟩ := (EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mp h0
    obtain ⟨a', ha1, ha', he'⟩ := (EHU3_iff ε lead Q T₂ hD₂ hc hv hQ hlead s _ _).mp h1
    rw [he, he', ← ha0, ← ha1]
    exact (raw_eqn_iff ε lead Q T₂ hD₂ hc hv hQ hlead s a a' _).mpr (hsol a ha a' ha')

include hD₂ in
theorem def_t₁ (hslope : ∀ s : T₂.contracted, kindU ε lead Q T₂ hD₂ s.val.2 = 2 →
      ∃ σ : RV M, HasSlope (Dof T₂ hD₂ s.val.2) (εU ε lead Q T₂ s.val.2) σ) :
    S.Definable LRV {z : Fin (1 + T₂.arity) → M | ∃ s : T₂.contracted,
      kindU ε lead Q T₂ hD₂ s.val.2 = 2 ∧ z = Fin.append ![(t₁U ε lead Q T₂ hD₂ s.val.2).val] (rvValues s.val.2)} := by
  let tail : Fin T₂.arity → Fin (1 + T₂.arity) := fun j => Fin.natAdd 1 j
  have hT := (targetRaw_definable T₂ (S := S)).preimage_comp tail
  have h0 := (K0raw_definable ε lead Q T₂ hD₂ hc hQ).preimage_comp tail
  have h1 := (K1raw_definable ε lead Q T₂ hD₂ hc hQ).preimage_comp tail
  have h2 := (T1raw_definable ε lead Q T₂ hD₂ hc hQ).preimage_comp
    (Sum.elim tail (fun _ : Fin 1 => Fin.castAdd T₂.arity 0))
  simp only [Sum.comp_elim] at h2
  convert hT.inter (h0.compl.inter (h1.compl.inter h2)) using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage]
  have hsl (s : T₂.contracted) (hk : kindU ε lead Q T₂ hD₂ s.val.2 = 2) :
      HasSlope (Dof T₂ hD₂ s.val.2) (εU ε lead Q T₂ s.val.2) (σU ε lead Q T₂ hD₂ s.val.2) := by
    have hex := hslope s hk
    rw [σU, dif_pos hex]
    exact hex.choose_spec
  have hk2 (s : T₂.contracted) : kindU ε lead Q T₂ hD₂ s.val.2 = 2 ↔
      ¬ K0raw ε lead Q T₂ hD₂ (rvValues s.val.2) ∧ ¬ K1raw ε lead Q T₂ hD₂ (rvValues s.val.2) := by
    rw [kindU_eq ε lead Q T₂ hD₂ hc hv hQ hlead s]
    by_cases hk0 : K0raw ε lead Q T₂ hD₂ (rvValues s.val.2) <;>
      by_cases hk1 : K1raw ε lead Q T₂ hD₂ (rvValues s.val.2) <;> simp [hk0, hk1]
  constructor
  · rintro ⟨s, hk, rfl⟩
    have htail : (Fin.append ![(t₁U ε lead Q T₂ hD₂ s.val.2).val] (rvValues s.val.2)) ∘ tail = rvValues s.val.2 :=
      funext fun j => by simp only [tail, Function.comp_apply, Fin.append_right]
    obtain ⟨hk0, hk1⟩ := (hk2 s).mp hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [htail]; exact (targetRaw_iff T₂ _).mpr ⟨s, rfl⟩
    · rw [htail]; exact hk0
    · rw [htail]; exact hk1
    · change T1raw ε lead Q T₂ hD₂ ((Fin.append ![(t₁U ε lead Q T₂ hD₂ s.val.2).val] (rvValues s.val.2)) ∘ tail)
        (Fin.append ![(t₁U ε lead Q T₂ hD₂ s.val.2).val] (rvValues s.val.2) (Fin.castAdd T₂.arity 0))
      rw [htail, Fin.append_left]
      exact (T1raw_iff ε lead Q T₂ hD₂ hc hv hQ hlead s hk0 (hsl s hk) _).mpr rfl
  · rintro ⟨ht, hk0, hk1, hT1⟩
    obtain ⟨s, hs⟩ := (targetRaw_iff T₂ _).mp ht
    have hs' : z ∘ tail = rvValues s.val.2 := hs
    rw [hs'] at hk0 hk1
    have hk : kindU ε lead Q T₂ hD₂ s.val.2 = 2 := (hk2 s).mpr ⟨hk0, hk1⟩
    refine ⟨s, hk, funext fun i => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      fin_cases j
      change T1raw ε lead Q T₂ hD₂ (z ∘ tail) (z (Fin.castAdd T₂.arity 0)) at hT1
      rw [hs'] at hT1
      exact (T1raw_iff ε lead Q T₂ hD₂ hc hv hQ hlead s hk0 (hsl s hk) _).mp hT1
    · rw [Fin.append_right]
      exact congrFun hs' j

end Final

end DiamondIntegral.Section7.Lemma720
