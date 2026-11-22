import «section 8».Theorem811

/-! The nonarchimedean Milnor fiber `𝒳_f` as an object of `μVF^◇[d]`, and Theorem 8.11 for it.

Let `f ∈ ℂ[x₁, …, x_d]`. In the ambient `P`, put
`𝒳_f = {x ∈ 𝔪^d | rv(f(x)) = rv(t)}`, with the constant volume form `0` (the value `1 ∈ Γ`).
This is the manuscript's `𝒳_f` for `X = 𝔸^d` at the origin, where the étale chart `q` of the
manuscript is the identity.

* `poly_integral`, `poly_lipschitz`: a polynomial with complex coefficients maps `𝒪^d` to `𝒪` and
  is `1`-Lipschitz there.
* `milnor_invariant`: `𝒳_f` is `β`-invariant for `β = v(t)` in every coordinate.
* `milnorObject f : VFObject (P.G.real) d`.
* `theorem_8_11_milnor`: with `Z_f(T) = Σ_m η h_m ∫^◇[𝒳_f] T^m` (the manuscript's (def:zeta)),
  `Z_f ∈ R[T]†`, and `𝒮_f = −lim_{T → ∞} Z_f = Θ 𝔼^◇ ∫^◇ [𝒳_f]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Milnor

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section9 SpecialTransformations.Section4
open DiamondIntegral.Section2 DiamondIntegral.Section6
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues

variable (P : PuiseuxAmbient) {d : ℕ}

/-! ### Values of polynomials with complex coefficients -/

theorem complex_value (c : ℂ) (hc : c ≠ 0) :
    Values.vfValueHom (ambientComplexFieldHom P.e c) = 1 := by
  change Values.vfValueHom (ambientPuiseuxFieldHom P.e (puiseuxConstant c)) = 1
  rw [ambient_vfValue_eq_of_valuation_eq P.e (puiseuxConstant c) 1, map_one, map_one]
  rw [map_one]
  simpa [hc] using constant_valuation c

theorem complex_value_ge (c : ℂ) : 1 ≤ Values.vfValueHom (ambientComplexFieldHom P.e c) := by
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero, ← Values.infinity_eq_zero]
    exact Values.le_infinity _
  · rw [complex_value P c hc]

/-- `f` with coefficients in the ambient. -/
abbrev fN (f : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) (VFType (M := P.N)) :=
  MvPolynomial.map (ambientComplexFieldHom P.e) f

theorem value_add_ge {γ : Values.GammaTop (M := P.N)} {a b : VFType (M := P.N)}
    (ha : γ ≤ Values.vfValueHom a) (hb : γ ≤ Values.vfValueHom b) : γ ≤ Values.vfValueHom (a + b) := by
  have h := vfValue_min_le_sub a (-b)
  rw [sub_neg_eq_add, vfValue_neg] at h
  exact (le_min ha hb).trans h

theorem value_add_gt {γ : Values.GammaTop (M := P.N)} {a b : VFType (M := P.N)}
    (ha : γ < Values.vfValueHom a) (hb : γ < Values.vfValueHom b) : γ < Values.vfValueHom (a + b) := by
  have h := vfValue_min_le_sub a (-b)
  rw [sub_neg_eq_add, vfValue_neg] at h
  exact (lt_min ha hb).trans_le h

/-- On `𝒪^d`, a polynomial with complex coefficients takes values in `𝒪`. -/
theorem poly_integral (g : MvPolynomial (Fin d) ℂ) {x : Fin d → VFType (M := P.N)}
    (hx : ∀ i, 1 ≤ Values.vfValueHom (x i)) : 1 ≤ Values.vfValueHom (MvPolynomial.eval x (fN P g)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    dsimp only [fN]
    rw [MvPolynomial.map_C, MvPolynomial.eval_C]
    exact complex_value_ge P a
  | add p q hp hq =>
    dsimp only [fN] at hp hq ⊢
    rw [RingHom.map_add, RingHom.map_add]
    exact value_add_ge P hp hq
  | mul_X p i hp =>
    dsimp only [fN] at hp ⊢
    rw [RingHom.map_mul, MvPolynomial.map_X, RingHom.map_mul, MvPolynomial.eval_X,
      map_mul Values.vfValueHom]
    exact one_le_mul hp (hx i)

/-- On `𝒪^d`, a polynomial with complex coefficients is `1`-Lipschitz. -/
theorem poly_lipschitz (g : MvPolynomial (Fin d) ℂ) {x y : Fin d → VFType (M := P.N)}
    (hx : ∀ i, 1 ≤ Values.vfValueHom (x i)) (hy : ∀ i, 1 ≤ Values.vfValueHom (y i))
    {γ : Values.Gamma (M := P.N)} (hxy : ∀ i, γ.val < Values.vfValueHom (x i - y i)) :
    γ.val < Values.vfValueHom (MvPolynomial.eval x (fN P g) - MvPolynomial.eval y (fN P g)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    dsimp only [fN]
    rw [MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.eval_C, sub_self]
    exact gamma_lt_value_zero γ
  | add p q hp hq =>
    dsimp only [fN] at hp hq ⊢
    rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, add_sub_add_comm]
    exact value_add_gt P hp hq
  | mul_X p i hp =>
    have hpi := poly_integral P p hy
    dsimp only [fN] at hp hpi ⊢
    rw [RingHom.map_mul, MvPolynomial.map_X, RingHom.map_mul, RingHom.map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_X]
    set u := MvPolynomial.eval x (MvPolynomial.map (ambientComplexFieldHom P.e) p)
    set w := MvPolynomial.eval y (MvPolynomial.map (ambientComplexFieldHom P.e) p)
    have he : u * x i - w * y i = (u - w) * x i + w * (x i - y i) := by ring
    rw [he]
    refine value_add_gt P ?_ ?_
    · rw [map_mul Values.vfValueHom]
      exact hp.trans_le (le_mul_of_one_le_right' (hx i))
    · rw [map_mul Values.vfValueHom]
      exact (hxy i).trans_le (le_mul_of_one_le_left' hpi)

/-! ### The set `𝒳_f` -/

/-- The image of `t` in the ambient. -/
abbrev tN : VFType (M := P.N) := ambientPuiseuxFieldHom P.e tSeries

/-- `𝒳_f = {x ∈ 𝔪^d | rv(f(x)) = rv(t)}`. -/
def milnorSet (f : MvPolynomial (Fin d) ℂ) : Set (Mixed P.N d 0) :=
  {p | (∀ i, 1 < Values.vfValueHom (p.1 i)) ∧
    rv P.N (MvPolynomial.eval p.1 (fN P f)) = rv P.N (tN P)}

theorem tN_mem : (tN P).val ∈ (P.G.real : Set P.N) :=
  ambientPuiseuxFieldHom_base_mem P.e P.G P.hB puiseuxBaseUniformizer

theorem fN_coeff_mem (f : MvPolynomial (Fin d) ℂ) (k : Fin d →₀ ℕ) :
    ((fN P f).coeff k).val ∈ (P.G.real : Set P.N) := by
  rw [MvPolynomial.coeff_map]
  exact ambientComplexFieldHom_base_mem P.e P.G P.hB _

theorem zero_mem : (0 : VFType (M := P.N)).val ∈ (P.G.real : Set P.N) := by
  have h := ambientComplexFieldHom_base_mem P.e P.G P.hB 0
  rwa [map_zero] at h

theorem one_mem : (1 : VFType (M := P.N)).val ∈ (P.G.real : Set P.N) := by
  have h := ambientComplexFieldHom_base_mem P.e P.G P.hB 1
  rwa [map_one] at h

theorem mem_ball_iff (x : VFType (M := P.N)) :
    x.val ∈ SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val
        (1 : VFType (M := P.N)).val ↔ 1 < Values.vfValueHom x := by
  change x.val ∈ OpenBallCodes.rawBall ![(0 : VFType (M := P.N)).val, (1 : VFType (M := P.N)).val] ↔ _
  rw [OpenBallCodes.rawBall, Set.mem_ofPred_eq, OpenBallCodes.body_realize]
  have hP : OpenBallCodes.Proper ![(0 : VFType (M := P.N)).val, (1 : VFType (M := P.N)).val] := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · exact (0 : VFType (M := P.N)).property
      · exact (1 : VFType (M := P.N)).property
    · intro h
      have h' : (1 : VFType (M := P.N)) = (0 : VFType (M := P.N)) := Subtype.ext h
      exact one_ne_zero h'
  rw [and_iff_right hP, and_iff_right x.property]
  have hd : (x - 0).val = iVFAdd x.val (iVFNeg (0 : VFType (M := P.N)).val) := by
    rw [sub_eq_add_neg]; rfl
  change ¬ iLe (iRv (iVFAdd x.val (iVFNeg (0 : VFType (M := P.N)).val))) (iRv (1 : VFType (M := P.N)).val) ↔ _
  rw [← hd]
  change ¬ VFValued.predV (1 : VFType (M := P.N)) (x - 0) ↔ _
  rw [Values.vf_pred_iff_gamma_le, sub_zero, map_one, not_le]

/-- The codes of `𝒳_f`. -/
def milnorCodes (f : MvPolynomial (Fin d) ℂ) : Set (Fin d ⊕ Fin 0 → P.N) :=
  {z | (∀ i, z (.inl i) ∈ SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val
      (1 : VFType (M := P.N)).val) ∧
    iRv (SpecialTransformations.Section5.mvPolynomialCode (fN P f) z) = iRv (tN P).val}

theorem milnorCodes_definable (f : MvPolynomial (Fin d) ℂ) :
    (P.G.real : Set P.N).Definable LRV (milnorCodes P f) := by
  have hball : (P.G.real : Set P.N).Definable LRV {z : Fin d ⊕ Fin 0 → P.N | ∀ i, z (.inl i) ∈
      SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val (1 : VFType (M := P.N)).val} := by
    have heach (i : Fin d) := (SpecialTransformations.Section8.rawOpenBall_definable (zero_mem P) (one_mem P)).preimage_comp
      (fun _ : Fin 1 => (Sum.inl i : Fin d ⊕ Fin 0))
    convert Set.definable_iInter_of_finite heach using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0) (S := (P.G.real : Set P.N))
    (fN P f) (fN_coeff_mem P f)
  change @Set.DefinableFun P.N LRV (CanonicalStructure.normalize (M := P.N)) (Fin d ⊕ Fin 0)
    (P.G.real : Set P.N) (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (fN P f)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq P.hc] at hp
  have hF : (P.G.real : Set P.N).DefinableFun LRV
      (fun z : Fin d ⊕ Fin 0 → P.N => iRv (SpecialTransformations.Section5.mvPolynomialCode (fN P f) z)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
      (show (P.G.real : Set P.N).DefinableMap LRV
          (fun z : Fin d ⊕ Fin 0 → P.N => ![SpecialTransformations.Section5.mvPolynomialCode (fN P f) z]) from by
        intro k
        fin_cases k
        exact hp)
  have hG : (P.G.real : Set P.N).DefinableFun LRV (fun _ : Fin d ⊕ Fin 0 → P.N => iRv (tN P).val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
      (show (P.G.real : Set P.N).DefinableMap LRV (fun _ : Fin d ⊕ Fin 0 → P.N => ![(tN P).val]) from by
        intro k
        fin_cases k
        exact LRV.definableFun_const _ (tN_mem P))
  convert hball.inter (hF.ofPred_eq hG) using 1
  ext z
  simp only [milnorCodes, Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem mem_milnorCodes_iff (f : MvPolynomial (Fin d) ℂ) (p : Mixed P.N d 0) :
    mixedValues p ∈ milnorCodes P f ↔ p ∈ milnorSet P f := by
  have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (fN P f) (mixedValues p) p.1
    (fun i => rfl)
  simp only [milnorCodes, milnorSet, Set.mem_ofPred_eq, hcode]
  refine and_congr (forall_congr' fun i => mem_ball_iff P (p.1 i)) ?_
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

/-- `𝒳_f` as a definable set over the base. -/
def milnorDefSet (f : MvPolynomial (Fin d) ℂ) : DefSet (rawMixedSpace (M := P.N) d 0) (P.G.real : Set P.N) :=
  ⟨milnorSet P f, by
    convert mixedValues_preimage_definable (milnorCodes P f) (milnorCodes_definable P f) using 1
    ext p
    exact (mem_milnorCodes_iff P f p).symm⟩

/-! ### `𝒳_f` is proper invariant -/

abbrev piV : Values.Gamma (M := P.N) := uniformizerValue P

theorem pi_named (T : Set P.N) (hT : (P.G.real : Set P.N) ⊆ T) :
    T.Definable LRV {z : Fin 1 → P.N | z 0 ∈ Values.gammaPullback {piV P}} :=
  ((gamma_real_codes_iff P.hc (P.G.real : Set P.N) {piV P}).mp (uniformizerValue_definable P)).mono hT

theorem value_tN : Values.vfValueHom (tN P) = (piV P).val := rfl

/-- If `x ∈ 𝒳_f` and `y ≡ x` modulo `v(t)` in every coordinate, then `y ∈ 𝒳_f`. -/
theorem milnor_invariant (f : MvPolynomial (Fin d) ℂ) {x y : Fin d → VFType (M := P.N)}
    (hx : (x, (Fin.elim0 : Fin 0 → _)) ∈ milnorSet P f)
    (hxy : ∀ i, (piV P).val < Values.vfValueHom (x i - y i)) :
    (y, (Fin.elim0 : Fin 0 → _)) ∈ milnorSet P f := by
  obtain ⟨hxM, hxf⟩ := hx
  have h1 : (1 : Values.GammaTop (M := P.N)) < (piV P).val := one_lt_uniformizerValue P
  have hyM : ∀ i, 1 < Values.vfValueHom (y i) := by
    intro i
    have h := vfValue_min_le_sub (x i) (x i - y i)
    rw [sub_sub_cancel] at h
    exact (lt_min (hxM i) (h1.trans (hxy i))).trans_le h
  refine ⟨hyM, ?_⟩
  have hfx : Values.vfValueHom (MvPolynomial.eval x (fN P f)) = (piV P).val := by
    rw [← value_tN]
    exact congrArg Values.vrv hxf
  have hlip := poly_lipschitz P f (fun i => (hxM i).le) (fun i => (hyM i).le) hxy
  rw [vfValue_sub_comm] at hlip
  have hne : MvPolynomial.eval x (fN P f) ≠ 0 := by
    intro h0
    rw [h0, map_zero, ← Values.infinity_eq_zero] at hfx
    exact (piV P).property hfx.symm
  rw [← hxf]
  apply rv_eq_of_value_close hne
  change Values.vfValueHom _ < Values.vfValueHom _
  rw [hfx]
  exact hlip

theorem milnor_alpha_invariant (f : MvPolynomial (Fin d) ℂ) (t : Fin 0 → RVInfinity P.N) :
    AlphaInvariant (fun _ : Fin d => piV P) (vfFibre (milnorSet P f) t) := by
  have ht : t = Fin.elim0 := Subsingleton.elim _ _
  subst ht
  intro a b hab
  constructor
  · intro ha
    exact milnor_invariant P f ha hab
  · intro hb
    exact milnor_invariant P f hb (DiamondIntegral.Section6.Congruent.symm (α := fun _ : Fin d => piV P) hab)

theorem milnor_proper (f : MvPolynomial (Fin d) ℂ) :
    ProperInvariant (P.G.real : Set P.N) (milnorSet P f) where
  definable := (milnorDefSet P f).definable
  vfBounded := ⟨1, fun p hp i => by
    change (1 : Values.GammaTop (M := P.N)) ≤ Values.vfValueHom (p.1 i)
    exact (hp.1 i).le⟩
  rvBounded := ⟨1, fun _ _ i => i.elim0⟩
  radii t := ⟨fun _ => piV P, fun _ => pi_named P _ Set.subset_union_left, milnor_alpha_invariant P f t⟩

/-- **The nonarchimedean Milnor fiber** `𝒳_f ⊆ 𝔪^d`, with the constant volume form `0`, as an object
of `μVF^◇[d]` over the base of Section 8. -/
def milnorObject (f : MvPolynomial (Fin d) ℂ) : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) d where
  labels := 0
  carrier := milnorDefSet P f
  form := gammaOneMap P.hc (milnorDefSet P f)
  proper := milnor_proper P f
  formCovariant _ := ⟨fun _ => piV P, fun _ => pi_named P _ Set.subset_union_left, fun _ _ _ _ _ => rfl⟩
  finiteRV _ := Set.toFinite _

theorem milnorObject_carrier (f : MvPolynomial (Fin d) ℂ) :
    (milnorObject P f).carrier.carrier = milnorSet P f := rfl

/-! ### Theorem 8.11 for `𝒳_f` -/

section Theorem

open DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section7.Theorem726 DiamondIntegral.Section7.DiamondRing
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section8.Hm RationalSeries

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hntB : ∃ x : P.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- `∫^◇ [𝒳_f] ∈ K μRV^db[*] / J_var` (Theorem 7.26). -/
abbrev milnorIntegral (f : MvPolynomial (Fin d) ℂ) : RelativeAnnularQuotient.Ring (base P) :=
  theorem_7_26_graded Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real
    P.G.small_real (base_nontrivial P) P.G.fieldBase hntB
    (ringClass Gv P.hc (unitObj Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv
      P.G.real P.G.small_real (base_nontrivial P)) (milnorObject P f))

/-- The motivic zeta function `Z_f(T) = Σ_{m ≥ 1} η h_m (∫^◇ [𝒳_f]) T^m` of (def:zeta). -/
abbrev milnorZeta (f : MvPolynomial (Fin d) ℂ) : PowerSeries Rloc :=
  zetaQ P (milnorIntegral P Gv hv hntB f)

/-- `Θ 𝔼^◇ ∫^◇ [𝒳_f]`. -/
abbrev milnorClass (f : MvPolynomial (Fin d) ℂ) : EquivariantVariety.ModifiedRing :=
  theta P (EdiamondQ P (milnorIntegral P Gv hv hntB f))

/-- **Theorem 8.11 (`direct:mil`) for `𝒳_f`.** The motivic zeta function `Z_f` lies in
`K^μ̂ Var_ℂ[[𝔸]⁻¹][T]†`, has degree `≤ 0`, and the motivic Milnor fiber
`𝒮_f = −lim_{T → ∞} Z_f(T)` equals `Θ 𝔼^◇ ∫^◇ [𝒳_f]`. -/
theorem theorem_8_11_milnor (f : MvPolynomial (Fin d) ℂ) :
    HasLimit Lunit (milnorZeta P Gv hv hntB f)
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc (milnorClass P Gv hv hntB f))) :=
  theorem_8_11_vf P Gv hv hntB (milnorObject P f)

end Theorem

end DiamondIntegral.Section8.Milnor
