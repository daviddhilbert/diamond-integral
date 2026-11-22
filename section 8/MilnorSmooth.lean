import «section 8».VolComparison

/-! The nonarchimedean Milnor fiber of a smooth affine variety, with the étale chart as a hypothesis.

Let `X ⊆ 𝔸^N` be cut out near the origin by `F₁, …, F_k ∈ ℂ[y₁, …, y_N]`, let `f ∈ ℂ[y]` be the
function and `q = (q₁, …, q_d)`, `q_i ∈ ℂ[y]` with `q_i(0) = 0`, a coordinate map at the origin.
The tube is `X(𝔪) = {y ∈ 𝔪^N | F(y) = 0}`.

`EtaleChart P F q` records what Hensel's lemma gives when `q` is étale at the origin
(manuscript, §8.2: "By Hensel's lemma, `q` induces a bijection between `X(𝔪)` and `𝔪^d`"):
`q : X(𝔪) → 𝔪^d` is surjective and its inverse is `1`-Lipschitz (so `q` is injective on the tube).
This is taken as a hypothesis, by the author's instruction; it is not proved here.

Under it, `𝒳_f = q({y ∈ X(𝔪) | rv(f(y)) = rv(t)}) ⊆ 𝔪^d` is definable over the base (the image of a
definable set under a polynomial map) and invariant for the radius `v(t)`, so it is an object of
`μVF^◇[d]` (`milnorObjectX`). Theorem 8.11 and Remark 8.14 follow (`theorem_8_11_smooth`,
`milnor_fiber_vol_smooth`).

`etaleChart_affine`: for `X = 𝔸^d` (no equations, `q` the identity) the hypothesis holds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

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

variable (P : PuiseuxAmbient) {N d k : ℕ}

/-! ### Definability of polynomial conditions -/

theorem ballCodes_definable (n : ℕ) :
    (P.G.real : Set P.N).Definable LRV {z : Fin n ⊕ Fin 0 → P.N | ∀ i, z (.inl i) ∈
      SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val (1 : VFType (M := P.N)).val} := by
  have heach (i : Fin n) := (SpecialTransformations.Section8.rawOpenBall_definable (zero_mem P) (one_mem P)).preimage_comp
    (fun _ : Fin 1 => (Sum.inl i : Fin n ⊕ Fin 0))
  convert Set.definable_iInter_of_finite heach using 1
  ext z
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rfl

theorem polyCode_definableFun {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    (P.G.real : Set P.N).DefinableFun LRV
      (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (fN P g)) := by
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0) (S := (P.G.real : Set P.N))
    (fN P g) (fN_coeff_mem P g)
  change @Set.DefinableFun P.N LRV (CanonicalStructure.normalize (M := P.N)) (Fin n ⊕ Fin 0)
    (P.G.real : Set P.N) (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (fN P g)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq P.hc] at hp
  exact hp

theorem polyCode_zero_definable {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    (P.G.real : Set P.N).Definable LRV {z : Fin n ⊕ Fin 0 → P.N |
      SpecialTransformations.Section5.mvPolynomialCode (fN P g) z = (0 : VFType (M := P.N)).val} := by
  have hG : (P.G.real : Set P.N).DefinableFun LRV (fun _ : Fin n ⊕ Fin 0 → P.N => (0 : VFType (M := P.N)).val) :=
    LRV.definableFun_const _ (zero_mem P)
  convert (polyCode_definableFun P g).ofPred_eq hG using 1

theorem polyCode_rv_definable {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    (P.G.real : Set P.N).Definable LRV {z : Fin n ⊕ Fin 0 → P.N |
      iRv (SpecialTransformations.Section5.mvPolynomialCode (fN P g) z) = iRv (tN P).val} := by
  have hF : (P.G.real : Set P.N).DefinableFun LRV
      (fun z : Fin n ⊕ Fin 0 → P.N => iRv (SpecialTransformations.Section5.mvPolynomialCode (fN P g) z)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
      (show (P.G.real : Set P.N).DefinableMap LRV
          (fun z : Fin n ⊕ Fin 0 → P.N => ![SpecialTransformations.Section5.mvPolynomialCode (fN P g) z]) from by
        intro j
        fin_cases j
        exact polyCode_definableFun P g)
  have hG : (P.G.real : Set P.N).DefinableFun LRV (fun _ : Fin n ⊕ Fin 0 → P.N => iRv (tN P).val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
      (show (P.G.real : Set P.N).DefinableMap LRV (fun _ : Fin n ⊕ Fin 0 → P.N => ![(tN P).val]) from by
        intro j
        fin_cases j
        exact LRV.definableFun_const _ (tN_mem P))
  convert hF.ofPred_eq hG using 1

/-! ### The tube and the chart hypothesis -/

/-- The tube `X(𝔪) = {y ∈ 𝔪^N | F(y) = 0}`. -/
def tube (F : Fin k → MvPolynomial (Fin N) ℂ) : Set (Fin N → VFType (M := P.N)) :=
  {y | (∀ i, 1 < Values.vfValueHom (y i)) ∧ ∀ j, MvPolynomial.eval y (fN P (F j)) = 0}

/-- The chart map `q` on points. -/
def chartMap (q : Fin d → MvPolynomial (Fin N) ℂ) (y : Fin N → VFType (M := P.N)) :
    Fin d → VFType (M := P.N) := fun i => MvPolynomial.eval y (fN P (q i))

/-- **The étale chart hypothesis (Hensel's lemma).** `q(0) = 0`, `q : X(𝔪) → 𝔪^d` is onto, and its
inverse is `1`-Lipschitz. -/
structure EtaleChart (F : Fin k → MvPolynomial (Fin N) ℂ) (q : Fin d → MvPolynomial (Fin N) ℂ) : Prop where
  zero : ∀ i, MvPolynomial.constantCoeff (q i) = 0
  surj : ∀ x : Fin d → VFType (M := P.N), (∀ i, 1 < Values.vfValueHom (x i)) →
    ∃ y ∈ tube P F, chartMap P q y = x
  lipschitz : ∀ y ∈ tube P F, ∀ y' ∈ tube P F, ∀ γ : Values.Gamma (M := P.N),
    (∀ i, γ.val < Values.vfValueHom (chartMap P q y i - chartMap P q y' i)) →
      ∀ j, γ.val < Values.vfValueHom (y j - y' j)

/-- A polynomial with complex coefficients and no constant term maps `𝔪^N` to `𝔪`. -/
theorem poly_maximal (g : MvPolynomial (Fin N) ℂ) (hg : MvPolynomial.constantCoeff g = 0)
    {y : Fin N → VFType (M := P.N)} (hy : ∀ i, 1 < Values.vfValueHom (y i)) :
    1 < Values.vfValueHom (MvPolynomial.eval y (fN P g)) := by
  have h0 : MvPolynomial.eval (0 : Fin N → VFType (M := P.N)) (fN P g) = 0 := by
    change MvPolynomial.eval (0 : Fin N → VFType (M := P.N)) (MvPolynomial.map (ambientComplexFieldHom P.e) g) = 0
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂Hom_zero_apply, hg, map_zero]
  have h := poly_lipschitz P g (x := y) (y := 0) (fun i => (hy i).le)
    (fun i => by simp only [Pi.zero_apply, map_zero]; rw [← Values.infinity_eq_zero]; exact Values.le_infinity _)
    (γ := 1) (fun i => by rw [Values.gamma_val_one]; simpa only [Pi.zero_apply, sub_zero] using hy i)
  rwa [h0, sub_zero, Values.gamma_val_one] at h

/-! ### The source set `{y ∈ X(𝔪) | rv(f(y)) = rv(t)}` -/

variable (F : Fin k → MvPolynomial (Fin N) ℂ) (f : MvPolynomial (Fin N) ℂ)
  (q : Fin d → MvPolynomial (Fin N) ℂ)

def sourceSet : Set (Mixed P.N N 0) :=
  {p | p.1 ∈ tube P F ∧ rv P.N (MvPolynomial.eval p.1 (fN P f)) = rv P.N (tN P)}

def sourceCodes : Set (Fin N ⊕ Fin 0 → P.N) :=
  {z | (∀ i, z (.inl i) ∈ SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val
      (1 : VFType (M := P.N)).val) ∧
    (∀ j, SpecialTransformations.Section5.mvPolynomialCode (fN P (F j)) z = (0 : VFType (M := P.N)).val) ∧
    iRv (SpecialTransformations.Section5.mvPolynomialCode (fN P f) z) = iRv (tN P).val}

theorem sourceCodes_definable : (P.G.real : Set P.N).Definable LRV (sourceCodes P F f) := by
  have hF : (P.G.real : Set P.N).Definable LRV {z : Fin N ⊕ Fin 0 → P.N | ∀ j,
      SpecialTransformations.Section5.mvPolynomialCode (fN P (F j)) z = (0 : VFType (M := P.N)).val} := by
    convert Set.definable_iInter_of_finite (fun j => polyCode_zero_definable P (F j)) using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  convert (ballCodes_definable P N).inter (hF.inter (polyCode_rv_definable P f)) using 1
  ext z
  simp only [sourceCodes, Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem mem_sourceCodes_iff (p : Mixed P.N N 0) :
    mixedValues p ∈ sourceCodes P F f ↔ p ∈ sourceSet P F f := by
  have hcode (g : MvPolynomial (Fin N) ℂ) :=
    SpecialTransformations.Section5.mvPolynomialCode_eq (fN P g) (mixedValues p) p.1 (fun i => rfl)
  simp only [sourceCodes, sourceSet, tube, Set.mem_ofPred_eq, hcode]
  constructor
  · rintro ⟨hb, hz, hr⟩
    exact ⟨⟨fun i => (mem_ball_iff P (p.1 i)).mp (hb i), fun j => Subtype.ext (hz j)⟩, Subtype.ext hr⟩
  · rintro ⟨⟨hb, hz⟩, hr⟩
    exact ⟨fun i => (mem_ball_iff P (p.1 i)).mpr (hb i), fun j => congrArg Subtype.val (hz j),
      congrArg Subtype.val hr⟩

def sourceDefSet : DefSet (rawMixedSpace (M := P.N) N 0) (P.G.real : Set P.N) :=
  ⟨sourceSet P F f, by
    convert mixedValues_preimage_definable (sourceCodes P F f) (sourceCodes_definable P F f) using 1
    ext p
    exact (mem_sourceCodes_iff P F f p).symm⟩

/-! ### `𝒳_f = q({y ∈ X(𝔪) | rv(f(y)) = rv(t)})` -/

/-- The chart as a definable map on the source set. -/
def chartDefMap : Map (sourceDefSet P F f) (DefSet.univ (rawMixedSpace (M := P.N) d 0) (P.G.real : Set P.N)) :=
  (universalVFPolynomialMap P.hc (P.G.real : Set P.N) (fun i => fN P (q i))
    (fun i c => fN_coeff_mem P (q i) c)).comp (Map.inclusion (fun _ _ => Set.mem_univ _))

theorem chartDefMap_val (a : sourceDefSet P F f) :
    (chartDefMap P F f q a).val = (chartMap P q a.val.1, Fin.elim0) := rfl

/-- `𝒳_f` in the chart coordinates. -/
def milnorSetX : Set (Mixed P.N d 0) := Set.range (fun a : sourceDefSet P F f => (chartDefMap P F f q a).val)

def milnorDefSetX : DefSet (rawMixedSpace (M := P.N) d 0) (P.G.real : Set P.N) :=
  ⟨milnorSetX P F f q, (chartDefMap P F f q).definable_image⟩

theorem mem_milnorSetX_iff (x : Fin d → VFType (M := P.N)) (t : Fin 0 → RVInfinity P.N) :
    (x, t) ∈ milnorSetX P F f q ↔
      ∃ y ∈ tube P F, rv P.N (MvPolynomial.eval y (fN P f)) = rv P.N (tN P) ∧ chartMap P q y = x := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (chartMap P q a.val.1, (Fin.elim0 : Fin 0 → RVInfinity P.N)) = (x, t) := ha
    exact ⟨a.val.1, a.property.1, a.property.2, congrArg Prod.fst ha'⟩
  · rintro ⟨y, hy, hf, rfl⟩
    refine ⟨⟨(y, Fin.elim0), hy, hf⟩, ?_⟩
    change (chartMap P q y, (Fin.elim0 : Fin 0 → RVInfinity P.N)) = (chartMap P q y, t)
    exact Prod.ext rfl (Subsingleton.elim _ _)

variable {F q}

theorem milnorX_maximal (hq : EtaleChart P F q) {x : Fin d → VFType (M := P.N)} {t : Fin 0 → RVInfinity P.N}
    (hx : (x, t) ∈ milnorSetX P F f q) (i : Fin d) : 1 < Values.vfValueHom (x i) := by
  obtain ⟨y, hy, -, rfl⟩ := (mem_milnorSetX_iff P F f q x t).mp hx
  exact poly_maximal P (q i) (hq.zero i) hy.1

/-- `𝒳_f` is invariant for the radius `v(t)`. -/
theorem milnorX_invariant (hq : EtaleChart P F q) {x x' : Fin d → VFType (M := P.N)}
    {t : Fin 0 → RVInfinity P.N} (hx : (x, t) ∈ milnorSetX P F f q)
    (hxx : ∀ i, (piV P).val < Values.vfValueHom (x i - x' i)) : (x', t) ∈ milnorSetX P F f q := by
  have h1 : (1 : Values.GammaTop (M := P.N)) < (piV P).val := one_lt_uniformizerValue P
  have hxM := milnorX_maximal P f hq hx
  obtain ⟨y, hy, hf, rfl⟩ := (mem_milnorSetX_iff P F f q x t).mp hx
  have hx'M : ∀ i, 1 < Values.vfValueHom (x' i) := by
    intro i
    have h := vfValue_min_le_sub (chartMap P q y i) (chartMap P q y i - x' i)
    rw [sub_sub_cancel] at h
    exact (lt_min (hxM i) (h1.trans (hxx i))).trans_le h
  obtain ⟨y', hy', rfl⟩ := hq.surj x' hx'M
  have hyy := hq.lipschitz y hy y' hy' (piV P) hxx
  have hfy : Values.vfValueHom (MvPolynomial.eval y (fN P f)) = (piV P).val := by
    rw [← value_tN]
    exact congrArg Values.vrv hf
  have hlip := poly_lipschitz P f (fun i => (hy.1 i).le) (fun i => (hy'.1 i).le) hyy
  rw [vfValue_sub_comm] at hlip
  have hne : MvPolynomial.eval y (fN P f) ≠ 0 := by
    intro h0
    rw [h0, map_zero, ← Values.infinity_eq_zero] at hfy
    exact (piV P).property hfy.symm
  refine (mem_milnorSetX_iff P F f q _ t).mpr ⟨y', hy', ?_, rfl⟩
  rw [← hf]
  apply rv_eq_of_value_close hne
  change Values.vfValueHom _ < Values.vfValueHom _
  rw [hfy]
  exact hlip

theorem milnorX_proper (hq : EtaleChart P F q) :
    ProperInvariant (P.G.real : Set P.N) (milnorSetX P F f q) where
  definable := (milnorDefSetX P F f q).definable
  vfBounded := ⟨1, fun p hp i => by
    change (1 : Values.GammaTop (M := P.N)) ≤ Values.vfValueHom (p.1 i)
    exact (milnorX_maximal P f hq (x := p.1) (t := p.2) hp i).le⟩
  rvBounded := ⟨1, fun _ _ i => i.elim0⟩
  radii t := ⟨fun _ => piV P, fun _ => pi_named P _ Set.subset_union_left, by
    intro a b hab
    constructor
    · intro ha
      exact milnorX_invariant P f hq ha hab
    · intro hb
      exact milnorX_invariant P f hq hb
        (DiamondIntegral.Section6.Congruent.symm (α := fun _ : Fin d => piV P) hab)⟩

/-- **The nonarchimedean Milnor fiber of `f` on `X` at the origin**, in the coordinates of an étale
chart `q`, with the constant volume form `0`: an object of `μVF^◇[d]`. -/
def milnorObjectX (hq : EtaleChart P F q) : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) d where
  labels := 0
  carrier := milnorDefSetX P F f q
  form := gammaOneMap P.hc (milnorDefSetX P F f q)
  proper := milnorX_proper P f hq
  formCovariant _ := ⟨fun _ => piV P, fun _ => pi_named P _ Set.subset_union_left, fun _ _ _ _ _ => rfl⟩
  finiteRV _ := Set.toFinite _

/-! ### `X = 𝔸^d` -/

/-- For `X = 𝔸^d`, with no equations and the identity chart, the chart hypothesis holds. -/
theorem etaleChart_affine :
    EtaleChart P (fun j : Fin 0 => j.elim0) (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)) := by
  have hmap : ∀ y : Fin d → VFType (M := P.N),
      chartMap P (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)) y = y := by
    intro y
    funext i
    change MvPolynomial.eval y (MvPolynomial.map (ambientComplexFieldHom P.e) (MvPolynomial.X i)) = y i
    rw [MvPolynomial.map_X, MvPolynomial.eval_X]
  refine ⟨fun i => MvPolynomial.constantCoeff_X (R := ℂ) i, fun x hx => ⟨x, ⟨hx, fun j => j.elim0⟩, hmap x⟩, ?_⟩
  intro y _ y' _ γ h j
  rw [hmap, hmap] at h
  exact h j

/-! ### Theorem 8.11 and Remark 8.14 for smooth `X` -/

section Theorem

open DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section7
open DiamondIntegral.Section7.Theorem726 DiamondIntegral.Section7.DiamondRing
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section8.Hm RationalSeries
open DiamondIntegral.Section8.VolComparison

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hntB : ∃ x : P.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- `∫^◇ [𝒳_f]` for smooth `X`. -/
abbrev milnorIntegralX (hq : EtaleChart P F q) : RelativeAnnularQuotient.Ring (base P) :=
  theorem_7_26_graded Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real
    P.G.small_real (base_nontrivial P) P.G.fieldBase hntB
    (ringClass Gv P.hc (unitObj Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv
      P.G.real P.G.small_real (base_nontrivial P)) (milnorObjectX P f hq))

/-- **Theorem 8.11 for smooth affine `X`**, given the étale chart hypothesis: the zeta function
`Z_f(T) = Σ_m η h_m (∫^◇[𝒳_f]) T^m` lies in `R[T]†` and `𝒮_f = −lim Z_f = Θ 𝔼^◇ ∫^◇ [𝒳_f]`. -/
theorem theorem_8_11_smooth (hq : EtaleChart P F q) :
    HasLimit Lunit (zetaQ P (milnorIntegralX P f Gv hv hntB hq))
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc
        (theta P (EdiamondQ P (milnorIntegralX P f Gv hv hntB hq))))) :=
  theorem_8_11_vf P Gv hv hntB (milnorObjectX P f hq)

/-- **Remark 8.14 for smooth affine `X`**: `𝒮_f = Vol([𝒳_f])`. -/
theorem milnor_fiber_vol_smooth (hq : EtaleChart P F q) :
    HasLimit Lunit (zetaQ P (milnorIntegralX P f Gv hv hntB hq))
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc (puiseuxBoundedVFVolume P
        (Algebra.GrothendieckAddGroup.of
          (gammaGroundVFSemiringClass (Remark728.forgetVF P.hc P.G (milnorObjectX P f hq))))))) := by
  rw [← remark_8_14 P Gv hv hntB (milnorObjectX P f hq)]
  exact theorem_8_11_smooth P f Gv hv hntB hq

end Theorem

end DiamondIntegral.Section8.Milnor
