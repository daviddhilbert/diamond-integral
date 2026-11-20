import «section 7».Lemma720Codes
import IntegrationSection3ACVF.UniformGammaBallSyntax
import IntegrationSection3ACVF.RVSlopeGraph
import IntegrationSection3ACVF.FullBaseLogic
import «section 6».RVLinearRadiusClosure
import «section 7».Lemma720CellGeom

/-! Lemma 7.20, step 6: the RV-slope rows of a scalar family, for the rv-affine
refinement (R130).

`slopeRow A f (p, x, b, t)` says: `b` and `t` are nonzero RV elements, and on the open
ball of radius `vrv b` around `x` the function `f p` is defined and RV-linear with slope
`t`. It is upstream-definable over the full base whenever the family has a definable
graph (`slopeRow_definable`), and it is the Section 6 relation `SlopeAt` at the radius
`codeValue b` (`slopeRow_iff`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
open IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace DiamondIntegral.Section7.Lemma720

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The raw slope row: on the ball of radius `vrv b` around `x`, `f p` is defined and
RV-linear with nonzero slope `t`. -/
def slopeRow {n : ℕ} (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (z : Fin n ⊕ Fin 3 → M) : Prop :=
  NonzeroRV (z (.inr 1)) ∧ NonzeroRV (z (.inr 2)) ∧
    ∀ y y' : M, ball (z (.inr 1)) y (z (.inr 0)) → ball (z (.inr 1)) y' (z (.inr 0)) →
      y ∈ A (z ∘ Sum.inl) ∧ y' ∈ A (z ∘ Sum.inl) ∧
        difference (f (z ∘ Sum.inl) y') (f (z ∘ Sum.inl) y) =
          RVSlopeGraph.multiply (z (.inr 2)) (difference y' y)

theorem multiply_graph_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {z : Fin 3 → M | z 2 = RVSlopeGraph.multiply (z 0) (z 1)} := by
  apply FullBaseAtomicity.OverBase.of_real
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hm : B.real.DefinableFun LRV (fun z : Fin 3 → M => iRVMul (z 0) (z 1)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show B.real.DefinableMap LRV (fun z : Fin 3 → M => ![z 0, z 1]) from by
        intro k
        fin_cases k <;> exact Set.DefinableFun.proj LRV)
  exact (Set.DefinableFun.proj LRV).ofPred_eq hm

theorem slopeRow_definable (B : FullBaseAtomicity.Base (M := M)) {n : ℕ}
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 3 → M | slopeRow A f z} := by
  -- variables: z : Fin n ⊕ Fin 3, then y y' : Fin 2, then u u' d e : Fin 4
  let ι := Fin n ⊕ Fin 3
  let κ := ι ⊕ Fin 2
  let ν := κ ⊕ Fin 4
  have hNZ := FullBaseAtomicity.OverBase.of_real (B := B)
    (nonzero_codes_normalized_definable (M := M) B.real)
  have hNZb := FullBaseAtomicity.OverBase.preimage_comp hNZ (fun _ : Fin 1 => (Sum.inr 1 : ι))
  have hNZt := FullBaseAtomicity.OverBase.preimage_comp hNZ (fun _ : Fin 1 => (Sum.inr 2 : ι))
  have hBall0 := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl (.inr 1), .inr 0, .inl (.inr 0)] : Fin 3 → κ)
  have hBall1 := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl (.inr 1), .inr 1, .inl (.inr 0)] : Fin 3 → κ)
  have hDom := FiniteScalarFamilies.domain_definable B A f hf
  have hDom0 := FullBaseAtomicity.OverBase.preimage_comp hDom
    (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr 0) : Fin n ⊕ Fin 1 → κ)
  have hDom1 := FullBaseAtomicity.OverBase.preimage_comp hDom
    (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr 1) : Fin n ⊕ Fin 1 → κ)
  -- the equation, with witnesses u = f y, u' = f y', d = diff y' y, e = diff u' u
  have hG0 := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim (fun i => .inl (.inl (.inl i))) (fun _ => .inl (.inr 0))) (fun _ => .inr 0) :
      (Fin n ⊕ Fin 1) ⊕ Fin 1 → ν)
  have hG1 := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim (fun i => .inl (.inl (.inl i))) (fun _ => .inl (.inr 1))) (fun _ => .inr 1) :
      (Fin n ⊕ Fin 1) ⊕ Fin 1 → ν)
  have hD := FullBaseAtomicity.OverBase.preimage_comp (difference_graph_definable B)
    (![.inl (.inr 1), .inl (.inr 0), .inr 2] : Fin 3 → ν)
  have hE := FullBaseAtomicity.OverBase.preimage_comp (difference_graph_definable B)
    (![.inr 1, .inr 0, .inr 3] : Fin 3 → ν)
  have hMul := FullBaseAtomicity.OverBase.preimage_comp (multiply_graph_definable B)
    (![.inl (.inl (.inr 2)), .inr 2, .inr 3] : Fin 3 → ν)
  have hEq := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter hG0 (FullBaseAtomicity.OverBase.inter hG1
      (FullBaseAtomicity.OverBase.inter hD (FullBaseAtomicity.OverBase.inter hE hMul))))
  have hConcl := FullBaseAtomicity.OverBase.inter hDom0 (FullBaseAtomicity.OverBase.inter hDom1 hEq)
  have hAll := FullBaseAtomicity.OverBase.forall_block
    (FullBaseLogic.implication B (FullBaseAtomicity.OverBase.inter hBall0 hBall1) hConcl)
  have hRow := FullBaseAtomicity.OverBase.inter hNZb (FullBaseAtomicity.OverBase.inter hNZt hAll)
  apply FullBaseAtomicity.OverBase.congr hRow
  intro z
  constructor
  · rintro ⟨hb, ht, hall⟩
    refine ⟨hb, ht, fun y y' hy hy' => ?_⟩
    obtain ⟨h0, h1, w, hw0, hw1, hwd, hwe, hwm⟩ := hall ![y, y'] ⟨hy, hy'⟩
    change y ∈ A (z ∘ Sum.inl) at h0
    change y' ∈ A (z ∘ Sum.inl) at h1
    change y ∈ A (z ∘ Sum.inl) ∧ w 0 = f (z ∘ Sum.inl) y at hw0
    change y' ∈ A (z ∘ Sum.inl) ∧ w 1 = f (z ∘ Sum.inl) y' at hw1
    change w 2 = difference y' y at hwd
    change w 3 = difference (w 1) (w 0) at hwe
    change w 3 = RVSlopeGraph.multiply (z (.inr 2)) (w 2) at hwm
    refine ⟨h0, h1, ?_⟩
    rw [← hw0.2, ← hw1.2, ← hwe, hwm, hwd]
  · rintro ⟨hb, ht, hrow⟩
    refine ⟨hb, ht, fun yy hyy => ?_⟩
    obtain ⟨hA0, hA1, heq⟩ := hrow (yy 0) (yy 1) hyy.1 hyy.2
    refine ⟨hA0, hA1, ![f (z ∘ Sum.inl) (yy 0), f (z ∘ Sum.inl) (yy 1), difference (yy 1) (yy 0),
      difference (f (z ∘ Sum.inl) (yy 1)) (f (z ∘ Sum.inl) (yy 0))], ⟨hA0, rfl⟩, ⟨hA1, rfl⟩, rfl, rfl, ?_⟩
    exact heq

section RVAffine
open DiamondIntegral.Section2 DiamondIntegral.Section6 DiamondIntegral.Section7.TwoCells
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem mem_gammaBall_iff (a x : VF M) (γ : Gamma M) :
    x.val ∈ GammaRadiusAtomicity.gammaBall a γ true ↔ γ.val < vfValue (x - a) := by
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact lt_of_le_not_ge h1 (h2 rfl)
  · intro h
    exact ⟨x.property, h.le, fun _ => not_le.mpr h⟩

theorem gammaBall_vf {a : VF M} {γ : Gamma M} {m : M} (hm : m ∈ GammaRadiusAtomicity.gammaBall a γ true) :
    iVF m := hm.1

include hv in
/-- Inclusion of a ball in an open disc transfers between points of the disc. -/
theorem gammaBall_sub_of_mem {a x y : VF M} {γ β : Gamma M}
    (hx : γ.val < vfValue (x - a)) (hy : γ.val < vfValue (y - a))
    (hsub : GammaRadiusAtomicity.gammaBall x β true ⊆ GammaRadiusAtomicity.gammaBall a γ true) :
    GammaRadiusAtomicity.gammaBall y β true ⊆ GammaRadiusAtomicity.gammaBall a γ true := by
  intro m hm
  let u : VF M := ⟨m, hm.1⟩
  have hu : β.val < vfValue (u - y) := (mem_gammaBall_iff y u β).mp hm
  change u.val ∈ _
  by_cases hyx : β.val < vfValue (y - x)
  · apply hsub
    apply (mem_gammaBall_iff x u β).mpr
    have he : u - x = (u - y) + (y - x) := by ring
    rw [he]
    exact lt_vfValue_add hv hu hyx
  · rw [not_lt] at hyx
    apply (mem_gammaBall_iff a u γ).mpr
    have hxy : γ.val < vfValue (y - x) := by
      have he : y - x = (y - a) + -(x - a) := by ring
      rw [he]
      exact lt_vfValue_add hv hy (by rw [vfValue_neg hv]; exact hx)
    have he : u - a = (u - y) + (y - a) := by ring
    rw [he]
    exact lt_vfValue_add hv (lt_trans hxy (lt_of_le_of_lt hyx hu)) hy

/-- `SlopeAt` on a subset of the domain, in terms of the raw slope row. -/
theorem slopeAt_iff_row {n : ℕ} (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hfVF : ∀ p x, x ∈ A p → iVF (f p x)) (p : Fin n → M) (A' : Set M) (hA' : A' ⊆ A p)
    (x : VF M) (β : Gamma M) (b : M) (hb : NonzeroRV b) (hbβ : codeValue b = β) (t : CanonicalRV.RVSort M) :
    RVLinearRadiusClosure.SlopeAt A' (f p) (fun y hy => hfVF p y (hA' hy)) x β t ↔
      GammaRadiusAtomicity.gammaBall x β true ⊆ A' ∧ slopeRow A f (Sum.elim p ![x.val, b, t.val]) := by
  have hball (y : M) : ball b y x.val ↔ y ∈ GammaRadiusAtomicity.gammaBall x β true := by
    constructor
    · intro h
      have := (ball_iff b hb ⟨y, h.1⟩ x).mp h
      rwa [hbβ] at this
    · intro h
      apply (ball_iff b hb ⟨y, h.1⟩ x).mpr
      rwa [hbβ]
  constructor
  · rintro ⟨ht, hSub, hLin⟩
    refine ⟨hSub, hb, ⟨t.property, ht⟩, fun y y' hy hy' => ?_⟩
    obtain ⟨yv, rfl⟩ : ∃ yv : VF M, yv.val = y := ⟨⟨y, hy.1⟩, rfl⟩
    obtain ⟨yv', rfl⟩ : ∃ yv : VF M, yv.val = y' := ⟨⟨y', hy'.1⟩, rfl⟩
    have hyB := (hball _).mp hy
    have hy'B := (hball _).mp hy'
    refine ⟨hA' (hSub hyB), hA' (hSub hy'B), ?_⟩
    have hL := hLin yv yv' hyB hy'B
    let fy : VF M := ⟨f p yv.val, hfVF p yv.val (hA' (hSub hyB))⟩
    let fy' : VF M := ⟨f p yv'.val, hfVF p yv'.val (hA' (hSub hy'B))⟩
    have h1 : difference (f p yv'.val) (f p yv.val) = iRv (fy' - fy).val := difference_vf fy' fy
    have h2 : difference yv'.val yv.val = iRv (yv' - yv).val := difference_vf yv' yv
    show difference (f p yv'.val) (f p yv.val) = RVSlopeGraph.multiply t.val (difference yv'.val yv.val)
    rw [h1, h2]
    exact hL.trans (RVSlopeGraph.multiply_rv t (rv M (yv' - yv))).symm
  · rintro ⟨hSub, -, ht, hrow⟩
    refine ⟨ht.2, hSub, fun y y' hy hy' => ?_⟩
    obtain ⟨-, -, heq⟩ := hrow y.val y'.val ((hball _).mpr hy) ((hball _).mpr hy')
    change difference (f p y'.val) (f p y.val) = RVSlopeGraph.multiply t.val (difference y'.val y.val) at heq
    have h1 := difference_vf (⟨f p y'.val, hfVF p y'.val (hA' (hSub hy'))⟩ : VFType (M := M))
      ⟨f p y.val, hfVF p y.val (hA' (hSub hy))⟩
    have h2 := difference_vf y' y
    change difference (f p y'.val) (f p y.val) = _ at h1
    rw [h1, h2] at heq
    exact heq.trans (RVSlopeGraph.multiply_rv t (rv M (y' - y)))

theorem vf_sort_definable (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    S.Definable₁ LRV {x : M | iVF x} := by
  have h := ((@definableAt_iff_normalized_raw M sM hM S .vf _).mp (@definableAt_sort M sM S .vf)).1
  rw [SpecialTransformations.Section4.canonical_normalize_eq hc] at h
  exact h

/-- The raw codes of the translated disc `c + τ^♯` are definable over `{c, τ}`. -/
theorem tdisc_raw_definable (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (c : VF M)
    (τ : RVInfinity M) (hcS : c.val ∈ S) (hτS : τ.val ∈ S) :
    S.Definable LRV {w : Fin 1 → M | ∃ x ∈ tdisc c τ, x.val = w 0} := by
  have hsort := (vf_sort_definable hc S).preimage_comp (fun _ : Fin 1 => (0 : Fin 1))
  have hneg : S.DefinableFun LRV (fun _ : Fin 1 → M => iVFNeg c.val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
      (show S.DefinableMap LRV (fun _ : Fin 1 → M => ![c.val]) from by
        intro k
        fin_cases k
        exact LRV.definableFun_const _ hcS)
  have hadd : S.DefinableFun LRV (fun w : Fin 1 → M => iVFAdd (w 0) (iVFNeg c.val)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
      (show S.DefinableMap LRV (fun w : Fin 1 → M => ![w 0, iVFNeg c.val]) from by
        intro k
        fin_cases k
        · exact Set.DefinableFun.proj LRV
        · exact hneg)
  have hrv : S.DefinableFun LRV (fun w : Fin 1 → M => iRv (iVFAdd (w 0) (iVFNeg c.val))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun w : Fin 1 → M => ![iVFAdd (w 0) (iVFNeg c.val)]) from by
        intro k
        fin_cases k
        exact hadd)
  have heq := hrv.ofPred_eq (LRV.definableFun_const _ hτS)
  convert hsort.inter heq using 1
  ext w
  constructor
  · rintro ⟨x, hx, hxw⟩
    refine ⟨show iVF (w 0) from hxw ▸ x.property, ?_⟩
    change iRv (iVFAdd (w 0) (iVFNeg c.val)) = τ.val
    rw [← hxw]
    exact congrArg Subtype.val hx
  · rintro ⟨hw, hτ⟩
    refine ⟨⟨w 0, hw⟩, Subtype.ext hτ, rfl⟩

theorem card_union_finite_lt {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) {S F : Set M}
    (hS : Cardinal.mk S < κ) (hF : F.Finite) : Cardinal.mk (S ∪ F : Set M) < κ := by
  refine lt_of_le_of_lt (Cardinal.mk_union_le S F) ?_
  have hF' : Cardinal.mk F < κ := lt_trans (Cardinal.lt_aleph0_iff_set_finite.mpr hF) hκ
  exact Cardinal.add_lt_of_lt hκ.le hS hF'

include hv in
/-- **RV-affinity from frozen slope rows.** On a translated disc `D = c + τ^♯` inside the
domain of `f p`, where `f p` is injective and the slope rows are the same at all points
of `D`, the function is RV-linear with a nonzero slope. -/
theorem hasSlope_of_rows (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hf : FiniteScalarFamilies.Graph (fullBase S) A f) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (p : Fin n → M) (c z : VF M) (hz : z ≠ 0) (g : VF M → VF M)
    (hDA : ∀ x ∈ tdisc c (rv M z), x.val ∈ A p) (hg : ∀ x ∈ tdisc c (rv M z), (g x).val = f p x.val)
    (hinj : Set.InjOn g (tdisc c (rv M z)))
    (hrows : ∀ x ∈ tdisc c (rv M z), ∀ y ∈ tdisc c (rv M z), ∀ b t : M,
      slopeRow A f (Sum.elim p ![x.val, b, t]) ↔ slopeRow A f (Sum.elim p ![y.val, b, t])) :
    ∃ σ : RV M, HasSlope (tdisc c (rv M z)) g σ := by
  let D := tdisc c (rv M z)
  let S' : Set M := S ∪ (Set.range p ∪ {c.val, (rv M z).val})
  have hsmall' : Cardinal.mk S' < κ :=
    card_union_finite_lt hκ hsmall ((Set.finite_range p).union (Set.toFinite _))
  let A' : Set M := Subtype.val '' D
  let ρ := gval z hz
  have hA'eq : A' = GammaRadiusAtomicity.gammaBall (c + z) ρ true := by
    ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_gammaBall_iff (c + z) x ρ).mpr ((tdisc_mem_iff hv c z hz x).mp hx)
    · intro hm
      let x : VF M := ⟨m, hm.1⟩
      exact ⟨x, (tdisc_mem_iff hv c z hz x).mpr ((mem_gammaBall_iff (c + z) x ρ).mp hm), rfl⟩
  have hA'A : A' ⊆ A p := by
    rintro m ⟨x, hx, rfl⟩
    exact hDA x hx
  have hfVF' : ∀ m ∈ A', iVF (f p m) := fun m hm => hfVF p m (hA'A hm)
  -- the graph over the enlarged base
  have hGraph : FullBaseAtomicity.OverBase (fullBase S') (ImaginaryBaseImages.graphOn A' (f p)) := by
    apply overBase_of_definable hc
    have hfam := (definable_of_overBase hc hf).mono (Set.subset_union_left : S ⊆ S')
    let ψ (w : Fin 2 → M) : (Fin n ⊕ Fin 1) ⊕ Fin 1 → M :=
      Sum.elim (Sum.elim p (fun _ => w 0)) (fun _ => w 1)
    have hψ : S'.DefinableMap LRV ψ := by
      rintro ((i | i) | i)
      · exact LRV.definableFun_const _ (Or.inr (Or.inl (Set.mem_range_self i)))
      · exact Set.DefinableFun.proj LRV
      · exact Set.DefinableFun.proj LRV
    have hdisc := (tdisc_raw_definable hc S' c (rv M z) (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inr (Or.inr rfl)))).preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
    convert hdisc.inter (hfam.preimage_map hψ) using 1
    ext w
    constructor
    · rintro ⟨hw0, hw1⟩
      obtain ⟨x, hx, hxw⟩ := hw0
      refine ⟨⟨x, hx, hxw⟩, ?_, ?_⟩
      · change w 0 ∈ A p
        rw [← hxw]
        exact hDA x hx
      · exact hw1
    · rintro ⟨⟨x, hx, hxw⟩, -, hw1⟩
      exact ⟨⟨x, hx, hxw⟩, hw1⟩
  have hInj : Set.InjOn (f p) A' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    have : g x = g y := Subtype.ext ((hg x hx).trans (he.trans (hg y hy).symm))
    rw [hinj hx hy this]
  have hEA : GammaRadiusAtomicity.gammaBall (c + z) ρ true ⊆ A' := hA'eq.symm.subset
  have hmemD (x : VF M) (hx : x.val ∈ GammaRadiusAtomicity.gammaBall (c + z) ρ true) : x ∈ D := by
    rw [← hA'eq] at hx
    obtain ⟨x', hx', he⟩ := hx
    rw [← Subtype.ext he]
    exact hx'
  have hRows : ∀ x y : VFType (M := M), x.val ∈ GammaRadiusAtomicity.gammaBall (c + z) ρ true →
      y.val ∈ GammaRadiusAtomicity.gammaBall (c + z) ρ true → ∀ β t,
        RVLinearRadiusClosure.SlopeAt A' (f p) hfVF' x β t ↔ RVLinearRadiusClosure.SlopeAt A' (f p) hfVF' y β t := by
    intro x y hx hy β t
    obtain ⟨b, hb, hbβ⟩ := GammaParameters.EndpointLogic.codeValue_surjective β
    have hx' := (mem_gammaBall_iff (c + z) x ρ).mp hx
    have hy' := (mem_gammaBall_iff (c + z) y ρ).mp hy
    rw [slopeAt_iff_row A f hfVF p A' hA'A x β b hb hbβ t, slopeAt_iff_row A f hfVF p A' hA'A y β b hb hbβ t,
      hA'eq]
    constructor
    · rintro ⟨hsub, hrow⟩
      exact ⟨gammaBall_sub_of_mem hv hx' hy' hsub, (hrows x (hmemD x hx) y (hmemD y hy) b t.val).mp hrow⟩
    · rintro ⟨hsub, hrow⟩
      exact ⟨gammaBall_sub_of_mem hv hy' hx' hsub, (hrows x (hmemD x hx) y (hmemD y hy) b t.val).mpr hrow⟩
  obtain ⟨t, ht, hLin⟩ := RVLinearRadiusClosure.on_ordinary_ball hκ.le hs (fullBase S') hsmall' h00
    A' (f p) hGraph hfVF' hInj (c + z) ρ hEA hRows
  have htz : t ≠ rvZero M := fun h => ht (congrArg Subtype.val h)
  refine ⟨⟨t, htz⟩, fun a ha a' ha' => ?_⟩
  have haB : a.val ∈ GammaRadiusAtomicity.gammaBall (c + z) ρ true := by rw [← hA'eq]; exact ⟨a, ha, rfl⟩
  have ha'B : a'.val ∈ GammaRadiusAtomicity.gammaBall (c + z) ρ true := by rw [← hA'eq]; exact ⟨a', ha', rfl⟩
  have hL := hLin a' a ha'B haB
  apply Subtype.ext
  rw [RVOperations.mul_val]
  have hga : g a = ⟨f p a.val, hfVF' a.val (hEA haB)⟩ := Subtype.ext (hg a ha)
  have hga' : g a' = ⟨f p a'.val, hfVF' a'.val (hEA ha'B)⟩ := Subtype.ext (hg a' ha')
  rw [hga, hga']
  exact hL

end RVAffine

end DiamondIntegral.Section7.Lemma720
