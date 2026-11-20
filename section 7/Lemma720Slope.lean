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
    (x : VF M) (β : Gamma M) (b : M) (hb : NonzeroRV b) (hbβ : GammaParameters.codeValue b = β) (t : CanonicalRV.RVSort M) :
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

end RVAffine

end DiamondIntegral.Section7.Lemma720
