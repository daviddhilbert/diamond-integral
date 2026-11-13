import «section 4».GammaDefinableFunctions

/-! Definable Gamma names are closed under the actual group product.
The graph is expressed in the RV language using full value fibres. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaGroupNames
open GammaOrderLogic GammaDefinableEuler GammaDefinableFunctions

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem codeValue_mul (t u : M) (ht : NonzeroRV t) (hu : NonzeroRV u) :
    codeValue (M := M) (iRVMul t u) = codeValue t * codeValue u := by
  have hm : NonzeroRV (iRVMul t u) :=
    ⟨rv_mul_mem hM ht.1 hu.1, fun h => ((rv_mul_eq_zero_of_model hM ht.1 hu.1).mp h).elim ht.2 hu.2⟩
  rw [codeValue, dite_eq_left hm, codeValue, dite_eq_left ht, codeValue, dite_eq_left hu]
  apply Subtype.ext
  change Values.vrv ⟨iRVMul t u, hm.1⟩ = Values.vrv ⟨t, ht.1⟩ * Values.vrv ⟨u, hu.1⟩
  exact Values.vrv_mul (M := M) ⟨t, ht.1⟩ ⟨u, hu.1⟩

omit hM in
theorem raw_mul_value_definable (S : Set M) :
    SpecialTransformations.Section3.DefinableOver S (fun _ : Fin 3 => .rv)
      {z | (∀ i, iRV (z i)) ∧ iLe (iRVMul (z 0) (z 1)) (z 2) ∧
        iLe (z 2) (iRVMul (z 0) (z 1))} := by
  let p : Parameters S := ⟨0, Fin.elim0, (fun _ => .vf), (fun i => i.elim0), (fun i => i.elim0)⟩
  let tm : LRV.Term (Fin 0 ⊕ Fin 3) := .func Fn.rvMul ![.var (.inr 0), .var (.inr 1)]
  let ts : Fin 2 → LRV.Term (Fin 0 ⊕ Fin 3) := ![tm, .var (.inr 2)]
  let us : Fin 2 → LRV.Term (Fin 0 ⊕ Fin 3) := ![.var (.inr 2), tm]
  let φ : LRV.BoundedFormula (Fin 0) 3 :=
    (.rel Rel.rvLe ts) ⊓ (.rel Rel.rvLe us)
  have htm : TmSort p.sorts (fun _ : Fin 3 => .rv) tm = some .rv := by
    apply tmSort_func
    intro i
    fin_cases i <;> rfl
  have hw : WellSorted p.sorts (fun _ : Fin 3 => .rv) φ := by
    apply wellSorted_inf
    · apply WellSorted.rel
      intro i
      fin_cases i
      · exact htm
      · rfl
    · apply WellSorted.rel
      intro i
      fin_cases i
      · rfl
      · exact htm
  refine ⟨p, φ, hw, ?_⟩
  ext z
  have htmz : tm.realize (Sum.elim p.values z) = iRVMul (z 0) (z 1) := by
    change Structure.funMap (L := LRV) Fn.rvMul
      (fun i => (![.var (.inr 0), .var (.inr 1)] i : LRV.Term (Fin 0 ⊕ Fin 3)).realize
        (Sum.elim p.values z)) = _
    have he : (fun i => (![.var (.inr 0), .var (.inr 1)] i : LRV.Term (Fin 0 ⊕ Fin 3)).realize
        (Sum.elim p.values z)) = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
    rw [he]
    rfl
  have hts : (fun i => (ts i).realize (Sum.elim p.values z)) =
      ![iRVMul (z 0) (z 1), z 2] := by
    funext i
    fin_cases i
    · exact htmz
    · rfl
  have hus : (fun i => (us i).realize (Sum.elim p.values z)) =
      ![z 2, iRVMul (z 0) (z 1)] := by
    funext i
    fin_cases i
    · rfl
    · exact htmz
  change ((∀ i, iRV (z i)) ∧ iLe (iRVMul (z 0) (z 1)) (z 2) ∧
    iLe (z 2) (iRVMul (z 0) (z 1))) ↔
      (∀ i, iRV (z i)) ∧ ((BoundedFormula.rel Rel.rvLe ts) ⊓
        (BoundedFormula.rel Rel.rvLe us)).Realize p.values z
  rw [BoundedFormula.realize_inf]
  change _ ↔ (∀ i, iRV (z i)) ∧
    (Structure.RelMap (L := LRV) Rel.rvLe (fun i => (ts i).realize (Sum.elim p.values z)) ∧
      Structure.RelMap (L := LRV) Rel.rvLe (fun i => (us i).realize (Sum.elim p.values z)))
  rw [hts, hus]
  rfl

theorem mul_graph_definable_base (B : Base (M := M)) :
    GammaDefinable B {z : Fin 3 → Values.Gamma (M := M) | z 0 * z 1 = z 2} := by
  have h := (proper_definable_base B 3).inter
    (real_definableOverBase B _ _ (raw_mul_value_definable B.real))
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ codeValue (M := M) (z 0) * codeValue (z 1) = codeValue (z 2)) ↔
    Proper z ∧ (∀ i, iRV (z i)) ∧ iLe (iRVMul (z 0) (z 1)) (z 2) ∧
      iLe (z 2) (iRVMul (z 0) (z 1))
  have hiff (hz : Proper z) :
      codeValue (M := M) (z 0) * codeValue (z 1) = codeValue (z 2) ↔
        iLe (iRVMul (z 0) (z 1)) (z 2) ∧ iLe (z 2) (iRVMul (z 0) (z 1)) := by
    have hm : NonzeroRV (iRVMul (z 0) (z 1)) := ⟨rv_mul_mem hM (hz 0).1 (hz 1).1,
      fun h => ((rv_mul_eq_zero_of_model hM (hz 0).1 (hz 1).1).mp h).elim (hz 0).2 (hz 1).2⟩
    rw [← codeValue_mul _ _ (hz 0) (hz 1), le_antisymm_iff,
      ← original_le_codeValue_iff _ _ hm (hz 2),
      ← original_le_codeValue_iff _ _ (hz 2) hm]
  constructor
  · rintro ⟨hz, he⟩
    exact ⟨hz, (fun i => (hz i).1), (hiff hz).mp he⟩
  · rintro ⟨hz, _, he⟩
    exact ⟨hz, (hiff hz).mpr he⟩

theorem mul_definable_base (B : Base (M := M)) (a b : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) (hb : GammaDefinableClosureAtBase B b) :
    GammaDefinableClosureAtBase B (a * b) := by
  let R : Set (Fin 3 → M) := {w | Proper w ∧ codeValue (M := M) (w 0) = a ∧
    codeValue (w 1) = b ∧ codeValue (w 0) * codeValue (w 1) = codeValue (w 2)}
  have hR : DefinableOverBase B (fun _ : Fin 3 => .rv) R := by
    have hg := mul_graph_definable_base B
    change DefinableOverBase B (fun _ : Fin 3 => .rv)
      {w | Proper w ∧ codeValue (M := M) (w 0) * codeValue (w 1) = codeValue (w 2)} at hg
    have hpa := ha.preimage_real (fun _ : Fin 3 => .rv) (fun _ : Fin 1 => (0 : Fin 3))
    have hpb := hb.preimage_real (fun _ : Fin 3 => .rv) (fun _ : Fin 1 => (1 : Fin 3))
    have h := (hg.inter hpa).inter hpb
    convert h using 1
    ext w
    change (Proper w ∧ codeValue (M := M) (w 0) = a ∧ codeValue (w 1) = b ∧
      codeValue (w 0) * codeValue (w 1) = codeValue (w 2)) ↔
      ((Proper w ∧ codeValue (M := M) (w 0) * codeValue (w 1) = codeValue (w 2)) ∧
        (w 0 ∈ Values.gammaPullback {a} ∧ w ∈ sortedUniverse (fun _ => .rv))) ∧
        (w 1 ∈ Values.gammaPullback {b} ∧ w ∈ sortedUniverse (fun _ => .rv))
    constructor
    · rintro ⟨hw, hwa, hwb, hwm⟩
      have hs : w ∈ sortedUniverse (fun _ : Fin 3 => .rv) := fun i => (hw i).1
      exact ⟨⟨⟨hw, hwm⟩, (gammaPullback_mem_codeValue_iff _ _ (hw 0)).mpr hwa, hs⟩,
        (gammaPullback_mem_codeValue_iff _ _ (hw 1)).mpr hwb, hs⟩
    · rintro ⟨⟨⟨hw, hwm⟩, hwa, _⟩, hwb, _⟩
      exact ⟨hw, (gammaPullback_mem_codeValue_iff _ _ (hw 0)).mp hwa,
        (gammaPullback_mem_codeValue_iff _ _ (hw 1)).mp hwb, hwm⟩
  have hp := hR.image_real (fun _ : Fin 1 => (2 : Fin 3))
  apply (unary_definable_iff B {a * b}).mp
  unfold GammaDefinable
  change DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | Proper z ∧ codeValue (M := M) (z 0) = a * b}
  have he : {z : Fin 1 → M | Proper z ∧ codeValue (M := M) (z 0) = a * b} =
      (fun w : Fin 3 → M => w ∘ (fun _ : Fin 1 => (2 : Fin 3))) '' R := by
    ext z
    constructor
    · rintro ⟨hz, hzab⟩
      obtain ⟨t, ht, hta⟩ := EndpointLogic.codeValue_surjective a
      obtain ⟨u, hu, hub⟩ := EndpointLogic.codeValue_surjective b
      refine ⟨![t, u, z 0], ⟨?_, hta, hub, ?_⟩, ?_⟩
      · intro i
        fin_cases i
        · exact ht
        · exact hu
        · exact hz 0
      · change codeValue (M := M) t * codeValue u = codeValue (z 0)
        rw [hta, hub, hzab]
      · funext i
        fin_cases i
        rfl
    · rintro ⟨w, ⟨hw, hwa, hwb, hwm⟩, he⟩
      have hwz : w 2 = z 0 := congrFun he 0
      refine ⟨(fun i => by fin_cases i; exact hwz ▸ hw 2), ?_⟩
      rw [← hwz, ← hwm, hwa, hwb]
  rw [he]
  exact hp

theorem add_definable_base (B : Base (M := M)) (a b : PaperGamma (M := M))
    (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a))
    (hb : GammaDefinableClosureAtBase B (toPaperGamma.symm b)) :
    GammaDefinableClosureAtBase B (toPaperGamma.symm (a + b)) :=
  mul_definable_base B (toPaperGamma.symm a) (toPaperGamma.symm b) ha hb

theorem one_definable_base (B : Base (M := M)) :
    GammaDefinableClosureAtBase B (1 : Values.Gamma (M := M)) := by
  have hg := mul_graph_definable_base B
  have h := hg.preimage_real (fun _ : Fin 1 => .rv) (fun _ : Fin 3 => (0 : Fin 1))
  apply (unary_definable_iff B {1}).mp
  unfold GammaDefinable
  convert h using 1
  ext z
  change (Proper z ∧ codeValue (M := M) (z 0) = 1) ↔
    (Proper (fun _ : Fin 3 => z 0) ∧
      codeValue (M := M) (z 0) * codeValue (z 0) = codeValue (z 0)) ∧
      z ∈ sortedUniverse (fun _ => .rv)
  constructor
  · rintro ⟨hz, he⟩
    exact ⟨⟨(fun _ => hz 0), by rw [he, one_mul]⟩, fun i => (hz i).1⟩
  · rintro ⟨⟨hz, he⟩, _⟩
    refine ⟨(fun i => by fin_cases i; exact hz 0), ?_⟩
    apply mul_left_cancel (a := codeValue (M := M) (z 0))
    simpa only [mul_one] using he

theorem zero_definable_base (B : Base (M := M)) :
    GammaDefinableClosureAtBase B (toPaperGamma.symm (0 : PaperGamma (M := M))) :=
  one_definable_base B

end DiamondIntegral.Section4.GammaGroupNames
