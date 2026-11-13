import Section3.GammaFiniteOrder

/-! First-order closure of Gamma order formulas over the original real and
imaginary base. All Gamma quantifiers are implemented by full nonzero RV
code preimages; no representative is added to the parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.ModelTheory

namespace DiamondIntegral.Section4.GammaOrderLogic

inductive Formula (ι : Type) : ℕ → Type where
  | lt {n : ℕ} (i j : Fin n) : Formula ι n
  | unary {n : ℕ} (a : ι) (i : Fin n) : Formula ι n
  | and {n : ℕ} (φ ψ : Formula ι n) : Formula ι n
  | not {n : ℕ} (φ : Formula ι n) : Formula ι n
  | ex {n : ℕ} (φ : Formula ι (n + 1)) : Formula ι n

def Formula.Realize {ι α : Type} [LT α] (A : ι → Set α) :
    {n : ℕ} → Formula ι n → (Fin n → α) → Prop
  | _, .lt i j, z => z i < z j
  | _, .unary a i, z => z i ∈ A a
  | _, .and φ ψ, z => φ.Realize A z ∧ ψ.Realize A z
  | _, .not φ, z => ¬ φ.Realize A z
  | _, .ex φ, z => ∃ x, φ.Realize A (Fin.cons x z)

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def GammaDefinable (B : Base (M := M)) {n : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M))) : Prop :=
  DefinableOverBase B (fun _ : Fin n => .rv)
    {z | Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ P}

theorem proper_definable_base (B : Base (M := M)) (n : ℕ) :
    DefinableOverBase B (fun _ : Fin n => .rv) {z | Proper z} := by
  apply real_definableOverBase
  apply (definableOver_iff_normalized_raw _ _ _).mpr
  exact ⟨proper_normalized_definable B.real, fun z hz i => (hz i).1⟩

theorem formula_definable_base {ι : Type} (B : Base (M := M))
    (A : ι → Set (Values.Gamma (M := M)))
    (hA : ∀ a, GammaDefinableOverBase B (A a)) {n : ℕ} (φ : Formula ι n) :
    GammaDefinable B {z | φ.Realize A z} := by
  unfold GammaDefinable
  induction φ with
  | @lt n i j =>
    apply real_definableOverBase
    apply (definableOver_iff_normalized_raw _ _ _).mpr
    have hlt := @definable_binary_at LRV M (CanonicalStructure.normalize (M := M))
      B.real (Fin n) (EndpointLogic.codeLt (M := M))
      (EndpointLogic.codeLt_definable (M := M) B.real) i j
    have he : {z : Fin n → M | Proper z ∧
        Formula.Realize A (.lt i j) (fun t => codeValue (M := M) (z t))} =
        {z | Proper z ∧ EndpointLogic.codeLt (z i) (z j)} := by
      ext z
      constructor
      · rintro ⟨hz, h⟩
        exact ⟨hz, (EndpointLogic.codeLt_iff _ _ (hz i) (hz j)).mpr h⟩
      · rintro ⟨hz, h⟩
        exact ⟨hz, (EndpointLogic.codeLt_iff _ _ (hz i) (hz j)).mp h⟩
    refine ⟨?_, fun z hz i => (hz.1 i).1⟩
    change @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin n)
      {z | Proper z ∧ Formula.Realize A (.lt i j) (fun t => codeValue (M := M) (z t))}
    rw [he]
    exact @Set.Definable.inter M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin n)
      _ _ (proper_normalized_definable B.real) hlt
  | @unary n a i =>
    have h := (hA a).preimage_real (fun _ : Fin n => .rv) (fun _ : Fin 1 => i)
    have hp := (proper_definable_base B n).inter h
    convert hp using 1
    ext z
    change (Proper z ∧ codeValue (M := M) (z i) ∈ A a) ↔
      Proper z ∧ (z i ∈ Values.gammaPullback (A a) ∧ z ∈ sortedUniverse (fun _ => .rv))
    constructor
    · rintro ⟨hz, hm⟩
      exact ⟨hz, (gammaPullback_mem_codeValue_iff _ _ (hz i)).mpr hm, fun j => (hz j).1⟩
    · rintro ⟨hz, hm, _⟩
      exact ⟨hz, (gammaPullback_mem_codeValue_iff _ _ (hz i)).mp hm⟩
  | @and n φ ψ hφ hψ =>
    have h := hφ.inter hψ
    convert h using 1
    ext z
    change (Proper z ∧ φ.Realize A _ ∧ ψ.Realize A _) ↔
      (Proper z ∧ φ.Realize A _) ∧ (Proper z ∧ ψ.Realize A _)
    tauto
  | @not n φ hφ =>
    have h := (proper_definable_base B n).inter hφ.compl
    convert h using 1
    ext z
    change (Proper z ∧ ¬ φ.Realize A _) ↔
      Proper z ∧ z ∈ sortedUniverse (fun _ => .rv) ∧ ¬ (Proper z ∧ φ.Realize A _)
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hz, (fun i => (hz i).1), fun h => hn h.2⟩
    · rintro ⟨hz, _, hn⟩
      exact ⟨hz, fun h => hn ⟨hz, h⟩⟩
  | @ex n φ hφ =>
    have h := hφ.image_real (fun i : Fin n => i.succ)
    change DefinableOverBase B (fun _ : Fin n => .rv)
      ((fun w => w ∘ (fun i : Fin n => i.succ)) ''
        {w | Proper w ∧ φ.Realize A (fun i => codeValue (M := M) (w i))}) at h
    convert h using 1
    ext z
    change (Proper z ∧ ∃ x, φ.Realize A (Fin.cons x (fun i => codeValue (M := M) (z i)))) ↔
      ∃ w, (Proper w ∧ φ.Realize A (fun i => codeValue (M := M) (w i))) ∧
        w ∘ (fun i : Fin n => i.succ) = z
    constructor
    · rintro ⟨hz, x, hx⟩
      obtain ⟨t, ht, htx⟩ := EndpointLogic.codeValue_surjective x
      refine ⟨Fin.cons t z, ⟨?_, ?_⟩, ?_⟩
      · intro i
        refine Fin.cases ht (fun j => hz j) i
      · have he : (fun i : Fin (n + 1) =>
            codeValue (M := M) ((Fin.cons t z : Fin (n + 1) → M) i)) =
            (Fin.cons x (fun i : Fin n => codeValue (M := M) (z i)) :
              Fin (n + 1) → Values.Gamma (M := M)) := by
          funext i
          refine Fin.cases htx (fun _ => rfl) i
        rw [he]
        exact hx
      · funext i
        rfl
    · rintro ⟨w, ⟨hw, hφw⟩, he⟩
      have hs (i : Fin n) : w i.succ = z i := congrFun he i
      refine ⟨(fun i => hs i ▸ hw i.succ), codeValue (M := M) (w 0), ?_⟩
      have hc : Fin.cons (codeValue (M := M) (w 0)) (fun i => codeValue (M := M) (z i)) =
          (fun i => codeValue (M := M) (w i)) := by
        funext i
        refine Fin.cases rfl (fun j => congrArg (codeValue (M := M)) (hs j).symm) i
      rw [hc]
      exact hφw

theorem unary_definable_iff (B : Base (M := M)) (A : Set (Values.Gamma (M := M))) :
    GammaDefinable B {z : Fin 1 → Values.Gamma (M := M) | z 0 ∈ A} ↔
      GammaDefinableOverBase B A := by
  have he : {z : Fin 1 → M | Proper z ∧ codeValue (M := M) (z 0) ∈ A} =
      {z | z 0 ∈ Values.gammaPullback A} := by
    ext z
    constructor
    · rintro ⟨hz, hm⟩
      exact (gammaPullback_mem_codeValue_iff A _ (hz 0)).mpr hm
    · intro hm
      have hz0 : NonzeroRV (z 0) := ⟨hm.choose, hm.choose_spec.choose⟩
      exact ⟨(fun i => by fin_cases i; exact hz0),
        (gammaPullback_mem_codeValue_iff A _ hz0).mp hm⟩
  change DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | Proper z ∧ codeValue (M := M) (z 0) ∈ A} ↔
    DefinableOverBase B (fun _ => .rv) {z | z 0 ∈ Values.gammaPullback A}
  rw [he]

def interiorFormula : Formula Unit 1 :=
  .ex (.ex (.and (.lt 1 2) (.and (.lt 2 0)
    (.not (.ex (.and (.lt 2 0) (.and (.lt 0 1) (.not (.unary () 0)))))))))

def Interior {α : Type} [LT α] (A : Set α) : Set α :=
  {x | ∃ l u, l < x ∧ x < u ∧ ∀ y, l < y → y < u → y ∈ A}

theorem interiorFormula_realize {α : Type} [LT α] (A : Set α) (x : Fin 1 → α) :
    interiorFormula.Realize (fun _ => A) x ↔ x 0 ∈ Interior A := by
  change (∃ l u, l < x 0 ∧ x 0 < u ∧ ¬ ∃ y, l < y ∧ y < u ∧ ¬ y ∈ A) ↔
    (∃ l u, l < x 0 ∧ x 0 < u ∧ ∀ y, l < y → y < u → y ∈ A)
  simp only [not_exists, not_and, not_not]

theorem interior_definable_base (B : Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : GammaDefinableOverBase B A) : GammaDefinableOverBase B (Interior A) := by
  apply (unary_definable_iff B (Interior A)).mp
  have h := formula_definable_base B (fun _ : Unit => A) (fun _ => hA) interiorFormula
  have he : {z : Fin 1 → Values.Gamma (M := M) | interiorFormula.Realize (fun _ => A) z} =
      {z | z 0 ∈ Interior A} := Set.ext (interiorFormula_realize A)
  rwa [he] at h

theorem complement_definable_base (B : Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : GammaDefinableOverBase B A) : GammaDefinableOverBase B Aᶜ := by
  apply (unary_definable_iff B Aᶜ).mp
  exact formula_definable_base B (fun _ : Unit => A) (fun _ => hA)
    (.not (.unary (n := 1) () 0))

theorem finite_union_definable_base {ι : Type} (B : Base (M := M)) (s : Finset ι)
    (A : ι → Set (Values.Gamma (M := M)))
    (hA : ∀ i ∈ s, GammaDefinableOverBase B (A i)) :
    GammaDefinableOverBase B (⋃ i ∈ s, A i) := by
  have h := DefinableOverBase.finite_iUnion s
    (fun i => {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (A i)}) (fun i hi => hA i hi)
  have he : {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (⋃ i ∈ s, A i)} =
      ⋃ i ∈ s, {z | z 0 ∈ Values.gammaPullback (A i)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hr, h0, hm⟩
      simp only [Set.mem_iUnion] at hm
      obtain ⟨i, hi, hm⟩ := hm
      exact ⟨i, hi, hr, h0, hm⟩
    · rintro ⟨i, hi, hr, h0, hm⟩
      exact ⟨hr, h0, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hm⟩⟩⟩
  change DefinableOverBase B (fun _ : Fin 1 => .rv) _
  rw [he]
  exact h

end DiamondIntegral.Section4.GammaOrderLogic
