import «section 5».FiniteValueDomainValidity
import «section 5».QuotientDomainSyntax
import «section 5».GammaRVSetObjects
import «section 4».Section3RVCodeBridge

/-! Literal original-language bounds for full native RV value patterns.
Zero coordinates are retained. A valid bound produces an actual native
RES object on the same domain, with its proved finite clean label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

 def rawRVValuePattern {n : ℕ} (x : Fin n → M) : Fin n → Values.GammaTop (M := M) :=
  fun i => if h : iRV (x i) then Values.vrv ⟨x i, h⟩ else Values.infinity

theorem rawRVValuePattern_of_tuple {n : ℕ} (x : Fin n → CanonicalRV.RVSort M) :
    rawRVValuePattern (rvValues x) = fun i => Values.vrv (x i) := by
  funext i
  simp only [rawRVValuePattern, rvValues, dif_pos (x i).property]

structure NativeRVValueSyntax (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] where
  equal : LRV.Formula (Fin 2)
  realize : ∀ x y : M, equal.Realize ![x, y] ↔ iLe x y ∧ iLe y x

theorem native_RV_value_syntax_exists : Nonempty (NativeRVValueSyntax M) := by
  have h : (∅ : Set M).Definable LRV {z : Fin 2 → M | iLe (z 0) (z 1) ∧ iLe (z 1) (z 0)} := by
    have hle := raw_le_definable (M := M) (∅ : Set M)
    convert hle.inter (hle.preimage_comp (![1, 0] : Fin 2 → Fin 2)) using 1
    ext z
    rfl
  obtain ⟨E, hE⟩ := Set.empty_definable_iff.mp h
  exact ⟨⟨E, fun x y => (Set.ext_iff.mp hE ![x, y]).symm⟩⟩

def nativeRVValueSyntax : NativeRVValueSyntax M := Classical.choice native_RV_value_syntax_exists

def rvValuePatternEqualityFormula {P : Type*} (E : LRV.Formula (Fin 2)) (n : ℕ) :
    LRV.Formula (P ⊕ (Fin n ⊕ Fin n)) :=
  tupleQuotientEqualityFormula E (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i))

theorem rvValuePatternEqualityFormula_realize {P : Type*} (E : NativeRVValueSyntax M) (n : ℕ)
    (v : P → M) (x y : Fin n → M) (hx : ∀ i, iRV (x i)) (hy : ∀ i, iRV (y i)) :
    (rvValuePatternEqualityFormula E.equal n).Realize (Sum.elim v (Sum.elim x y)) ↔
      rawRVValuePattern x = rawRVValuePattern y := by
  rw [rvValuePatternEqualityFormula, tupleQuotientEqualityFormula_realize]
  simp only [Sum.elim_inr, Sum.elim_inl]
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [E.realize]
  simpa only [rawRVValuePattern, dif_pos (hx i), dif_pos (hy i), Values.sameValue] using
    (Values.vrv_eq_iff (⟨x i, hx i⟩ : CanonicalRV.RVSort M) ⟨y i, hy i⟩).symm

def rvFiniteValueValidityFormula {P : Type*} {n : ℕ} (N : ℕ) (E : NativeRVValueSyntax M)
    (D : LRV.Formula (P ⊕ Fin n)) : LRV.Formula P :=
  finiteValueValidityFormula N D (rvValuePatternEqualityFormula E.equal n)

theorem rvFiniteValueValidityFormula_card {P : Type*} {n : ℕ} (N : ℕ) (E : NativeRVValueSyntax M)
    (D : LRV.Formula (P ⊕ Fin n)) (v : P → M)
    (hD : ∀ x, D.Realize (Sum.elim v x) → ∀ i, iRV (x i)) :
    (rvFiniteValueValidityFormula N E D).Realize v ↔
      (rawRVValuePattern '' {x | D.Realize (Sum.elim v x)}).Finite ∧
        (rawRVValuePattern '' {x | D.Realize (Sum.elim v x)}).ncard ≤ N :=
  finiteValueValidityFormula_on_domain_card N D _ v rawRVValuePattern
    (fun x y hx hy => rvValuePatternEqualityFormula_realize E n v x y (hD x hx) (hD y hy))

theorem gammaRVFiniteValues_iff_raw_patterns (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {n : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaRVFiniteValues hc B A ↔ (rawRVValuePattern '' Section3RVCodeBridge.rawDomain A).Finite := by
  have he : rawRVValuePattern '' Section3RVCodeBridge.rawDomain A =
      (fun x i => Values.vrv (x i)) '' A.carrier := by
    rw [Section3RVCodeBridge.rawDomain, Set.image_image]
    congr 1
    funext x
    exact rawRVValuePattern_of_tuple x
  rw [he]
  rfl

def nativeRESObjectOfRawSet (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ => .rv) A) (hf : (rawRVValuePattern '' A).Finite) :
    GammaGroundRESObject hc B n :=
  nativeRESObjectOfGammaSet hc B (Section3RVCodeBridge.ofRaw A hA)
    ((gammaRVFiniteValues_iff_raw_patterns hc B _).mpr
      (by simpa only [Section3RVCodeBridge.rawDomain_ofRaw] using hf))

end DiamondIntegral.Section5
