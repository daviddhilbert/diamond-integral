import «section 4».GammaGermLogic
import «section 4».GammaWeightedFamilies
import «section 4».EulerGerms

/-! Canonical step coefficients of actual weighted Gamma fibres are
finite-range original-base definable families. Left/right germs and the
far-left value are characterized in the Gamma language; no endpoints or
RV representatives are added to the conclusion's base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaGermFamilies
open GammaOrderLogic GammaDefinableEuler GammaFamilyIntegration GammaIntegerFamilies
open GammaWeightedFamilies GammaGermLogic EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def germFamily (right : Bool) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) : ℤ :=
  let F := fibreFunction h00 B k f hf (fun j => z j.succ)
  if right then rightValue k F (toPaperGamma (z 0)) else leftValue k F (toPaperGamma (z 0))

def tailFamily (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) : ℤ := tailValue k (fibreFunction h00 B k f hf y)

theorem germFamily_level_iff (right : Bool) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (k : EulerKind) {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) (z : Fin (n + 1) → Values.Gamma (M := M)) (m : ℤ) :
    germFamily right h00 B k f hf z = m ↔
      z ∈ if right then RightGerm {w | f w = m} else LeftGerm {w | f w = m} := by
  cases right
  · simp only [germFamily, Bool.false_eq_true, ite_false]
    rw [leftValue_eq_iff]
    change (∃ l : Values.Gamma (M := M), l < z 0 ∧ ∀ x : Values.Gamma (M := M),
      l < x → x < z 0 → fibreFunction h00 B k f hf (fun j => z j.succ) (toPaperGamma x) = m) ↔ _
    simp only [fibreFunction_eval]
    rfl
  · simp only [germFamily, ite_true]
    rw [rightValue_eq_iff]
    change (∃ u : Values.Gamma (M := M), z 0 < u ∧ ∀ x : Values.Gamma (M := M),
      z 0 < x → x < u → fibreFunction h00 B k f hf (fun j => z j.succ) (toPaperGamma x) = m) ↔ _
    simp only [fibreFunction_eval]
    rfl

theorem tailFamily_level_iff (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) (m : ℤ) :
    tailFamily h00 B k f hf y = m ↔ y ∈ Tail {w | f w = m} := by
  rw [tailFamily, tailValue_eq_iff]
  change (∃ l : Values.Gamma (M := M), ∀ x : Values.Gamma (M := M),
    x < l → fibreFunction h00 B k f hf y (toPaperGamma x) = m) ↔ _
  simp only [fibreFunction_eval]
  rfl

theorem germFamily_definable (right : Bool) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (k : EulerKind) {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) : IntegerFamilyDefinable B (germFamily right h00 B k f hf) := by
  refine ⟨hf.1.subset ?_, ?_⟩
  · rintro m ⟨z, rfl⟩
    let F := fibreFunction h00 B k f hf (fun j => z j.succ)
    have hm : germFamily right h00 B k f hf z ∈ Set.range (F : PaperGamma (M := M) → ℤ) := by
      cases right
      · exact leftValue_mem_range k F (toPaperGamma (z 0))
      · exact rightValue_mem_range k F (toPaperGamma (z 0))
    obtain ⟨x, hx⟩ := hm
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    exact ⟨Fin.cons γ (fun j => z j.succ),
      (fibreFunction_eval h00 B k f hf (fun j => z j.succ) γ).symm.trans hx⟩
  · intro m
    have h : GammaDefinable B (if right then RightGerm {w | f w = m} else LeftGerm {w | f w = m}) := by
      cases right
      · exact leftGerm_definable B _ (hf.2 m)
      · exact rightGerm_definable B _ (hf.2 m)
    convert h using 1
    ext z
    exact germFamily_level_iff right h00 B k f hf z m

theorem tailFamily_definable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    IntegerFamilyDefinable B (tailFamily h00 B k f hf) := by
  refine ⟨hf.1.subset ?_, ?_⟩
  · rintro m ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := tailValue_mem_range k (fibreFunction h00 B k f hf y)
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    exact ⟨Fin.cons γ y, (fibreFunction_eval h00 B k f hf y γ).symm.trans hx⟩
  · intro m
    convert tail_definable B {w | f w = m} (hf.2 m) using 1
    ext y
    exact tailFamily_level_iff h00 B k f hf y m

def pointCoefficientFamily (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) : ℤ :=
  ((coefficientEquiv k).symm (fibreFunction h00 B k f hf (fun j => z j.succ))).2.1 (toPaperGamma (z 0))

def rayCoefficientFamily (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) : ℤ :=
  ((coefficientEquiv k).symm (fibreFunction h00 B k f hf (fun j => z j.succ))).2.2 (toPaperGamma (z 0))

theorem pointCoefficientFamily_eq (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) :
    pointCoefficientFamily h00 B k f hf z = f z - germFamily false h00 B k f hf z := by
  rw [pointCoefficientFamily, pointCoefficient_eq, fibreFunction_eval]
  have hez : Fin.cons (z 0) (fun j => z j.succ) = z := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  rw [hez]
  rfl

theorem rayCoefficientFamily_eq (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) :
    rayCoefficientFamily h00 B k f hf z = germFamily true h00 B k f hf z - germFamily false h00 B k f hf z := by
  exact rayCoefficient_eq k (fibreFunction h00 B k f hf (fun j => z j.succ)) (toPaperGamma (z 0))

theorem pointCoefficientFamily_definable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (k : EulerKind) {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) : IntegerFamilyDefinable B (pointCoefficientFamily h00 B k f hf) := by
  convert combine_definable B f (germFamily false h00 B k f hf) hf
    (germFamily_definable false h00 B k f hf) (fun a b => a - b) using 1
  funext z
  exact pointCoefficientFamily_eq h00 B k f hf z

theorem rayCoefficientFamily_definable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (k : EulerKind) {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) : IntegerFamilyDefinable B (rayCoefficientFamily h00 B k f hf) := by
  convert combine_definable B (germFamily true h00 B k f hf) (germFamily false h00 B k f hf)
    (germFamily_definable true h00 B k f hf) (germFamily_definable false h00 B k f hf)
    (fun a b => a - b) using 1
  funext z
  exact rayCoefficientFamily_eq h00 B k f hf z

end DiamondIntegral.Section4.GammaGermFamilies
