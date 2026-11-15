import «section 5».OriginalRVTagDomains
import «section 5».RESSetSchemaRecoding

/-! Tagged sums of native RES families have exact literal rows and an
explicit sum bound on their full value supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def nativeZeroValue : Values.GammaTop (M := M) := Values.vrv ⟨iRVZero, rv_zero_mem hM⟩
def nativeOneValue : Values.GammaTop (M := M) := Values.vrv ⟨iRVOne, rv_one_mem hM⟩

def valuePatternLeftTag (b : ℕ) (x : Fin a → Values.GammaTop (M := M)) :
    Fin (1+(a+b)) → Values.GammaTop (M := M) :=
  Fin.append (fun _ : Fin 1 => nativeZeroValue) (Fin.append x (fun _ : Fin b => nativeZeroValue))
def valuePatternRightTag (a : ℕ) (y : Fin b → Values.GammaTop (M := M)) :
    Fin (1+(a+b)) → Values.GammaTop (M := M) :=
  Fin.append (fun _ : Fin 1 => nativeOneValue) (Fin.append (fun _ : Fin a => nativeZeroValue) y)

theorem rawRVValuePattern_append {a b : ℕ} (x : Fin a → M) (y : Fin b → M) :
    rawRVValuePattern (Fin.append x y) = Fin.append (rawRVValuePattern x) (rawRVValuePattern y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rawRVValuePattern, Fin.append_left, Fin.append_right]

theorem rawRVValuePattern_constant {n : ℕ} (c : M) (hc : iRV c) :
    rawRVValuePattern (fun _ : Fin n => c) = fun _ => Values.vrv ⟨c, hc⟩ := by
  funext i
  exact dif_pos hc

theorem rawRVLeftTag_valuePattern (x : Fin a → M) :
    rawRVValuePattern (rawRVLeftTag b x) = valuePatternLeftTag b (rawRVValuePattern x) := by
  simp only [rawRVLeftTag, valuePatternLeftTag, rawRVValuePattern_append,
    rawRVValuePattern_constant iRVZero (rv_zero_mem hM), nativeZeroValue]

theorem rawRVRightTag_valuePattern (y : Fin b → M) :
    rawRVValuePattern (rawRVRightTag a y) = valuePatternRightTag a (rawRVValuePattern y) := by
  simp only [rawRVRightTag, valuePatternRightTag, rawRVValuePattern_append,
    rawRVValuePattern_constant iRVZero (rv_zero_mem hM),
    rawRVValuePattern_constant iRVOne (rv_one_mem hM), nativeZeroValue, nativeOneValue]

def RESSetSchema.sum (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) :
    RESSetSchema B p (1+(a+b)) sp := ⟨nativeRVTaggedDomain F.domain G.domain, F.valueBound+G.valueBound⟩

theorem RESSetSchema.sum_row (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (z : Fin p → M) (w : Fin (1+(a+b)) → M) :
    w ∈ (F.sum G).rowDomain z ↔
      (∃ x ∈ F.rowDomain z, w = rawRVLeftTag b x) ∨
      (∃ y ∈ G.rowDomain z, w = rawRVRightTag a y) :=
  nativeRVTaggedDomain_row F.domain G.domain z w

theorem RESSetSchema.sum_value_image (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (z : Fin p → M) :
    rawRVValuePattern '' (F.sum G).rowDomain z =
      (valuePatternLeftTag b '' (rawRVValuePattern '' F.rowDomain z)) ∪
      (valuePatternRightTag a '' (rawRVValuePattern '' G.rowDomain z)) := by
  ext γ
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases (F.sum_row G z w).mp hw with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨_, ⟨x, hx, rfl⟩, (rawRVLeftTag_valuePattern x).symm⟩
    · exact Or.inr ⟨_, ⟨y, hy, rfl⟩, (rawRVRightTag_valuePattern y).symm⟩
  · rintro (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨_, ⟨y, hy, rfl⟩, rfl⟩)
    · exact ⟨rawRVLeftTag b x, (F.sum_row G z _).mpr (Or.inl ⟨x, hx, rfl⟩), rawRVLeftTag_valuePattern x⟩
    · exact ⟨rawRVRightTag a y, (F.sum_row G z _).mpr (Or.inr ⟨y, hy, rfl⟩), rawRVRightTag_valuePattern y⟩

theorem RESSetSchema.sum_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) : (F.sum G).Valid hc z := by
  obtain ⟨hz, hf, hn⟩ := (F.valid_iff_finite_values hc z).mp hF
  obtain ⟨_, hg, hm⟩ := (G.valid_iff_finite_values hc z).mp hG
  apply ((F.sum G).valid_iff_finite_values hc z).mpr
  rw [F.sum_value_image G z]
  refine ⟨hz, (hf.image _).union (hg.image _), ?_⟩
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add
    ((Set.ncard_image_le hf).trans hn) ((Set.ncard_image_le hg).trans hm))

theorem RESSetSchema.sum_recode_row
    (R : GammaParameterRecode B p q sp sq) (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (z : Fin p → M) (t : Fin q → M)
    (hF : R.DomainAgreement F.domain z t) (hG : R.DomainAgreement G.domain z t)
    (w : Fin (1+(a+b)) → M) :
    w ∈ (F.sum G).rowDomain z ↔ w ∈ ((F.recode R).sum (G.recode R)).rowDomain t := by
  rw [F.sum_row G, (F.recode R).sum_row (G.recode R)]
  exact or_congr (exists_congr (fun x => and_congr (hF x) Iff.rfl))
    (exists_congr (fun y => and_congr (hG y) Iff.rfl))

end DiamondIntegral.Section5
