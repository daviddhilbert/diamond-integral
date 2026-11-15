import «section 5».GammaValueSchemata
import «section 4».GammaGroupNames

/-! Constant Gamma values give uniform full-fibre schemata over every
proper tuple, with exactly the original imaginary parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

def GammaValueSchema.constant (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) : GammaValueSchema B p sp :=
  ⟨⟨{w | (w ∘ Fin.natAdd p) 0 ∈ Values.gammaPullback {α} ∧
      w ∈ sortedUniverse (Fin.append sp (fun _ : Fin 1 => .rv))},
    hα.preimage_real (Fin.append sp (fun _ : Fin 1 => .rv)) (Fin.natAdd p)⟩⟩

theorem GammaValueSchema.constant_row (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (x : Fin 1 → M) :
    Fin.append z x ∈ (GammaValueSchema.constant (sp := sp) α hα).domain.val ↔
      Proper x ∧ codeValue (x 0) = α := by
  change (_ ∈ Values.gammaPullback {α} ∧ _) ↔ _
  simp only [Function.comp_apply, Fin.append_right]
  constructor
  · rintro ⟨hx, _⟩
    have hp : NonzeroRV (x 0) := by obtain ⟨hr, h0, _⟩ := hx; exact ⟨hr, h0⟩
    refine ⟨fun i => ?_, (gammaPullback_mem_codeValue_iff _ _ hp).mp hx⟩
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    exact ⟨hp.1, hp.2⟩
  · rintro ⟨hp, he⟩
    refine ⟨(gammaPullback_mem_codeValue_iff _ _ (hp 0)).mpr he, ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hz j
    · simpa only [Fin.append_right, sortEval, iRV] using (hp j).1

theorem GammaValueSchema.constant_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    (GammaValueSchema.constant (sp := sp) α hα).Valid hc z :=
  GammaValueSchema.valid_of_full_singleton_row hc _ z hz α
    (GammaValueSchema.constant_row α hα z hz)

theorem GammaValueSchema.constant_value (hc : CanonicalStructure.IsCanonical (M := M))
    (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    (GammaValueSchema.constant (sp := sp) α hα).value hc z
      (GammaValueSchema.constant_valid hc α hα z hz) = α := by
  let F := GammaValueSchema.constant (sp := sp) α hα
  let h := GammaValueSchema.constant_valid hc α hα z hz
  obtain ⟨x, hx⟩ := h.2.2
  exact ((F.value_row hc z h x).mp hx).2.symm.trans
    ((GammaValueSchema.constant_row α hα z hz x).mp hx).2

def nativeTorusSchema (B : Base (M := M)) (sp : Fin p → SortTag) : RESSetSchema B p 1 sp :=
  (GammaValueSchema.constant 1 (GammaGroupNames.one_definable_base B) : GammaValueSchema B p sp).resSchema

end DiamondIntegral.Section5
