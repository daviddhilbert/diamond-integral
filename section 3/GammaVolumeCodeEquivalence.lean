import «section 3».GammaDensityCodeRows
import «section 3».GammaQuotientFunctionRows

/-! Equality in the existing Gamma imaginary is a definable equivalence
of complete RV codes. Its domain and all representatives are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def gammaVolumeCodePairIndices : Fin 1 ⊕ Fin 1 → Fin (1+1) :=
  Sum.elim (Fin.castAdd 1) (Fin.natAdd 1)

def gammaVolumeCodeEq : Set (Fin (1+1) → M) :=
  {w | w ∘ gammaVolumeCodePairIndices ∈ (volumeGammaSpace hc).relation (volumeGammaSpace hc) Eq}

theorem gammaVolumeCodeEq_definable :
    DefinableOverBase B (Fin.append (fun _ : Fin 1 => .rv) (fun _ : Fin 1 => .rv))
      (gammaVolumeCodeEq (hc := hc)) := by
  have hd : B.real.Definable LRV (gammaVolumeCodeEq (hc := hc)) :=
    ((volumeGammaSpace hc).diagonal_definable.mono (Set.empty_subset B.real)).preimage_comp gammaVolumeCodePairIndices
  have hp : ∀ w ∈ gammaVolumeCodeEq (hc := hc), ∀ i,
      sortEval (Fin.append (fun _ : Fin 1 => .rv) (fun _ : Fin 1 => .rv) i) (w i) := by
    intro w hw i
    obtain ⟨hx,hy,_⟩ := hw
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> fin_cases j
    · exact hx.1
    · exact hy.1
  exact (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hp).mp
    (GammaGroundRawDefinable.of_real hd)

theorem gammaVolumeCodeEq_append (c d : (volumeGammaSpace hc).domain) :
    Fin.append c.val d.val ∈ gammaVolumeCodeEq (hc := hc) ↔
      (volumeGammaSpace hc).decode c = (volumeGammaSpace hc).decode d := by
  have he : Fin.append c.val d.val ∘ gammaVolumeCodePairIndices = Sum.elim c.val d.val := by
    funext i
    cases i <;> simp only [gammaVolumeCodePairIndices,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fin.append_left,Fin.append_right]
  change _ ∈ (volumeGammaSpace hc).relation (volumeGammaSpace hc) Eq ↔ _
  rw [he,(volumeGammaSpace hc).relation_decode (volumeGammaSpace hc)]

end DiamondIntegral.Section3
