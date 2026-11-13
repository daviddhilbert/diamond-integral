import «section 4».GammaFubiniTwo
import «section 4».GammaFamilySlicesTwo
import «section 4».GammaFibreIntegralCongruence
import «section 4».GammaParameterExtension

/-! Commute the first two actual coordinate integrals in a Gamma family
with any finite parameter suffix. The two-coordinate theorem is applied
over the explicitly enlarged Gamma base; fibre congruence identifies its
values with the original-base integrals. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaParametricFubini
open GammaDefinableEuler GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral
open GammaFamilySlicesTwo GammaFibreIntegralCongruence GammaParameterExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def swapFirstTwoIndex (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases (0 : Fin (n + 1)).succ (Fin.cases 0 (fun i => i.succ.succ))

def swapFirstTwo {n : ℕ} (f : (Fin (n + 2) → Values.Gamma (M := M)) → ℤ) :
    (Fin (n + 2) → Values.Gamma (M := M)) → ℤ := fun z => f (z ∘ swapFirstTwoIndex n)

theorem swapFirstTwo_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin (n + 2) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    IntegerFamilyDefinable B (swapFirstTwo f) := reindex_definable B f hf (swapFirstTwoIndex n)

def integralTwoAt (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 2) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) : ℤ :=
  integralFirst h00 B k (integralFirst h00 B k f hf)
    (integralFirst_definable h00 hκ hs B hr hγ k f hf) y

theorem commute_first_two (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 2) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) :
    integralTwoAt h00 hκ hs B hr hγ k f hf y =
      integralTwoAt h00 hκ hs B hr hγ k (swapFirstTwo f) (swapFirstTwo_definable B f hf) y := by
  let B' := GammaBaseExtension.withGamma B (Set.range y)
  have hγ' : Cardinal.mk B'.gamma < κ := finite_gamma_extension_small hκ B hγ y
  have hΓ' : Section2.NontrivialDefinableGamma B' := nontrivial_extend B (Set.range y) hΓ
  let g := sliceTwo f y
  have hg : IntegerFamilyDefinable B' g := sliceTwo_definable B f hf y
  have hgs := GammaFubiniTwo.swapFamily_definable B' g hg
  have hfs := swapFirstTwo_definable B f hf
  have hleft : integralTwoAt h00 hκ hs B hr hγ k f hf y =
      integrateAll h00 hκ hs B' hr hγ' k 2 ⟨g, hg⟩ := by
    change integralFirst h00 B k (integralFirst h00 B k f hf)
        (integralFirst_definable h00 hκ hs B hr hγ k f hf) y =
      integralFirst h00 B' k (integralFirst h00 B' k g hg)
        (integralFirst_definable h00 hκ hs B' hr hγ' k g hg) emptyTuple
    apply integralFirst_congr h00 B B' k
      (integralFirst h00 B k f hf) (integralFirst_definable h00 hκ hs B hr hγ k f hf)
      (integralFirst h00 B' k g hg) (integralFirst_definable h00 hκ hs B' hr hγ' k g hg) y emptyTuple
    intro b
    exact integralFirst_congr h00 B B' k f hf g hg (Fin.cons b y) (Fin.cons b emptyTuple) (fun a => rfl)
  have hright : integralTwoAt h00 hκ hs B hr hγ k (swapFirstTwo f) hfs y =
      integrateAll h00 hκ hs B' hr hγ' k 2 ⟨GammaFubiniTwo.swapFamily g, hgs⟩ := by
    change integralFirst h00 B k (integralFirst h00 B k (swapFirstTwo f) hfs)
        (integralFirst_definable h00 hκ hs B hr hγ k (swapFirstTwo f) hfs) y =
      integralFirst h00 B' k (integralFirst h00 B' k (GammaFubiniTwo.swapFamily g) hgs)
        (integralFirst_definable h00 hκ hs B' hr hγ' k (GammaFubiniTwo.swapFamily g) hgs) emptyTuple
    apply integralFirst_congr h00 B B' k
      (integralFirst h00 B k (swapFirstTwo f) hfs)
      (integralFirst_definable h00 hκ hs B hr hγ k (swapFirstTwo f) hfs)
      (integralFirst h00 B' k (GammaFubiniTwo.swapFamily g) hgs)
      (integralFirst_definable h00 hκ hs B' hr hγ' k (GammaFubiniTwo.swapFamily g) hgs) y emptyTuple
    intro b
    apply integralFirst_congr h00 B B' k (swapFirstTwo f) hfs (GammaFubiniTwo.swapFamily g) hgs
      (Fin.cons b y) (Fin.cons b emptyTuple)
    intro a
    change f ((Fin.cons a (Fin.cons b y)) ∘ swapFirstTwoIndex n) = f (Fin.cons b (Fin.cons a y))
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  exact hleft.trans ((GammaFubiniTwo.fubini_two h00 linear hκ hs B' hr hγ' hΓ' k g hg).trans hright.symm)

end DiamondIntegral.Section4.GammaParametricFubini
