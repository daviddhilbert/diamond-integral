import «section 4».GammaFibreIntegralCongruence

/-! Coordinate pullback on the original-base integer-family groups.
Integrating the first coordinate commutes with every substitution among
the remaining coordinates. This uses equality of actual fibre functions. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCoordinatePullback
open GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaFibreIntegralCongruence

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def keepFirst {n m : ℕ} (π : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (π i).succ)

def pullback (B : Base (M := M)) {n m : ℕ} (π : Fin n → Fin m) :
    familySubgroup B n →+ familySubgroup B m where
  toFun f := ⟨(fun z => f.val (z ∘ π)), reindex_definable B f.val f.property π⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pullback_id (B : Base (M := M)) (n : ℕ) :
    pullback B (id : Fin n → Fin n) = AddMonoidHom.id (familySubgroup B n) := by
  ext f z
  rfl

theorem pullback_comp (B : Base (M := M)) {n m l : ℕ} (π : Fin n → Fin m) (ρ : Fin m → Fin l) :
    (pullback B ρ).comp (pullback B π) = pullback B (ρ ∘ π) := by
  ext f z
  rfl

theorem integralFirst_naturality (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : Section4.EulerKind)
    {n m : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) (π : Fin n → Fin m) (y : Fin m → Values.Gamma (M := M)) :
    integralFirst h00 B k (fun z => f (z ∘ keepFirst π)) (reindex_definable B f hf (keepFirst π)) y =
      integralFirst h00 B k f hf (y ∘ π) := by
  apply integralFirst_congr h00 B B k _ _ f hf y (y ∘ π)
  intro x
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem integrateFirst_naturality (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : Section4.EulerKind) {n m : ℕ} (π : Fin n → Fin m) :
    (integrateFirst h00 hκ hs B hr hγ k m).comp (pullback B (keepFirst π)) =
      (pullback B π).comp (integrateFirst h00 hκ hs B hr hγ k n) := by
  apply AddMonoidHom.ext
  intro f
  have hf : IntegerFamilyDefinable B f.val := f.property
  apply Subtype.ext
  funext y
  change integralFirst h00 B k (fun z => f.val (z ∘ keepFirst π))
      (reindex_definable B f.val hf (keepFirst π)) y = integralFirst h00 B k f.val hf (y ∘ π)
  exact integralFirst_naturality h00 B k f.val hf π y

end DiamondIntegral.Section4.GammaCoordinatePullback
