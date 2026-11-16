import «section 6».FiniteBoundedMeasuredRVFactorizations

/-! Forgetting Gamma forms preserves the complete relatively unary
factorization, its actual label map, finite volume and intermediate bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def MeasuredRVUnaryChain.forget {U V : MeasuredRVObject (M := M) S n} :
    MeasuredRVUnaryChain S n U V → RVUnaryChain S n U.object V.object
  | .identity U => .identity U.object
  | .step i e h T => .step i e.iso h T.forget

theorem MeasuredRVUnaryChain.forget_map {U V : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n U V) : T.forget.iso.hom.map = T.iso.iso.hom.map := by
  induction T with
  | identity U => rfl
  | step i e h T ih =>
    apply Map.ext
    intro u
    change T.forget.iso.hom.map (e.iso.hom.map u) = T.iso.iso.hom.map (e.iso.hom.map u)
    rw [ih]

theorem MeasuredRVUnaryChain.forget_finiteVolume {U V : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n U V) : T.forget.finiteVolume := by
  induction T with
  | identity U => exact U.finiteVolume
  | @step U V W i e h T ih => exact ⟨U.finiteVolume,ih⟩

theorem MeasuredRVUnaryChain.forget_doublyBounded {U V : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n U V) (hT : T.doublyBounded) : T.forget.doublyBounded := by
  induction T with
  | identity U => exact hT
  | step i e h T ih => exact ⟨hT.1,ih hT.2⟩

theorem lemma_6_29_finite_labels_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hFin : U.domain.carrier.Finite) (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u j, (U.value u j).val ≠ iRVZero) (hV : ∀ v j, (V.value v j).val ≠ iRVZero)
    (hUB : RVObjectDoublyBounded U) (hVB : RVObjectDoublyBounded V) :
    ∃ T : RVUnaryChain S n U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume ∧ T.doublyBounded := by
  let e₀ := structuralMeasuredRVIso hc e hUF hVF hU hV
  obtain ⟨T,hT,hTB⟩ := lemma_6_29_measured_finite_labels_doublyBounded hc hn e₀ hFin hUB hVB
  exact ⟨T.forget,T.forget_map.trans hT,T.forget_finiteVolume,T.forget_doublyBounded hTB⟩

end DiamondIntegral.Section6
