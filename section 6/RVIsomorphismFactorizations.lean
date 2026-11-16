import «section 6».MeasuredRVGlobalAssembly
import «section 6».MeasuredRVChainForgetting

/-! Lemma 6.29 in every positive degree, with arbitrary RV dimension.
Actual original-base chains recover the prescribed morphism. Both
measured and unmeasured variants retain finite volume, and all bounds
hold at every intermediate object in the doubly bounded variants. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem lemma_6_29_measured (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) :
    ∃ T : MeasuredRVUnaryChain S n U V, T.iso.iso.hom.map = e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  obtain ⟨r,D,hD,hCover,hPieces⟩ := exists_measured_rv_factorizations_on_finite_cover hc h00 hκ hs hsmall hn e
  choose T hT hTB using hPieces
  exact exists_measured_rv_factorization_from_cover hc hn e D hD hCover T hT hTB

theorem lemma_6_29_measured_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ T : MeasuredRVUnaryChain S n U V, T.iso.iso.hom.map = e.iso.hom.map ∧ T.doublyBounded := by
  obtain ⟨T,hT,hB⟩ := lemma_6_29_measured hc h00 hκ hs hsmall hn e
  exact ⟨T,hT,hB ⟨hU,hV⟩⟩

theorem lemma_6_29 (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero) (hV : ∀ v k, (V.value v k).val ≠ iRVZero) :
    ∃ T : RVUnaryChain S n U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume ∧
      ((RVObjectDoublyBounded U ∧ RVObjectDoublyBounded V) → T.doublyBounded) := by
  let E := structuralMeasuredRVIso hc e hUF hVF hU hV
  obtain ⟨T,hT,hTB⟩ := lemma_6_29_measured hc h00 hκ hs hsmall hn E
  exact ⟨T.forget,T.forget_map.trans hT,T.forget_finiteVolume,
    fun hB => T.forget_doublyBounded (hTB hB)⟩

theorem lemma_6_29_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero) (hV : ∀ v k, (V.value v k).val ≠ iRVZero)
    (hUB : RVObjectDoublyBounded U) (hVB : RVObjectDoublyBounded V) :
    ∃ T : RVUnaryChain S n U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume ∧ T.doublyBounded := by
  obtain ⟨T,hT,hTF,hTB⟩ := lemma_6_29 hc h00 hκ hs hsmall hn e hUF hVF hU hV
  exact ⟨T,hT,hTF,hTB ⟨hUB,hVB⟩⟩

end DiamondIntegral.Section6
