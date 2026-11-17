import «section 3».GammaChainClosureDescent
import «section 3».GammaElementaryLiftJacobian

/-! The generated-base elementary construction can be run inside dcl,
then descended. Its Jacobian is computed over the original VF field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gammaAdmissible_closure {U : GammaRVObject B n}
    (hU : (closureBase B).real ⊆ U.codes) {i : Fin n} (h : GammaAdmissible U i) :
    GammaAdmissible (gammaRVObjectClosure U hU) i where
  nonzero := h.nonzero
  algebraic u := (h.algebraic u).mono (by
    rintro x (hx | hx)
    · exact Or.inl ((subset_closureBase B).1 hx)
    · exact Or.inr hx) (subset_closureBase B).2

theorem gammaElementaryDiagram_exists_original
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    {U : GammaRVObject B n} (hU : (closureBase B).real ⊆ U.codes)
    {i : Fin n} (h : GammaAdmissible U i) : Nonempty (ElementaryLiftDiagram U i) := by
  obtain ⟨D⟩ := lemma_6_12 hκ.le hs h00 (closureBase_real_small hκ B hr hg) hB (gammaAdmissible_closure hU h)
  exact ⟨gammaElementaryDiagram_closure_descent hU D⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaElementaryLift_exists_original_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : GammaRVObject B n} (hU : (closureBase B).real ⊆ U.codes)
    {i : Fin n} (h : GammaAdmissible U i) :
    ∃ D : ElementaryLiftDiagram U i, ∀ p : typedLift U.object,
      AlgebraicIndependent (vfParameterField B.real) (show Fin n → Section2.VF M from p.val.1) →
        HasMixedVFJacobianAt D.liftIso.equiv p 1 := by
  obtain ⟨D⟩ := gammaElementaryDiagram_exists_original hκ hs h00 hr hg hB hU h
  exact ⟨D,gammaElementaryLift_jacobian_one hc hκ.le hs hr hv D⟩

end DiamondIntegral.Section3
