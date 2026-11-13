import «section 4».RVAdmissibleDisjointInvariants
import «section 4».RVOrdinaryDisjointInvariants

/-! Cut additivity suffices for scissors inside an admissible family,
including RES, with all closure witnesses retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVAdmissibleRestrictionInvariants
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions RVAdmissibleFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Measured {B : Base (M := M)} (F : Family B) (R : Type*) [AddCommGroup R] where
  value : ∀ k (a : Chart B k), F.good k a → R
  iso : ∀ k (a b : Chart B k) (ha : F.good k a) (hb : F.good k b),
    Iso a b → value k a ha = value k b hb
  partition : ∀ {n k} (a : Data B n k) (ha : F.good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I),
    value k a.toChart ha = value k (outside a I hI).toChart (F.outside_good a I hI ha) +
      value k (inside a I hI).toChart (F.inside_good a I hI ha)

structure Ordinary {B : Base (M := M)} (F : Family B) (R : Type*) [AddCommGroup R] where
  value : ∀ k (a : Chart B k), F.good k a → R
  iso : ∀ k (a b : Chart B k) (ha : F.good k a) (hb : F.good k b),
    RVForgetScissors.UnderlyingIso a b → value k a ha = value k b hb
  partition : ∀ {n k} (a : Data B n k) (ha : F.good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I),
    value k a.toChart ha = value k (outside a I hI).toChart (F.outside_good a I hI ha) +
      value k (inside a I hI).toChart (F.inside_good a I hI ha)

theorem measured_scissor_data {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : Measured F R) {n k : ℕ} (a b c d : Data B n k)
    (ha : F.good k a.toChart) (hb : F.good k b.toChart) (hc : F.good k c.toChart) (hd : F.good k d.toChart)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (hD : RVMeasuredGroup.packed d.toChart = RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart) :
    f.value k c.toChart hc + f.value k d.toChart hd = f.value k a.toChart ha + f.value k b.toChart hb := by
  have hA := f.partition a ha b.domain b.domain_definable
  have hU := f.partition c hc b.domain b.domain_definable
  have hO := f.iso k _ _ (F.outside_good a b.domain b.domain_definable ha)
    (F.outside_good c b.domain b.domain_definable hc) (RVScissorComponents.outsideIso a b c hC)
  have hI := f.iso k _ _ (F.inside_good a b.domain b.domain_definable ha) hd (RVScissorComponents.insideLeftIso a b c d hC hD)
  have hJ := f.iso k _ _ (F.inside_good c b.domain b.domain_definable hc) hb (RVScissorComponents.insideUnionIso a b c hC)
  rw [hU, hA, hI, hJ, ← hO]
  abel

theorem measured_scissor {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : Measured F R) {k : ℕ} (a b c d : Chart B k)
    (ha : F.good k a) (hb : F.good k b) (hc : F.good k c) (hd : F.good k d) (h : RVMeasuredGroup.Scissor a b c d) :
    f.value k c hc + f.value k d hd = f.value k a ha + f.value k b hb := by
  rcases a with ⟨aN, aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
  rcases b with ⟨bN, bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
  rcases c with ⟨cN, cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
  rcases d with ⟨dN, dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩
  rcases h with ⟨hab, hac, had, hU, hI⟩
  change aN = bN at hab
  subst bN
  change aN = cN at hac
  subst cN
  change aN = dN at had
  subst dN
  exact measured_scissor_data F f
    ⟨aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
    ⟨bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
    ⟨cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
    ⟨dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩ ha hb hc hd hU hI


theorem ordinary_scissor_data {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : Ordinary F R) {n k : ℕ} (a b c d : Data B n k)
    (ha : F.good k a.toChart) (hb : F.good k b.toChart) (hc : F.good k c.toChart) (hd : F.good k d.toChart)
    (hC : RVForgetScissors.packedDomain c.toChart = RVForgetScissors.packedDomain a.toChart ∪ RVForgetScissors.packedDomain b.toChart)
    (hD : RVForgetScissors.packedDomain d.toChart = RVForgetScissors.packedDomain a.toChart ∩ RVForgetScissors.packedDomain b.toChart) :
    f.value k c.toChart hc + f.value k d.toChart hd = f.value k a.toChart ha + f.value k b.toChart hb := by
  have hA := f.partition a ha b.domain b.domain_definable
  have hU := f.partition c hc b.domain b.domain_definable
  have hO := f.iso k _ _ (F.outside_good a b.domain b.domain_definable ha)
    (F.outside_good c b.domain b.domain_definable hc) (RVOrdinaryScissorComponents.outsideIso a b c hC)
  have hI := f.iso k _ _ (F.inside_good a b.domain b.domain_definable ha) hd (RVOrdinaryScissorComponents.insideLeftIso a b d hD)
  have hJ := f.iso k _ _ (F.inside_good c b.domain b.domain_definable hc) hb (RVOrdinaryScissorComponents.insideUnionIso a b c hC)
  rw [hU, hA, hI, hJ, ← hO]
  abel

theorem ordinary_scissor {B : Base (M := M)} (F : Family B) {R : Type*} [AddCommGroup R]
    (f : Ordinary F R) {k : ℕ} (a b c d : Chart B k)
    (ha : F.good k a) (hb : F.good k b) (hc : F.good k c) (hd : F.good k d) (h : RVForgetScissors.Scissor a b c d) :
    f.value k c hc + f.value k d hd = f.value k a ha + f.value k b hb := by
  rcases a with ⟨aN, aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
  rcases b with ⟨bN, bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
  rcases c with ⟨cN, cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
  rcases d with ⟨dN, dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩
  rcases h with ⟨hab, hac, had, hU, hI⟩
  change aN = bN at hab
  subst bN
  change aN = cN at hac
  subst cN
  change aN = dN at had
  subst dN
  exact ordinary_scissor_data F f
    ⟨aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
    ⟨bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
    ⟨cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
    ⟨dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩ ha hb hc hd hU hI


end DiamondIntegral.Section4.RVAdmissibleRestrictionInvariants
