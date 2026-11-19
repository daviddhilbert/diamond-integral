import «section 7».SpecialChainInduction
import «section 6».DiamondSimultaneous
import «section 6».DiamondStandardContraction

/-! Lemma 7.13 (`kernel:dim:1:coa`).

If the lifts of two doubly bounded objects `U`, `V` of `μRV^db[1]` are
isomorphic in `μVF^◇[1]`, then `([U], [V]) ∈ μIsp^db` (`lift_iso_muIsp`).
Lemma 6.38, applied to the composite isomorphism between the lifts of the
charts of `U` and `V`, gives relative aperture chains on both sides and an
isomorphism of the two contractions in `μRV^db[1]`. By Lemma 7.11 each
contraction is reached from `[U]`, respectively `[V]`, by blowups.

`lemma_7_13` is the printed statement for standard contractions, with the
isomorphism `A ≅ B` in `μVF^◇[1]` as hypothesis: Remark 6.28 identifies each
object with the lift of its standard contraction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.KernelDimOne
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section6.DiamondSimultaneous DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.MeasuredRVBounds

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}

/-! ### The class of a contraction of Lemma 6.38 -/

section Matching
variable {r : ℕ} {A B : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {s : ℕ}
variable {B' : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {f : Map A B'} {h00 : M ⊨ Axioms.ACVF00}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable {σ : Map B' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable (H : UnaryRelativeMeasuredMatching (G := G) A B' f h00 ω σ)

/-- A chain set on the source of a matching whose form transports `ω` has the
class of the source contraction. -/
theorem clsG_source (g : Good T H.geometry.source) (hg : ∀ p : A, g.form (H.geometry.sourceMap p) = ω p)
    (hA : ∀ a : Fin 1 → VF M, {u : Fin H.geometry.sourceArity → RVInfinity M |
      (a, u) ∈ H.geometry.source.carrier}.Finite) :
    clsG hc g = cls (objOf hc T (H.sourceRV hA) (H.sourceRV_doublyBounded hA)) := by
  have hform : ∀ q : H.geometry.source, g.form q = H.geometry.sourceForm h00 ω q := by
    intro q
    obtain ⟨p, rfl⟩ := (H.geometry.sourceChain.bijective h00).2 q
    rw [hg, UnaryRelativePreparedMatching.sourceForm_transport]
  symm
  apply cls_objOf_eq hc
  exact contractionIso H.geometry.sourceTagged H.geometry.sourcePullback hA H.geometry.sourceBounded
    (H.geometry.sourceForm h00 ω) H.sourceForm_constant (regularize_tagged _)
    (regularize_pullback _ g.pullback) (regularize_finite _ g.finite) (regularize_vfDoublyBounded _ g.vfBounded)
    (regForm g) (regForm_labels g) (regularization _) (regularization_bijective _)
    (regularization_matching _ H.geometry.sourceTagged) (fun _ => rfl)
    (fun p => (regForm_apply g p).trans (hform p))

/-- The same on the target. -/
theorem clsG_target (g : Good T H.geometry.target) (hg : ∀ p : B', g.form (H.geometry.targetMap p) = σ p)
    (hB : ∀ b : Fin 1 → VF M, {v : Fin H.geometry.targetArity → RVInfinity M |
      (b, v) ∈ H.geometry.target.carrier}.Finite) :
    clsG hc g = cls (objOf hc T (H.targetRV hB) (H.targetRV_doublyBounded hB)) := by
  have hform : ∀ q : H.geometry.target, g.form q = H.geometry.targetForm h00 σ q := by
    intro q
    obtain ⟨p, rfl⟩ := (H.geometry.targetChain.bijective h00).2 q
    rw [hg, UnaryRelativePreparedMatching.targetForm_transport]
  symm
  apply cls_objOf_eq hc
  exact contractionIso H.geometry.targetTagged H.geometry.targetPullback hB H.geometry.targetBounded
    (H.geometry.targetForm h00 σ) H.targetForm_constant (regularize_tagged _)
    (regularize_pullback _ g.pullback) (regularize_finite _ g.finite) (regularize_vfDoublyBounded _ g.vfBounded)
    (regForm g) (regForm_labels g) (regularization _) (regularization_bijective _)
    (regularization_matching _ H.geometry.targetTagged) (fun _ => rfl)
    (fun p => (regForm_apply g p).trans (hform p))

end Matching

/-! ### Lemma 7.13 -/

section Kernel
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
variable (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include h00 hκ hs hv hsmall hΓ hnt in
/-- Lemma 7.13, core form: if the lifts of doubly bounded objects `U`, `V` of
`μRV^db[1]` are isomorphic in `μVF^◇[1]`, then `([U], [V]) ∈ μIsp^db`. -/
theorem lift_iso_muIsp {U V : MeasuredRVObject (M := M) (T : Set M) 1} (hU : U.doublyBounded)
    (hV : V.doublyBounded) (hPU : ProperInvariant (T : Set M) (rvLift U.object).carrier)
    (hPV : ProperInvariant (T : Set M) (rvLift V.object).carrier)
    (F : Isomorphic G (liftObject U hPU) (liftObject V hPV)) :
    MuIsp (k := 0) (cls (objOf hc T U hU)) (cls (objOf hc T V hV)) := by
  have hE := isomorphic_equivalence (G := G) (S := (T : Set M)) (n := 1) h00 hc hκ.le hs hsmall hv
  have hdU : (toMeasured hc (objOf hc T U hU).toChart).doublyBounded :=
    toMeasured_doublyBounded hc h00 lin hκ.le hs hsmall hΓ _ (chartOf_bounded hc U hU) (chartOf_noInfinity hc U hU)
  have hdV : (toMeasured hc (objOf hc T V hV).toChart).doublyBounded :=
    toMeasured_doublyBounded hc h00 lin hκ.le hs hsmall hΓ _ (chartOf_bounded hc V hV) (chartOf_noInfinity hc V hV)
  have hPU' := measuredRVLift_properInvariant h00 hc hκ hs hv _ hdU
  have hPV' := measuredRVLift_properInvariant h00 hc hκ hs hv _ hdV
  have i1 : Isomorphic G (liftObject _ hPU') (liftObject U hPU) :=
    lift_isomorphic_pos h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt one_pos (measuredIso_chartOf hc U) hdU hU hPU' hPU
  have i2 : Isomorphic G (liftObject V hPV) (liftObject _ hPV') :=
    lift_isomorphic_pos h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt one_pos (measuredIso_chartOf hc V).symm hV hdV hPV hPV'
  obtain ⟨Φ⟩ := hE.trans (hE.trans i1 F) i2
  obtain ⟨H, chA, chB, -, -, hA', hB', -, -, -, -, e, -⟩ :=
    lemma_6_38_diamond_contractible h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt Φ
  obtain ⟨gA, hfA, m, hm⟩ := lemma_7_11 (k := 0) hc (objOf hc T U hU).toChart hdU
    (objOf hc T U hU).domain_bounded hκ hs hsmall h00 chA
  obtain ⟨gB, hfB, n, hn⟩ := lemma_7_11 (k := 0) hc (objOf hc T V hV).toChart hdV
    (objOf hc T V hV).domain_bounded hκ hs hsmall h00 chB
  have eA := clsG_source hc H gA hfA hA'
  have eB := clsG_target hc H gB hfB hB'
  have eAB := cls_objOf_eq hc (H.sourceRV_doublyBounded hA') (H.targetRV_doublyBounded hB') e
  refine ⟨clsG hc gA, m, n, hm, ?_⟩
  rw [eA, eAB, ← eB]
  exact hn

include h00 hκ hs hv hsmall hΓ hnt in
/-- Lemma 7.13 (`kernel:dim:1:coa`): if `A ≅ B` in `μVF^◇[1]` and `U`, `V` are
standard contractions of `A`, `B`, then `([U], [V]) ∈ μIsp^db`. -/
theorem lemma_7_13 {A B : VFObject (M := M) (T : Set M) 1} (F : Isomorphic G A B)
    {e₁ e₂ : Equiv.Perm (Fin 1)} (FA : NormalizedMeasuredContraction (G := G) A.carrier A.form e₁)
    (FB : NormalizedMeasuredContraction (G := G) B.carrier B.form e₂) :
    MuIsp (k := 0)
      (cls (objOf hc T (FA.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A Fin.elim0)) (FA.headStartObject_doublyBounded 0 Fin.elim0)))
      (cls (objOf hc T (FB.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin B Fin.elim0)) (FB.headStartObject_doublyBounded 0 Fin.elim0))) := by
  have hE := isomorphic_equivalence (G := G) (S := (T : Set M)) (n := 1) h00 hc hκ.le hs hsmall hv
  obtain ⟨hPU, iA⟩ := remark_6_28 h00 hc lin hκ hs hv hsmall hΓ A FA 0 Fin.elim0
  obtain ⟨hPV, iB⟩ := remark_6_28 h00 hc lin hκ hs hv hsmall hΓ B FB 0 Fin.elim0
  have iA' : Isomorphic G A (liftObject _ hPU) := iA
  have iB' : Isomorphic G B (liftObject _ hPV) := iB
  exact lift_iso_muIsp hc h00 hκ hs hv B₀ hsmall hΓ hnt _ _ hPU hPV (hE.trans (hE.symm iA') (hE.trans F iB'))

end Kernel

end DiamondIntegral.Section7.KernelDimOne
