import «section 3».BoundedNativeVFBridge
import «section 5».Completed18LocalKernel
import «section 5».NativeLiftGroundTransfer
import IntegrationSection6.FiniteNonzeroIntegration
import IntegrationSection6.GammaNonzeroIspSemiring
import IntegrationSection6.GammaNonzeroBasicRelation
import IntegrationSection6.GammaGlobalAdditiveLift
import IntegrationSection6.GammaNonzeroThroughEmbeddings

/-! Theorem 3.22, bounded part, from the fixed-degree integral of [18]
(`integrationThroughAt`, its Proposition 6.18 in the nonzero-coordinate
filtered form). The manuscript bounded source `⊕_{i ≤ k} K₊RV[i]` maps to
the native stage `k` through the proved global comparison of RV
semirings; the stage congruence of [18] is the restriction of its global
special congruence, which the global comparison identifies with the
manuscript special congruence. Lift classes are matched in the native
global VF semigroup, into which the native `VF[k]` semigroup embeds by
the fixed-degree theorem. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B₀ B : Base (M := M)} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
  (hr : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real) (hγ : Cardinal.mk B.gamma < κ)
  (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hB : VFGammaGeneratedBase B)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩


section NativeStage

/-- The native fixed-degree lift, followed into the global VF semigroup,
is the global lift of the stage element. -/
theorem boundedNative_lift_through (k : ℕ) (x : GammaNonzeroThroughAt (B := B) (S := Set.univ) k) :
    gammaVFFiniteToAllAdditive (((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm (((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk' x)) = (gammaNonzeroGlobalAdditiveLiftAt (B := B) (S := Set.univ) hκ hs h00 hr hB) (gammaThroughToGradedAt k x) := by
  rw [gammaNonzeroGlobalAdditiveLiftAt_through]
  rfl

include hκ hs h00 hr FBase hγ δ hδ hδ1 hB in
/-- The native `VF[k]` semigroup embeds in the native global VF semigroup. -/
theorem boundedNative_toAll_injective (k : ℕ) :
    Function.Injective (gammaVFFiniteToAllAdditive (B := B) (k := k)) := by
  intro y₁ y₂ h
  obtain ⟨z₁,rfl⟩ := ((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm.surjective y₁
  obtain ⟨z₂,rfl⟩ := ((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm.surjective y₂
  obtain ⟨x₁,rfl⟩ := ((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk'_surjective z₁
  obtain ⟨x₂,rfl⟩ := ((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk'_surjective z₂
  rw [boundedNative_lift_through,boundedNative_lift_through] at h
  have hu : (gammaNonzeroIspUnionAddCon (B := B) hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) (gammaThroughToGradedAt k x₁) (gammaThroughToGradedAt k x₂) := by
    rw [gammaNonzeroIspUnionAddCon_eq_lift_kernel]
    exact h
  rw [gammaNonzeroIspUnionAddCon_stage_iff] at hu
  exact congrArg ((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm (((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).eq.mpr hu)

end NativeStage

section RVStage
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B₀ sn D → DefinableOverBase B sn D)
variable (K : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase B₀ sn D)

/-- The global comparison of RV semirings, through the base change. -/
def boundedRVGraded : GammaGroundRVPositiveSemiring hc B₀ →+ GammaNonzeroGradedAt (B := B) (S := Set.univ) :=
  (completed18RVPositiveEquiv (hc := hc) (B := B)).toAddMonoidHom.comp
    (sortedTransferRVPositive (hc := hc) H).toAddMonoidHom

theorem boundedRVGraded_class {i : ℕ} (U : GammaGroundRVObject hc B₀ i) :
    boundedRVGraded H (gammaGroundRVSemiringClass U) =
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) i
        (gammaNonzeroClassAt (groundRVAt (sortedTransferRVObject H U)) (groundRVAt_full _)) := by
  change completed18RVPositiveEquiv (sortedTransferRVPositive H (gammaGroundRVSemiringClass U)) = _
  rw [sortedTransferRVPositive_class,completed18RVPositiveEquiv_class]

theorem boundedRVGraded_bounded_class {k : ℕ} (i : Fin (k+1)) (U : GammaGroundRVObject hc B₀ i.val) :
    boundedRVGraded H (gammaGroundRVBoundedInclude (gammaGroundRVBoundedClass i U)) =
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) i.val
        (gammaNonzeroClassAt (groundRVAt (sortedTransferRVObject H U)) (groundRVAt_full _)) := by
  rw [gammaGroundRVBoundedInclude_class,boundedRVGraded_class]

theorem boundedRVGraded_support {k : ℕ} (a : GammaGroundRVBoundedPositive hc B₀ k) (j : ℕ) (hj : k < j) :
    boundedRVGraded H (gammaGroundRVBoundedInclude a) j = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]; rfl
  | of i c =>
    obtain ⟨U,rfl⟩ := gammaGroundRVClass_surjective c
    change boundedRVGraded H (gammaGroundRVBoundedInclude (gammaGroundRVBoundedClass i U)) j = 0
    rw [boundedRVGraded_bounded_class]
    exact DirectSum.of_eq_of_ne _ _ _ (by have := i.isLt; omega)
  | add a b ha hb =>
    rw [map_add,map_add]
    change boundedRVGraded H (gammaGroundRVBoundedInclude a) j +
      boundedRVGraded H (gammaGroundRVBoundedInclude b) j = 0
    rw [ha,hb,add_zero]

/-- The manuscript bounded RV source in the native stage `k`. -/
def boundedRVNative (k : ℕ) :
    GammaGroundRVBoundedPositive hc B₀ k →+ GammaNonzeroThroughAt (B := B) (S := Set.univ) k :=
  (gammaGradedToThroughAt k).comp ((boundedRVGraded H).comp gammaGroundRVBoundedInclude)

theorem boundedRVNative_embed {k : ℕ} (a : GammaGroundRVBoundedPositive hc B₀ k) :
    gammaThroughToGradedAt k (boundedRVNative H k a) = boundedRVGraded H (gammaGroundRVBoundedInclude a) :=
  gammaThroughToGradedAt_project k _ (boundedRVGraded_support H a)

include K in
theorem boundedRVNative_surjective (k : ℕ) : Function.Surjective (boundedRVNative (hc := hc) H k) := by
  have key : ∀ g : GammaNonzeroGradedAt (B := B) (S := Set.univ),
      ∃ a : GammaGroundRVBoundedPositive hc B₀ k, boundedRVNative H k a = gammaGradedToThroughAt k g := by
    intro g
    induction g using DirectSum.induction_on with
    | zero => exact ⟨0,by simp only [map_zero]⟩
    | of i c =>
      by_cases hi : i ≤ k
      · let U : GammaGroundRVObject hc B i :=
          nativeRVGroundObject (nativeRVClassRepresentative c) (nativeRVClassRepresentative_full c)
        let U₀ : GammaGroundRVObject hc B₀ i := sortedTransferRVObject K U
        let i' : Fin (k+1) := ⟨i,Nat.lt_succ_of_le hi⟩
        refine ⟨gammaGroundRVBoundedClass i' U₀,?_⟩
        change gammaGradedToThroughAt k (boundedRVGraded H
          (gammaGroundRVBoundedInclude (gammaGroundRVBoundedClass i' U₀))) = _
        congr 1
        rw [gammaGroundRVBoundedInclude_class]
        change completed18RVPositiveEquiv (sortedTransferRVPositive H
          (gammaGroundRVSemiringClass (sortedTransferRVObject K U))) = _
        rw [← sortedTransferRVPositive_class K U,sortedTransferRVPositive_left_inv K H,
          completed18RVPositiveEquiv_class]
        congr 1
        have h₁ : gammaNonzeroClassAt (groundRVAt U) (groundRVAt_full U) =
            groundRVClassNative (gammaGroundRVClass U) := (groundRVClassNative_class U).symm
        rw [h₁]
        exact groundRVClassNative_native c
      · refine ⟨0,?_⟩
        rw [map_zero,gammaGradedToThroughAt_of_above k i c (by omega)]
    | add g h hg hh =>
      obtain ⟨a,ha⟩ := hg
      obtain ⟨b,hb⟩ := hh
      exact ⟨a+b,by rw [map_add,map_add,ha,hb]⟩
  intro x
  obtain ⟨a,ha⟩ := key (gammaThroughToGradedAt k x)
  exact ⟨a,ha.trans (gammaGradedToThroughAt_embed k x)⟩

end RVStage

section Lift
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B₀ sn D → DefinableOverBase B sn D)
variable (K : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase B₀ sn D)
variable (hdim : ∀ {n r : ℕ} (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (k : ℕ),
  Section2.vfDimension D.carrier ≤ (k : WithBot ℕ) ↔ GammaHasVFDimLE B D.carrier k)

omit [Valued (Section2.VF M) G] in
theorem boundedTransfer_lift_carrier {i : ℕ} (U : GammaGroundRVObject hc B₀ i) :
    (gammaGroundObjectLift (sortedTransferRVObject H U)).carrier = (gammaGroundObjectLift U).carrier := by
  ext q
  change (∃ u : (sortedTransferRVObject H U).domain, u.val = q.2 ∧
      ((sortedTransferRVObject H U).volume u).val = Section2.tupleRV M q.1) ↔
    ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = Section2.tupleRV M q.1
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,(sortedTransferRVVolume_value H U u).symm.trans hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,(sortedTransferRVVolume_value H U ⟨u.val,u.property⟩).trans hv⟩

/-- The bounded lift `⊕_{i ≤ k} K₊RV[i] → K₊VF[k]` obtained from [18]. -/
def boundedNativeLift (k : ℕ) : GammaGroundRVBoundedPositive hc B₀ k →+ GammaGroundVFKPlus hc B₀ k :=
  (boundedVFNativeEquiv (k := k) H K hdim).symm.toAddMonoidHom.comp
    (((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm.toAddMonoidHom.comp (((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk'.comp (boundedRVNative H k)))

theorem boundedNativeLift_apply {k : ℕ} (a : GammaGroundRVBoundedPositive hc B₀ k) :
    boundedVFNativeEquiv H K hdim (boundedNativeLift hκ hs h00 hr FBase hγ δ hδ hδ1 hB H K hdim k a) =
      ((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm (((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk' (boundedRVNative H k a)) :=
  (boundedVFNativeEquiv H K hdim).apply_symm_apply _

theorem boundedNativeLift_class {k : ℕ} (i : Fin (k+1)) (U : GammaGroundRVObject hc B₀ i.val) :
    boundedNativeLift hκ hs h00 hr FBase hγ δ hδ hδ1 hB H K hdim k (gammaGroundRVBoundedClass i U) =
      gammaGroundVFClass ((gammaGroundObjectLiftVF U).raise (Nat.le_of_lt_succ i.isLt)) := by
  apply (boundedVFNativeEquiv H K hdim).injective
  rw [boundedNativeLift_apply,boundedVFNativeEquiv_class]
  apply boundedNative_toAll_injective hκ hs h00 hr FBase hγ δ hδ hδ1 hB
  rw [boundedNative_lift_through,boundedRVNative_embed,boundedRVGraded_bounded_class,
    gammaVFFiniteToAllAdditive_class]
  rw [gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of]
  change gammaAllAdditiveLiftClassesAt hκ hs h00 hr hB
    (gammaIsoClassAt (groundRVAt (sortedTransferRVObject H U))) = _
  rw [gammaAllAdditiveLiftClassesAt_class]
  unfold gammaAllAdditiveLiftClass
  symm
  apply PositiveAdditiveGrothendieck.of_iso
  refine ⟨(gammaIso_reflexive _ (gammaVFAllFromBounded (boundedGroundNative H hdim
    ((gammaGroundObjectLiftVF U).raise (Nat.le_of_lt_succ i.isLt)))).definable).congr rfl ?_⟩
  exact ((boundedTransfer_lift_carrier H U).symm.trans
    (groundRVAt_lift_domain (sortedTransferRVObject H U)).symm)

theorem boundedNativeLift_surjective (k : ℕ) :
    Function.Surjective (boundedNativeLift hκ hs h00 hr FBase hγ δ hδ hδ1 hB H K hdim k) :=
  (boundedVFNativeEquiv H K hdim).symm.surjective.comp
    (((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm.surjective.comp (((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk'_surjective.comp (boundedRVNative_surjective H K k)))

theorem boundedNativeLift_kernel (k : ℕ) :
    gammaGroundRVBoundedSpecialCongruence (ground := B₀) (k := k) hc =
      AddCon.ker (boundedNativeLift hκ hs h00 hr FBase hγ δ hδ hδ1 hB H K hdim k) := by
  ext a b
  rw [AddCon.ker_rel]
  change (gammaGroundRVSpecialCongruence hc B₀).mk' (gammaGroundRVBoundedInclude a) =
      (gammaGroundRVSpecialCongruence hc B₀).mk' (gammaGroundRVBoundedInclude b) ↔ _
  rw [show ∀ x y, (gammaGroundRVSpecialCongruence hc B₀).mk' x = (gammaGroundRVSpecialCongruence hc B₀).mk' y ↔
      gammaGroundRVSpecialCongruence hc B₀ x y from fun x y => (gammaGroundRVSpecialCongruence hc B₀).eq]
  rw [← sortedTransferRVPositive_special_iff (H := K) (K := H),completed18RVSpecial_iff,
    ← gammaNonzeroIsp_eq_basic hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB]
  change gammaNonzeroIspUnionAddCon (B := B) hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB (boundedRVGraded H (gammaGroundRVBoundedInclude a))
    (boundedRVGraded H (gammaGroundRVBoundedInclude b)) ↔ _
  rw [← boundedRVNative_embed H a,← boundedRVNative_embed H b,gammaNonzeroIspUnionAddCon_stage_iff,
    ← show ((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk' (boundedRVNative H k a) = ((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).mk' (boundedRVNative H k b) ↔ _ from ((gammaNonzeroThroughIspAt (B := B) hκ hs h00 hr) k).eq]
  constructor
  · intro h
    apply (boundedVFNativeEquiv H K hdim).injective
    rw [boundedNativeLift_apply,boundedNativeLift_apply,h]
  · intro h
    have h' := congrArg (boundedVFNativeEquiv H K hdim) h
    rw [boundedNativeLift_apply,boundedNativeLift_apply] at h'
    exact ((integrationThroughAt hκ hs h00 hr FBase hγ δ hδ hδ1 (completed_section5_input hκ hs) hB) k).symm.injective h'

end Lift

end DiamondIntegral.Section3
