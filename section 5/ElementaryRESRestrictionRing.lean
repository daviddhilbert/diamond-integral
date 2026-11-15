import «section 5».ElementaryNativeRESValues
import «section 4».Section3RESNativeRingMaps

/-! Elementary restriction gives a ring homomorphism on the actual
ordinary RES presentation. Auxiliary degrees are forgotten in the target,
while every original parameter and every domain coordinate is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
open RVChartDisjointUnion RVMeasuredCharts Section3RESClassCuts Section3RVCodeBridge RVChartRestrictions
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M)
local notation "Bₙ" => EmptyGammaGround.base (Set.range (e ∘ c))
local notation "Bₘ" => EmptyGammaGround.base (Set.range c)
local notation "v" => elementaryNativeRESValue hcM hcN e c

def elementaryRESChartValue {k : ℕ} (a : RESChart Bₙ k) : RESDimensionFreeRing.Ring Bₘ :=
  v (Section3RVChartBridge.nativeRES hcN a)

theorem elementaryRESChartValue_partition {n k : ℕ} (a : Data Bₙ n k)
    (ha : (RVAdmissibleFamilies.res Bₙ).good k a.toChart)
    (I : Set (Fin n → N)) (hI : DefinableOverBase Bₙ (fun _ : Fin n => .rv) I) :
    elementaryRESChartValue hcM hcN e c ⟨a.toChart,ha⟩ =
      elementaryRESChartValue hcM hcN e c ⟨(outside a I hI).toChart,
        (RVAdmissibleFamilies.res Bₙ).outside_good a I hI ha⟩ +
      elementaryRESChartValue hcM hcN e c ⟨(inside a I hI).toChart,
        (RVAdmissibleFamilies.res Bₙ).inside_good a I hI ha⟩ := by
  let U := ordinaryNative hcN a.toChart ha
  let X := ofRaw (hc := hcN) (a.domain ∩ I) (a.domain_definable.inter hI)
  have hX : X.carrier ⊆ U.obj.domain.carrier := fun _ hx => hx.1
  have hi : v (U.restrict X hX) =
      v (ordinaryNative hcN (inside a I hI).toChart ((RVAdmissibleFamilies.res Bₙ).inside_good a I hI ha)) :=
    elementaryNativeRESValue_bijection hcM hcN e c _ _
      (Section3RVRestrictionBridge.nativeRestrictionIso a.toChart _ _ (fun _ hx => hx.1))
  have ho : v (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) =
      v (ordinaryNative hcN (outside a I hI).toChart ((RVAdmissibleFamilies.res Bₙ).outside_good a I hI ha)) :=
    elementaryNativeRESValue_bijection hcM hcN e c _ _ (Section3RVClassCuts.complementIso a I hI)
  have h := elementaryNativeRESValue_cut hcM hcN e c U X hX
  rw [hi,ho] at h
  exact h.symm.trans (add_comm _ _)

def elementaryRESRestrictionCutInvariant :
    RVAdmissibleRestrictionInvariants.Ordinary (RVAdmissibleFamilies.res Bₙ) (RESDimensionFreeRing.Ring Bₘ) where
  value _ a ha := elementaryRESChartValue hcM hcN e c ⟨a,ha⟩
  iso _ _ _ _ _ f := elementaryNativeRESValue_bijection hcM hcN e c _ _
    (Section3RVRoundtripBridge.nativeIso f)
  partition := elementaryRESChartValue_partition hcM hcN e c

def elementaryRESRestrictionInvariant : RESOrdinaryRing.Invariant Bₙ (RESDimensionFreeRing.Ring Bₘ) where
  value _ a := elementaryRESChartValue hcM hcN e c a
  unit := (elementaryNativeRESValue_bijection hcM hcN e c _ _
    Section3RVBasicClasses.nativeUnitIso).trans (elementaryNativeRESValue_unit hcM hcN e c)
  product _ _ a b := by
    have h := elementaryNativeRESValue_bijection hcM hcN e c
      ((Section3RVChartBridge.nativeRES hcN b).product (Section3RVChartBridge.nativeRES hcN a))
      (Section3RVChartBridge.nativeRES hcN (RVMeasuredProductProperties.resProduct a b))
      (Section3RVBasicClasses.nativeProductIso a.toChart b.toChart)
    exact h.symm.trans ((elementaryNativeRESValue_product hcM hcN e c _ _).trans (mul_comm _ _))
  iso _ _ _ f := elementaryNativeRESValue_bijection hcM hcN e c _ _
    (Section3RVRoundtripBridge.nativeIso f)
  empty k a ha := by
    have hD : (Section3RVChartBridge.nativeRES hcN a).obj.domain.carrier = ∅ := by
      ext x
      change rvValues x ∈ a.domain ↔ False
      rw [ha]
      rfl
    exact (elementaryNativeRESValue_bijection hcM hcN e c _ _
      (GammaGroundBijection.ofEmpty hD (show (GammaGroundRESObject.empty hcN Bₙ k).obj.domain.carrier = ∅ from rfl))).trans
        (elementaryNativeRESValue_empty hcM hcN e c k)
  scissor _ a b d f h := RVAdmissibleRestrictionInvariants.ordinary_scissor (RVAdmissibleFamilies.res Bₙ)
    (elementaryRESRestrictionCutInvariant hcM hcN e c) a.toChart b.toChart d.toChart f.toChart
    a.finite_values b.finite_values d.finite_values f.finite_values h

def elementaryRESOrdinaryRestriction : RESOrdinaryRing.Ring Bₙ →+* RESDimensionFreeRing.Ring Bₘ :=
  RESOrdinaryRing.lift Bₙ (elementaryRESRestrictionInvariant hcM hcN e c)

theorem elementaryRESOrdinaryRestriction_class {k : ℕ} (a : RESChart Bₙ k) :
    elementaryRESOrdinaryRestriction hcM hcN e c (RESOrdinaryRing.objectClass a) =
      elementaryRESChartValue hcM hcN e c a :=
  RESOrdinaryRing.lift_objectClass Bₙ (elementaryRESRestrictionInvariant hcM hcN e c) a

theorem elementaryRESOrdinaryRestriction_degreeIdeal :
    RESDimensionFreeRing.degreeIdeal Bₙ ≤ RingHom.ker (elementaryRESOrdinaryRestriction hcM hcN e c) := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,l,a,b,f,rfl⟩
  change elementaryRESOrdinaryRestriction hcM hcN e c (_ - _) = 0
  rw [map_sub,elementaryRESOrdinaryRestriction_class,elementaryRESOrdinaryRestriction_class]
  exact sub_eq_zero.mpr (elementaryNativeRESValue_bijection hcM hcN e c _ _
    (bijectionOfRaw a.domain b.domain a.domain_definable b.domain_definable
      f.extension f.extension_graph f.extension_bijOn))

def elementaryRESUngradedRestriction : RESDimensionFreeRing.Ring Bₙ →+* RESDimensionFreeRing.Ring Bₘ :=
  Ideal.Quotient.lift (RESDimensionFreeRing.degreeIdeal Bₙ) (elementaryRESOrdinaryRestriction hcM hcN e c)
    (fun _ h => elementaryRESOrdinaryRestriction_degreeIdeal hcM hcN e c h)

end DiamondIntegral.Section5
