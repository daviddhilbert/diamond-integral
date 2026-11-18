import «section 5».ElementaryRESExtensionData
import «section 5».ElementaryRESFibreQuotient
import «section 5».PuiseuxAmbientComparison

/-! The elementary restriction on the reduced ungraded RES ring is an
isomorphism. Its inverse extends every actual RES domain over the named
coefficients by the same definition in the larger model; both composites
are the identity on actual chart classes. -/
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
local notation "X" => elementaryNativeRVExtension hcM hcN e c
local notation "R" => elementaryNativeRVRestriction hcM hcN e c

/-! ## Extension of native domains commutes with the RES operations -/

theorem elementaryNativeRVExtension_product {n m : ℕ}
    (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (E : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) m)) :
    (X (gammaGroundRVProductDomain D E)).carrier = (gammaGroundRVProductDomain (X D) (X E)).carrier := by
  apply elementaryNativeRVExtension_carrier_eq
  rw [elementaryNativeRVRestriction_product]
  ext x
  rw [rv_product_mem_projections,rv_product_mem_projections,elementaryNativeRVRestriction_extension,
    elementaryNativeRVRestriction_extension]

theorem elementaryNativeRVExtension_sdiff {n : ℕ}
    (D E : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n)) :
    (X (D.sdiff E)).carrier = ((X D).sdiff (X E)).carrier := by
  apply elementaryNativeRVExtension_carrier_eq
  rw [elementaryNativeRVRestriction_sdiff]
  ext x
  change (x ∈ (R (X D)).carrier ∧ x ∉ (R (X E)).carrier) ↔ (x ∈ D.carrier ∧ x ∉ E.carrier)
  rw [elementaryNativeRVRestriction_extension,elementaryNativeRVRestriction_extension]

/-! ## Values of extended native RES objects -/

def elementaryNativeRESExtension {k : ℕ} (U : GammaGroundRESObject hcM Bₘ k) :
    GammaGroundRESObject hcN Bₙ U.obj.arity :=
  nativeRESObjectOfGammaSet hcN _ (X U.obj.domain)
    (elementaryNativeRVExtension_finite hcM hcN e c U.obj.domain U.property)

local notation "W" => elementaryNativeRESExtension hcM hcN e c

def elementaryNativeRESExtensionValue {k : ℕ} (U : GammaGroundRESObject hcM Bₘ k) :
    RESDimensionFreeRing.Ring Bₙ :=
  nativeUngradedClass hcN (W U)

local notation "w" => elementaryNativeRESExtensionValue hcM hcN e c

theorem elementaryNativeRESExtensionValue_bijection {k l : ℕ}
    (U : GammaGroundRESObject hcM Bₘ k) (V : GammaGroundRESObject hcM Bₘ l)
    (f : GammaGroundBijection U.obj.domain V.obj.domain) : w U = w V :=
  nativeUngradedClass_bijection hcN _ _ (elementaryNativeRVExtensionBijection hcM hcN e c f)

theorem elementaryNativeRESExtensionValue_empty (k : ℕ) :
    w (GammaGroundRESObject.empty hcM Bₘ k) = 0 := by
  have hD : (W (GammaGroundRESObject.empty hcM Bₘ k)).obj.domain.carrier = ∅ :=
    elementaryNativeRVExtension_carrier_eq hcM hcN e c (GammaGroundRESObject.empty hcN Bₙ k).obj.domain _
      ((elementaryNativeRVRestriction_empty hcM hcN e c k).trans rfl)
  exact (nativeUngradedClass_bijection hcN _ (GammaGroundRESObject.empty hcN Bₙ 0)
    (GammaGroundBijection.ofEmpty hD rfl)).trans (nativeUngradedClass_empty hcN Bₙ 0)

theorem elementaryNativeRESExtensionValue_product {k l : ℕ}
    (U : GammaGroundRESObject hcM Bₘ k) (V : GammaGroundRESObject hcM Bₘ l) :
    w (U.product V) = w U * w V :=
  (nativeUngradedClass_bijection hcN (W (U.product V)) ((W U).product (W V))
    (GammaGroundBijection.ofCarrierEq
      (elementaryNativeRVExtension_product hcM hcN e c U.obj.domain V.obj.domain))).trans
    (nativeUngradedClass_product hcN _ _)

theorem elementaryNativeRESExtensionValue_cut {k : ℕ} (U : GammaGroundRESObject hcM Bₘ k)
    (Y : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) U.obj.arity))
    (hY : Y.carrier ⊆ U.obj.domain.carrier) :
    w (U.restrict Y hY) + w (U.restrict (U.obj.domain.sdiff Y) (fun _ h => h.1)) = w U := by
  let U' := W U
  have hY' : (X Y).carrier ⊆ U'.obj.domain.carrier :=
    elementaryNativeRVExtension_subset hcM hcN e c Y U.obj.domain hY
  have h₁ := nativeUngradedClass_bijection hcN (W (U.restrict Y hY)) (U'.restrict (X Y) hY')
    (GammaGroundBijection.ofCarrierEq rfl)
  have h₂ := nativeUngradedClass_bijection hcN
    (W (U.restrict (U.obj.domain.sdiff Y) (fun _ h => h.1)))
    (U'.restrict (U'.obj.domain.sdiff (X Y)) (fun _ h => h.1))
    (GammaGroundBijection.ofCarrierEq (elementaryNativeRVExtension_sdiff hcM hcN e c U.obj.domain Y))
  exact (congrArg₂ (· + ·) h₁ h₂).trans (nativeUngradedClass_cut hcN U' (X Y) hY')

theorem elementaryNativeRESExtensionValue_unit :
    w (GammaGroundRESObject.unit hcM Bₘ) = 1 := by
  apply (nativeUngradedClass_bijection hcN (W (GammaGroundRESObject.unit hcM Bₘ))
    (GammaGroundRESObject.unit hcN Bₙ) ?_).trans (nativeUngradedClass_unit hcN Bₙ)
  apply GammaGroundBijection.ofCarrierEq
  apply elementaryNativeRVExtension_carrier_eq
  ext x
  change x ∈ (R (GammaGroundRESObject.unit hcN Bₙ).obj.domain).carrier ↔
    x ∈ (GammaGroundRESObject.unit hcM Bₘ).obj.domain.carrier
  rw [elementaryNativeRVRestriction_mem]
  rfl

/-! ## The extension ring homomorphism on ordinary chart classes -/

def elementaryRESExtensionChartValue {k : ℕ} (a : RESChart Bₘ k) : RESDimensionFreeRing.Ring Bₙ :=
  w (Section3RVChartBridge.nativeRES hcM a)

theorem elementaryRESExtensionChartValue_partition {n k : ℕ} (a : Data Bₘ n k)
    (ha : (RVAdmissibleFamilies.res Bₘ).good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase Bₘ (fun _ : Fin n => .rv) I) :
    elementaryRESExtensionChartValue hcM hcN e c ⟨a.toChart,ha⟩ =
      elementaryRESExtensionChartValue hcM hcN e c ⟨(outside a I hI).toChart,
        (RVAdmissibleFamilies.res Bₘ).outside_good a I hI ha⟩ +
      elementaryRESExtensionChartValue hcM hcN e c ⟨(inside a I hI).toChart,
        (RVAdmissibleFamilies.res Bₘ).inside_good a I hI ha⟩ := by
  let U := ordinaryNative hcM a.toChart ha
  let Y := ofRaw (hc := hcM) (a.domain ∩ I) (a.domain_definable.inter hI)
  have hY : Y.carrier ⊆ U.obj.domain.carrier := fun _ hx => hx.1
  have hi : w (U.restrict Y hY) =
      w (ordinaryNative hcM (inside a I hI).toChart ((RVAdmissibleFamilies.res Bₘ).inside_good a I hI ha)) :=
    elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _
      (Section3RVRestrictionBridge.nativeRestrictionIso a.toChart _ _ (fun _ hx => hx.1))
  have ho : w (U.restrict (U.obj.domain.sdiff Y) (fun _ h => h.1)) =
      w (ordinaryNative hcM (outside a I hI).toChart ((RVAdmissibleFamilies.res Bₘ).outside_good a I hI ha)) :=
    elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _ (Section3RVClassCuts.complementIso a I hI)
  have h := elementaryNativeRESExtensionValue_cut hcM hcN e c U Y hY
  rw [hi,ho] at h
  exact h.symm.trans (add_comm _ _)

def elementaryRESExtensionCutInvariant :
    RVAdmissibleRestrictionInvariants.Ordinary (RVAdmissibleFamilies.res Bₘ) (RESDimensionFreeRing.Ring Bₙ) where
  value _ a ha := elementaryRESExtensionChartValue hcM hcN e c ⟨a,ha⟩
  iso _ _ _ _ _ f := elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _
    (Section3RVRoundtripBridge.nativeIso f)
  partition := elementaryRESExtensionChartValue_partition hcM hcN e c

def elementaryRESExtensionInvariant : RESOrdinaryRing.Invariant Bₘ (RESDimensionFreeRing.Ring Bₙ) where
  value _ a := elementaryRESExtensionChartValue hcM hcN e c a
  unit := (elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _
    Section3RVBasicClasses.nativeUnitIso).trans (elementaryNativeRESExtensionValue_unit hcM hcN e c)
  product _ _ a b := by
    have h := elementaryNativeRESExtensionValue_bijection hcM hcN e c
      ((Section3RVChartBridge.nativeRES hcM b).product (Section3RVChartBridge.nativeRES hcM a))
      (Section3RVChartBridge.nativeRES hcM (RVMeasuredProductProperties.resProduct a b))
      (Section3RVBasicClasses.nativeProductIso a.toChart b.toChart)
    exact h.symm.trans ((elementaryNativeRESExtensionValue_product hcM hcN e c _ _).trans (mul_comm _ _))
  iso _ _ _ f := elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _
    (Section3RVRoundtripBridge.nativeIso f)
  empty k a ha := by
    have hD : (Section3RVChartBridge.nativeRES hcM a).obj.domain.carrier = ∅ := by
      ext x
      change rvValues x ∈ a.domain ↔ False
      rw [ha]
      rfl
    exact (elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _
      (GammaGroundBijection.ofEmpty hD (show (GammaGroundRESObject.empty hcM Bₘ k).obj.domain.carrier = ∅ from rfl))).trans
        (elementaryNativeRESExtensionValue_empty hcM hcN e c k)
  scissor _ a b d f h := RVAdmissibleRestrictionInvariants.ordinary_scissor (RVAdmissibleFamilies.res Bₘ)
    (elementaryRESExtensionCutInvariant hcM hcN e c) a.toChart b.toChart d.toChart f.toChart
    a.finite_values b.finite_values d.finite_values f.finite_values h

def elementaryRESOrdinaryExtension : RESOrdinaryRing.Ring Bₘ →+* RESDimensionFreeRing.Ring Bₙ :=
  RESOrdinaryRing.lift Bₘ (elementaryRESExtensionInvariant hcM hcN e c)

theorem elementaryRESOrdinaryExtension_class {k : ℕ} (a : RESChart Bₘ k) :
    elementaryRESOrdinaryExtension hcM hcN e c (RESOrdinaryRing.objectClass a) =
      elementaryRESExtensionChartValue hcM hcN e c a :=
  RESOrdinaryRing.lift_objectClass Bₘ (elementaryRESExtensionInvariant hcM hcN e c) a

theorem elementaryRESOrdinaryExtension_degreeIdeal :
    RESDimensionFreeRing.degreeIdeal Bₘ ≤ RingHom.ker (elementaryRESOrdinaryExtension hcM hcN e c) := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,l,a,b,f,rfl⟩
  change elementaryRESOrdinaryExtension hcM hcN e c (_ - _) = 0
  rw [map_sub,elementaryRESOrdinaryExtension_class,elementaryRESOrdinaryExtension_class]
  exact sub_eq_zero.mpr (elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _
    (bijectionOfRaw a.domain b.domain a.domain_definable b.domain_definable
      f.extension f.extension_graph f.extension_bijOn))

def elementaryRESUngradedExtension : RESDimensionFreeRing.Ring Bₘ →+* RESDimensionFreeRing.Ring Bₙ :=
  Ideal.Quotient.lift (RESDimensionFreeRing.degreeIdeal Bₘ) (elementaryRESOrdinaryExtension hcM hcN e c)
    (fun _ h => elementaryRESOrdinaryExtension_degreeIdeal hcM hcN e c h)

/-! ## Value fibres extend to value fibres -/

theorem elementaryRESExtensionChartValue_fibre (β : Values.Gamma (M := M))
    (hβ : GammaDefinableClosureAtBase Bₘ β) (α : Values.Gamma (M := N))
    (hα : GammaDefinableClosureAtBase Bₙ α)
    (hext : (elementaryActualExtension e c ⟨fullRawValueFibre β,
      (fullRawValueFibre_definable_iff hcM _ β).mpr hβ⟩).val = fullRawValueFibre α) :
    elementaryRESExtensionChartValue hcM hcN e c
      (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)) =
    RESDimensionFreeRing.objectClass
      (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)) := by
  let V := Section3RVChartBridge.nativeRES hcN
    (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ))
  have hraw : nativeRawDomainSet hcM c (Section3RVChartBridge.nativeRES hcM
      (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ))).obj.domain =
      ⟨fullRawValueFibre β,(fullRawValueFibre_definable_iff hcM _ β).mpr hβ⟩ := by
    apply Subtype.ext
    change rawDomain (ofRaw (hc := hcM)
      (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)).domain
      (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)).domain_definable) = _
    rw [rawDomain_ofRaw,fibre_domain_eq_full]
  have h := nativeUngradedClass_bijection hcN
    (W (Section3RVChartBridge.nativeRES hcM
      (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ)))) V
    (GammaGroundBijection.ofCarrierEq (by
      apply Set.ext
      intro (t : Fin 1 → CanonicalRV.RVSort N)
      change rvValues t ∈ (elementaryActualExtension e c (nativeRawDomainSet hcM c (Section3RVChartBridge.nativeRES hcM
          (RESFibreObjects.fibre Bₘ β 1 hβ (GammaGroupNames.one_definable_base Bₘ))).obj.domain)).val ↔
        rvValues t ∈ (RESFibreObjects.fibre Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)).domain
      rw [hraw,hext,fibre_domain_eq_full]))
  refine h.trans ?_
  change RESDimensionFreeRing.objectClass (Section3RVChartBridge.chartRES V) = _
  exact RESDimensionFreeRing.objectClass_iso _ _
    (RVUnderlyingIsomorphisms.ofFixed (Section3RVRoundtripBridge.chart_native _))

def elementaryRESOrdinaryReducedExtension : RESOrdinaryRing.Ring Bₘ →+* RESDimensionFreeReduction.Ring Bₙ :=
  (RESDimensionFreeReduction.quotient Bₙ).comp (elementaryRESOrdinaryExtension hcM hcN e c)

theorem elementaryRESExtension_kills_fibres : RESOrdinaryReduction.fibreIdeal Bₘ ≤
    RingHom.ker (elementaryRESOrdinaryReducedExtension hcM hcN e c) := by
  apply Ideal.span_le.mpr
  rintro x ⟨β,hβ,rfl⟩
  obtain ⟨α,hα,_,hext⟩ := elementary_value_fibre_extension hcM hcN e c β hβ
  obtain ⟨α₁,hα₁,he₁,hext₁⟩ := elementary_value_fibre_extension hcM hcN e c 1
    (GammaGroupNames.one_definable_base Bₘ)
  have h₁ : α₁ = 1 := Subtype.ext (he₁.symm.trans (elementaryGammaTopMap_one e))
  subst h₁
  change elementaryRESOrdinaryReducedExtension hcM hcN e c (_ - _) = 0
  rw [map_sub]
  change RESDimensionFreeReduction.quotient Bₙ
    (elementaryRESOrdinaryExtension hcM hcN e c (RESOrdinaryRing.objectClass _)) -
    RESDimensionFreeReduction.quotient Bₙ
    (elementaryRESOrdinaryExtension hcM hcN e c (RESOrdinaryRing.objectClass _)) = 0
  simp only [RESFibreObjects.torus]
  rw [elementaryRESOrdinaryExtension_class,elementaryRESOrdinaryExtension_class,
    elementaryRESExtensionChartValue_fibre hcM hcN e c β hβ α hα hext,
    elementaryRESExtensionChartValue_fibre hcM hcN e c 1 (GammaGroupNames.one_definable_base Bₘ)
      1 hα₁ hext₁]
  change RESDimensionFreeReduction.fromOrdinary Bₙ (RESOrdinaryRing.objectClass _) -
    RESDimensionFreeReduction.fromOrdinary Bₙ (RESOrdinaryRing.objectClass _) = 0
  exact sub_eq_zero.mpr (congrArg (RESDimensionFreeReduction.fromGradedReduced Bₙ)
    (RESOrdinaryReduction.fibre_class Bₙ α 1 hα (GammaGroupNames.one_definable_base Bₙ)))

def elementaryRESUngradedReducedExtension :
    RESDimensionFreeRing.Ring Bₘ →+* RESDimensionFreeReduction.Ring Bₙ :=
  (RESDimensionFreeReduction.quotient Bₙ).comp (elementaryRESUngradedExtension hcM hcN e c)

theorem elementaryRESUngradedReducedExtension_kills_fibres : RESDimensionFreeReduction.fibreIdeal Bₘ ≤
    RingHom.ker (elementaryRESUngradedReducedExtension hcM hcN e c) := by
  apply Ideal.map_le_iff_le_comap.mpr
  exact elementaryRESExtension_kills_fibres hcM hcN e c

/-- The inverse of the elementary restriction: extension of every actual
RES domain over the named coefficients to the larger model. -/
def elementaryRESReducedExtension :
    RESDimensionFreeReduction.Ring Bₘ →+* RESDimensionFreeReduction.Ring Bₙ :=
  Ideal.Quotient.lift (RESDimensionFreeReduction.fibreIdeal Bₘ)
    (elementaryRESUngradedReducedExtension hcM hcN e c)
    (fun _ h => elementaryRESUngradedReducedExtension_kills_fibres hcM hcN e c h)

/-! ## Both composites are the identity -/

theorem reducedRESRing_hom_ext {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF] (B : Base (M := Q))
    {T : Type*} [CommRing T] (f g : RESDimensionFreeReduction.Ring B →+* T)
    (h : ∀ k (a : RESChart B k),
      f (RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a)) =
        g (RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a))) : f = g := by
  apply Ideal.Quotient.ringHom_ext (I := RESDimensionFreeReduction.fibreIdeal B)
  apply Ideal.Quotient.ringHom_ext (I := RESDimensionFreeRing.degreeIdeal B)
  exact RESOrdinaryRing.hom_ext B _ _ h

theorem nativeUngradedClass_nativeRES {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF]
    (hc : CanonicalStructure.IsCanonical (M := Q)) {B : Base (M := Q)} {k : ℕ} (a : RESChart B k) :
    nativeUngradedClass hc (Section3RVChartBridge.nativeRES hc a) = RESDimensionFreeRing.objectClass a := by
  change RESDimensionFreeRing.objectClass
    (Section3RVChartBridge.chartRES (Section3RVChartBridge.nativeRES hc a)) = _
  exact RESDimensionFreeRing.objectClass_iso _ _
    (RVUnderlyingIsomorphisms.ofFixed (Section3RVRoundtripBridge.chart_native _))

theorem elementaryRESReducedRestriction_class {k : ℕ} (a : RESChart Bₙ k) :
    elementaryRESReducedRestriction hcM hcN e c
      (RESDimensionFreeReduction.fromOrdinary Bₙ (RESOrdinaryRing.objectClass a)) =
      RESDimensionFreeReduction.quotient Bₘ (elementaryRESChartValue hcM hcN e c a) := by
  change RESDimensionFreeReduction.quotient Bₘ
    (elementaryRESOrdinaryRestriction hcM hcN e c (RESOrdinaryRing.objectClass a)) = _
  rw [elementaryRESOrdinaryRestriction_class]

theorem elementaryRESReducedExtension_class {k : ℕ} (a : RESChart Bₘ k) :
    elementaryRESReducedExtension hcM hcN e c
      (RESDimensionFreeReduction.fromOrdinary Bₘ (RESOrdinaryRing.objectClass a)) =
      RESDimensionFreeReduction.quotient Bₙ (elementaryRESExtensionChartValue hcM hcN e c a) := by
  change RESDimensionFreeReduction.quotient Bₙ
    (elementaryRESOrdinaryExtension hcM hcN e c (RESOrdinaryRing.objectClass a)) = _
  rw [elementaryRESOrdinaryExtension_class]

theorem elementaryRESChartValue_chartRES {k : ℕ} (U : GammaGroundRESObject hcN Bₙ k) :
    elementaryRESChartValue hcM hcN e c (Section3RVChartBridge.chartRES U) =
      elementaryNativeRESValue hcM hcN e c U :=
  elementaryNativeRESValue_bijection hcM hcN e c _ _ (Section3RVRoundtripBridge.native_chart U.obj)

theorem elementaryRESExtensionChartValue_chartRES {k : ℕ} (U : GammaGroundRESObject hcM Bₘ k) :
    elementaryRESExtensionChartValue hcM hcN e c (Section3RVChartBridge.chartRES U) = w U :=
  elementaryNativeRESExtensionValue_bijection hcM hcN e c _ _ (Section3RVRoundtripBridge.native_chart U.obj)

theorem elementaryNativeRESValue_extension {k : ℕ} (U : GammaGroundRESObject hcM Bₘ k) :
    elementaryNativeRESValue hcM hcN e c (W U) = nativeUngradedClass hcM U :=
  nativeUngradedClass_bijection hcM _ _ (GammaGroundBijection.ofCarrierEq
    (elementaryNativeRVRestriction_extension hcM hcN e c U.obj.domain))

theorem elementaryNativeRESExtensionValue_restriction {k : ℕ} (U : GammaGroundRESObject hcN Bₙ k) :
    w (elementaryNativeRESRestriction hcM hcN e c U) = nativeUngradedClass hcN U :=
  nativeUngradedClass_bijection hcN _ _ (GammaGroundBijection.ofCarrierEq
    (elementaryNativeRVExtension_restriction hcM hcN e c U.obj.domain))

theorem elementaryRESReducedRestriction_comp_extension :
    (elementaryRESReducedRestriction hcM hcN e c).comp (elementaryRESReducedExtension hcM hcN e c) =
      RingHom.id _ := by
  apply reducedRESRing_hom_ext
  intro k a
  rw [RingHom.comp_apply,RingHom.id_apply,elementaryRESReducedExtension_class]
  change elementaryRESReducedRestriction hcM hcN e c (RESDimensionFreeReduction.fromOrdinary Bₙ
    (RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES
      (W (Section3RVChartBridge.nativeRES hcM a))))) = _
  rw [elementaryRESReducedRestriction_class,elementaryRESChartValue_chartRES,
    elementaryNativeRESValue_extension,nativeUngradedClass_nativeRES]
  rfl

theorem elementaryRESReducedExtension_comp_restriction :
    (elementaryRESReducedExtension hcM hcN e c).comp (elementaryRESReducedRestriction hcM hcN e c) =
      RingHom.id _ := by
  apply reducedRESRing_hom_ext
  intro k a
  rw [RingHom.comp_apply,RingHom.id_apply,elementaryRESReducedRestriction_class]
  change elementaryRESReducedExtension hcM hcN e c (RESDimensionFreeReduction.fromOrdinary Bₘ
    (RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES
      (elementaryNativeRESRestriction hcM hcN e c (Section3RVChartBridge.nativeRES hcN a))))) = _
  rw [elementaryRESReducedExtension_class,elementaryRESExtensionChartValue_chartRES,
    elementaryNativeRESExtensionValue_restriction,nativeUngradedClass_nativeRES]
  rfl

/-- The elementary restriction is a ring isomorphism, with inverse the
extension `elementaryRESReducedExtension`. -/
def elementaryRESReducedRestrictionEquiv :
    RESDimensionFreeReduction.Ring Bₙ ≃+* RESDimensionFreeReduction.Ring Bₘ :=
  RingEquiv.ofRingHom (elementaryRESReducedRestriction hcM hcN e c)
    (elementaryRESReducedExtension hcM hcN e c)
    (elementaryRESReducedRestriction_comp_extension hcM hcN e c)
    (elementaryRESReducedExtension_comp_restriction hcM hcN e c)

theorem elementaryRESReducedRestrictionEquiv_apply (x : RESDimensionFreeReduction.Ring Bₙ) :
    elementaryRESReducedRestrictionEquiv hcM hcN e c x = elementaryRESReducedRestriction hcM hcN e c x :=
  rfl

theorem elementaryRESReducedRestriction_bijective :
    Function.Bijective (elementaryRESReducedRestriction hcM hcN e c) :=
  (elementaryRESReducedRestrictionEquiv hcM hcN e c).bijective

/-! ## Elimination of real-definable Gamma names is invertible -/

section GroundTransferInverse
variable {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF] {B C : Base (M := Q)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → Q)),
  DefinableOverBase B sn A → DefinableOverBase C sn A)
variable (H' : ∀ {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → Q)),
  DefinableOverBase C sn A → DefinableOverBase B sn A)

theorem resGroundTransferReduced_objectClass {k : ℕ} (a : RESChart B k) :
    resGroundTransferReduced H (RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a)) =
      RESDimensionFreeReduction.fromOrdinary C (RESOrdinaryRing.objectClass (resGroundTransferObject H a)) := by
  change RESDimensionFreeReduction.fromOrdinary C (resGroundTransferOrdinary H (RESOrdinaryRing.objectClass a)) = _
  rw [resGroundTransferOrdinary_class]

theorem resGroundTransferReduced_comp_inverse :
    (resGroundTransferReduced H').comp (resGroundTransferReduced H) = RingHom.id _ := by
  apply reducedRESRing_hom_ext
  intro k a
  rw [RingHom.comp_apply,RingHom.id_apply,resGroundTransferReduced_objectClass,
    resGroundTransferReduced_objectClass]
  exact congrArg (RESDimensionFreeReduction.fromOrdinary B) (RESOrdinaryRing.objectClass_iso
    (RVForgetScissors.ofMap (resGroundTransferObject H' (resGroundTransferObject H a)).toChart a.toChart id
      (RVSharpCharts.identity_graph_definable B _ a.domain_definable) (Set.bijOn_id _)))

theorem eliminateRealGammaRES_bijective (B : Base (M := Q))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    Function.Bijective (eliminateRealGammaRES B hγ) :=
  (RingEquiv.ofRingHom (eliminateRealGammaRES B hγ)
    (resGroundTransferReduced (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mpr h))
    (resGroundTransferReduced_comp_inverse
      (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mpr h)
      (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mp h))
    (resGroundTransferReduced_comp_inverse
      (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mp h)
      (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mpr h))).bijective

end GroundTransferInverse

end DiamondIntegral.Section5

/-! ## The ambient comparison Θ is a ring isomorphism -/

namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance ambientIsoSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientIsoSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (hcN : CanonicalStructure.IsCanonical (M := N)) (e : Carrier ↪ₑ[LRV] N)

theorem coefficientGroundComparison_bijective (S : Set Carrier) (hS : S = {c | baseCarrier c}) :
    Function.Bijective (coefficientGroundComparison S hS) := by
  subst hS
  exact theta_5_14_concrete.bijective

theorem ambientRealPuiseuxComparison_bijective :
    Function.Bijective (ambientRealPuiseuxComparison hcN e) :=
  (coefficientGroundComparison_bijective _ laurentCoefficientEnumeration_range).comp
    (elementaryRESReducedRestriction_bijective canonicalInterpret_isCanonical hcN e
      laurentCoefficientEnumeration)

/-- Notation 5.14 for every elementary ambient model of the concrete
Puiseux model: the ambient Θ is bijective. -/
theorem ambientPuiseuxComparison_bijective (B : Base (M := N))
    (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    Function.Bijective (ambientPuiseuxComparison hcN e B hB hγ) := by
  obtain ⟨real,gamma⟩ := B
  change real = _ at hB
  subst hB
  exact (ambientRealPuiseuxComparison_bijective hcN e).comp (eliminateRealGammaRES_bijective _ hγ)

/-- The ambient Θ as a ring isomorphism. -/
def ambientPuiseuxComparisonEquiv (B : Base (M := N))
    (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    RESDimensionFreeReduction.Ring B ≃+* EquivariantVariety.ModifiedRing :=
  RingEquiv.ofBijective (ambientPuiseuxComparison hcN e B hB hγ)
    (ambientPuiseuxComparison_bijective hcN e B hB hγ)

theorem ambientPuiseuxComparisonEquiv_apply (B : Base (M := N))
    (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ)
    (x : RESDimensionFreeReduction.Ring B) :
    ambientPuiseuxComparisonEquiv hcN e B hB hγ x = ambientPuiseuxComparison hcN e B hB hγ x := rfl

end DiamondIntegral.Section5.PuiseuxOriginal
