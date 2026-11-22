import «section 8».MilnorFiber
import «section 7».Corollary727Rings

/-! Remark 8.14 (`rem-comp-milnor-fib`): `Θ 𝔼^◇ ∫^◇ = Vol` on `K μVF^◇[*]`.

`Vol = Θ ∘ E_b ∘ ∫` is Notation 5.15's volume over the context base `⟨T, Γ⟩`
(`puiseuxBoundedVFVolume`), with `∫` Section 3's integral of the underlying VF object. By
Corollary 7.27 (left square), `∫ ∘ forget = (forget, base change) ∘ ∫^◇`, so it suffices to show
`Θ ∘ E_b ∘ (forget, base change) = Θ ∘ 𝔼^◇` on `K μRV^db[*]` (`theta_bounded_forget`). Both are
ring maps; on a product generator `[g♯ × V]` both sides are `χ(I) [G_m]^ℓ Θ([V])`:

* `integrateAll_base`: the iterated Euler integral does not depend on the base over which the family
  is definable (the fibre functions are determined by their values);
* `integrateAll_bounded_comparison` (library): on a bounded family `χ_b = χ_g`;
* `theta_res_ext`: `Θ` over `⟨T, Γ⟩` of the base extension of an RES class is `Θ` over `⟨T, ∅⟩` of the
  class (both eliminate the Γ names to the same chart).

Headline: `remark_8_14` and, for the Milnor fiber, `remark_8_14_milnor`:
`𝒮_f = Θ 𝔼^◇ ∫^◇ [𝒳_f] = Vol([𝒳_f])`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section8.VolComparison

open DiamondIntegral.Section4 DiamondIntegral.Section4.GammaWeightedFamilies
open DiamondIntegral.Section4.GammaFamilyIntegration DiamondIntegral.Section4.GammaIntegerFamilies

/-! ### The iterated Euler integral does not depend on the base -/

section Base

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integralFirst_base (h00 : M ⊨ Axioms.ACVF00) (B B' : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (hf' : IntegerFamilyDefinable B' f) (y : Fin n → Values.Gamma (M := M)) :
    integralFirst h00 B k f hf y = integralFirst h00 B' k f hf' y := by
  unfold integralFirst
  congr 1

theorem integrateAll_base (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B B' : Base (M := M)) (hr : Cardinal.mk B.real < κ)
    (hγ : Cardinal.mk B.gamma < κ) (hr' : Cardinal.mk B'.real < κ) (hγ' : Cardinal.mk B'.gamma < κ)
    (k : EulerKind) (n : ℕ) (f : familySubgroup B n) (f' : familySubgroup B' n) (h : f.val = f'.val) :
    GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n f =
      GammaIteratedIntegral.integrateAll h00 hκ hs B' hr' hγ' k n f' := by
  induction n with
  | zero =>
    change f.val GammaIteratedIntegral.emptyTuple = f'.val GammaIteratedIntegral.emptyTuple
    rw [h]
  | succ n ih =>
    obtain ⟨fv, hfv⟩ := f
    obtain ⟨fv', hfv'⟩ := f'
    change fv = fv' at h
    subst h
    refine ih _ _ ?_
    funext y
    exact integralFirst_base h00 B B' k fv hfv hfv' y

end Base

/-! ### `Θ ∘ E_b ∘ (forget, base change) = Θ ∘ 𝔼^◇` on `K μRV^db[*]` -/

section Puiseux

open DiamondIntegral.Section3 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.Hm
open DiamondIntegral.Section7.Corollary727 DiamondIntegral.Section7.BaseExtension
open RVMeasuredCharts

variable (P : PuiseuxAmbient)

/-- `Θ` over the context base `⟨T, Γ⟩`. -/
abbrev thetaG : RESDimensionFreeReduction.Ring P.G.base →+* EquivariantVariety.ModifiedRing :=
  ambientPuiseuxComparison P.hc P.e P.G.base P.hB P.hγ

/-- `E_b` on `K RV[*]/(P − 1)` over `⟨T, Γ⟩`. -/
abbrev Eb : RVOrdinaryPNormalization.Ring P.G.base →+* RESDimensionFreeReduction.Ring P.G.base :=
  RVT001OrdinaryNormalization.bounded P.G.model00 Section5.GammaQE.gamma_piecewise_rational_affine
    P.G.uncountable.le P.G.saturated P.G.base P.G.small_real P.G.small_gamma P.G.nontrivial_definable_gamma
    (Section3T001Integration.ordinary (hc := P.hc) P.G.uncountable.le P.G.saturated P.G.model00
      P.G.small_real P.G.small_gamma P.G.nontrivial_definable_gamma)

/-- `Vol = Θ ∘ E_b ∘ ∫` (Notation 5.15). -/
theorem vol_eq : puiseuxBoundedVFVolume P =
    (thetaG P).comp ((Eb P).comp (nativeVFChartIntegral (completed18GroundLiftInput P.G P.hc))) := rfl

theorem Eb_quotient (y : RVOrdinaryRing.Ring P.G.base) :
    Eb P (RVOrdinaryPNormalization.quotient P.G.base y) =
      nativeRVEvaluation P.G.model00 Section5.GammaQE.gamma_piecewise_rational_affine P.G.uncountable.le
        P.G.saturated P.hc P.G.base P.G.small_real P.G.small_gamma P.G.nontrivial_definable_gamma
        EulerKind.bounded y := rfl

variable {ℓ r : ℕ} (g : GammaBoundedRVCharts.BoundedChart (base P) ℓ) (V : RESChart (base P) r)

/-- The support of `g` over the context base. -/
abbrev gExt : GammaOrdinaryCharts.Chart P.G.base ℓ := ⟨g.support, transfer P.G g.support_definable⟩

theorem Eb_sharp :
    Eb P (forgetNormalized P.G (RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp g))) =
      (GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated P.G.base
          P.G.small_real P.G.small_gamma EulerKind.bounded ℓ
          (GammaIndicators.indicatorFamily P.G.base g.support (transfer P.G g.support_definable)) :
            RESDimensionFreeReduction.Ring P.G.base) * nativeTorusClass P.G.base ^ ℓ := by
  change Eb P (RVOrdinaryPNormalization.quotient _ (ordinaryExt (transfer P.G)
    (RVOrdinaryMaps.boundedForget _ (RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp g))))) = _
  rw [RVOrdinaryMaps.boundedForget_class, ordinaryExt_class, Eb_quotient]
  have F : RVUnderlyingIsomorphisms.Iso (chartExt (transfer P.G) (GammaBoundedRVCharts.sharp g).toChart)
      (GammaOrdinaryCharts.sharpChart (gExt P g)) :=
    RVUnderlyingIsomorphisms.ofMap _ _ (fun u => u ∘ id)
      (RVCoordinateMaps.coordinate_graph_definable P.G.base _
        (chartExt (transfer P.G) (GammaBoundedRVCharts.sharp g).toChart).domain_definable id)
      ⟨fun u hu => hu, fun u _ v _ h => h, fun u hu => ⟨u, hu, rfl⟩⟩
  rw [nativeRVEvaluation_underlyingIso _ _ _ _ _ _ _ _ _ _ _ _ F, ← GammaOrdinarySharpRingMap.sharp_class,
    nativeRVEvaluation_gamma]

/-- The base extension of an RES chart. -/
abbrev resExt : RESChart P.G.base r := ⟨chartExt (transfer P.G) V.toChart, V.finite_values⟩

theorem Eb_res :
    Eb P (forgetNormalized P.G (RVBoundedRing.objectClass (RVBoundedCharts.ofRES V))) =
      nativeRESChartClass (resExt P V) := by
  change Eb P (RVOrdinaryPNormalization.quotient _ (ordinaryExt (transfer P.G)
    (RVOrdinaryMaps.boundedForget _ (RVBoundedRing.objectClass (RVBoundedCharts.ofRES V))))) = _
  rw [RVOrdinaryMaps.boundedForget_class, ordinaryExt_class, Eb_quotient]
  change nativeRVEvaluation _ _ _ _ _ _ _ _ _ _ (RVOrdinaryRing.objectClass (resExt P V).toChart) = _
  rw [← RVOrdinaryMaps.ofRES_class, nativeRVEvaluation_res]
  rfl

/-- `Θ` of the base extension of an RES class is `Θ` of the class. -/
theorem theta_res_ext : thetaG P (nativeRESChartClass (resExt P V)) = theta P (nativeRESChartClass V) := by
  change ambientPuiseuxComparison P.hc P.e P.G.base P.hB P.hγ
      (RESDimensionFreeReduction.fromOrdinary _ (RESOrdinaryRing.objectClass (resExt P V))) =
    ambientPuiseuxComparison P.hc P.e (base P) P.hB (fun _ h => absurd h (Set.notMem_empty _))
      (RESDimensionFreeReduction.fromOrdinary _ (RESOrdinaryRing.objectClass V))
  unfold ambientPuiseuxComparison
  simp only [RingHom.comp_apply]
  unfold eliminateRealGammaRES
  rw [resGroundTransferReduced_objectClass
      (fun sn A h => (realGammaGround_definable_iff P.G.base P.hγ sn A).mp h),
    resGroundTransferReduced_objectClass
      (fun sn A h => (realGammaGround_definable_iff (base P) (fun _ h => absurd h (Set.notMem_empty _)) sn A).mp h)]
  rfl

/-- `χ_b` over `⟨T, Γ⟩` of the support of `g` is Section 8's `χ` over `⟨T, ∅⟩`. -/
theorem integrateAll_ext :
    GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated P.G.base
        P.G.small_real P.G.small_gamma EulerKind.bounded ℓ
        (GammaIndicators.indicatorFamily P.G.base g.support (transfer P.G g.support_definable)) =
      chi P g.support g.support_definable := by
  obtain ⟨β, hβ⟩ := g.domain_bounded
  have hbox : GammaBoundedFamilies.BoxSupported β⁻¹ β
      (GammaIndicators.indicatorFamily P.G.base g.support (transfer P.G g.support_definable)).val := by
    intro z hz i
    have hzI : z ∈ g.support := by
      by_contra h
      exact hz (by simp [GammaIndicators.indicatorFamily, h])
    exact hβ z hzI i
  rw [GammaBoundedFamilies.integrateAll_bounded_comparison P.G.model00 P.G.uncountable.le P.G.saturated
    P.G.base P.G.small_real P.G.small_gamma EulerKind.bounded EulerKind.geometric ℓ _ β⁻¹ β hbox]
  exact integrateAll_base P.G.model00 P.G.uncountable.le P.G.saturated P.G.base (base P) P.G.small_real
    P.G.small_gamma P.G.small_real _ EulerKind.geometric ℓ _ _ rfl

theorem thetaG_torus : thetaG P (nativeTorusClass P.G.base) = modifiedTorusClass :=
  ambientPuiseuxComparison_nativeTorusClass P.hc P.e P.G.base P.hB P.hγ

theorem theta_torus : theta P (nativeTorusClass (base P)) = modifiedTorusClass :=
  ambientPuiseuxComparison_nativeTorusClass P.hc P.e (base P) P.hB _

theorem theta_Eb_prod :
    thetaG P (Eb P (forgetNormalized P.G (RVBoundedRing.objectClass (prodChart P g V)))) =
      theta P (Ediamond P (RVBoundedRing.objectClass (prodChart P g V))) := by
  rw [RVBoundedRing.objectClass_product, map_mul, map_mul, map_mul, Eb_sharp, Eb_res, map_mul, map_mul,
    Ediamond_sharp, Ediamond_res, map_mul, map_intCast, map_pow, map_mul, map_intCast, map_pow,
    integrateAll_ext, theta_res_ext, thetaG_torus, theta_torus]

/-- **`Θ ∘ E_b ∘ (forget, base change) = Θ ∘ 𝔼^◇` on `K μRV^db[*]`.** -/
theorem theta_bounded_forget (x : RVBoundedRing.Ring (base P)) :
    thetaG P (Eb P (forgetNormalized P.G x)) = theta P (Ediamond P x) := by
  have hobj : ∀ {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k),
      thetaG P (Eb P (forgetNormalized P.G (RVBoundedRing.objectClass a))) =
        theta P (Ediamond P (RVBoundedRing.objectClass a)) := by
    intro k a
    have h := RVBoundedDecomposition.bounded_value P.hc P.G.model00 P.G.uncountable.le P.G.saturated
      P.G.small_real (hγ0 P) (base_nontrivial P) (RVBoundedDecomposition.ringValue (base P)) a
    suffices H : ∀ y ∈ AddSubmonoid.closure (RVBoundedDecomposition.ringValue (base P)).products,
        thetaG P (Eb P (forgetNormalized P.G y)) = theta P (Ediamond P y) from H _ h
    intro y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem y hy =>
      obtain ⟨r, l, V, g, rfl⟩ := hy
      exact theta_Eb_prod P g V
    | zero => simp only [map_zero]
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
  induction mem_closure_objectClass P x using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, a, rfl⟩ := hx
    exact hobj a
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | neg x _ hx => simp only [map_neg, hx]

end Puiseux

/-! ### Remark 8.14 -/

section Final

open SpecialTransformations.Section9 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2 DiamondIntegral.Section6 DiamondIntegral.Section7
open DiamondIntegral.Section3 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.Hm DiamondIntegral.Section8.Milnor
open DiamondIntegral.Section7.Corollary727 DiamondIntegral.Section7.Corollary727Rings
open DiamondIntegral.Section7.Theorem726 DiamondIntegral.Section7.DiamondRing
open DiamondIntegral.Section6.DiamondCategory RationalSeries

variable (P : PuiseuxAmbient)
variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hntB : ∃ x : P.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- **Remark 8.14 (`rem-comp-milnor-fib`).** For every object `A` of `μVF^◇[k]` over the base of
Section 8, `Θ 𝔼^◇ ∫^◇ [A] = Vol([A])`, where `Vol = Θ ∘ E_b ∘ ∫` is Notation 5.15's volume of the
underlying VF object over the context base. -/
theorem remark_8_14 {k : ℕ} (A : DiamondCategory.VFObject (M := P.N) (P.G.real : Set P.N) k) :
    theta P (EdiamondQ P (theorem_7_26_graded Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real
        P.G.small_real (base_nontrivial P) P.G.fieldBase hntB
        (ringClass Gv P.hc (unitObj Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv
          P.G.real P.G.small_real (base_nontrivial P)) A))) =
      puiseuxBoundedVFVolume P
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF P.hc P.G A))) := by
  rw [vol_eq, RingHom.comp_apply, RingHom.comp_apply,
    left_object Gv P.G P.hc hv (base_nontrivial P) P.G.fieldBase hntB (completed18GroundLiftInput P.G P.hc) A]
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (intD Gv P.G P.hc hv (base_nontrivial P) P.G.fieldBase hntB
    (ringClass Gv P.hc (one Gv P.G P.hc hv (base_nontrivial P)) A))
  have hg : theorem_7_26_graded Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv P.G.real
      P.G.small_real (base_nontrivial P) P.G.fieldBase hntB
      (ringClass Gv P.hc (unitObj Gv P.G.model00 P.hc P.G.uncountable P.G.saturated hv
        P.G.real P.G.small_real (base_nontrivial P)) A) = RelativeAnnularQuotient.quotient (base P) x := by
    change Ideal.quotEquivOfEq (RelativeAnnularConverse.ideal_eq_manuscriptIdeal (B := base P)).symm
      (intD Gv P.G P.hc hv (base_nontrivial P) P.G.fieldBase hntB
      (ringClass Gv P.hc (one Gv P.G P.hc hv (base_nontrivial P)) A)) = _
    rw [← hx, Ideal.quotEquivOfEq_mk]
    rfl
  rw [hg, ← Ediamond_eq, ← hx]
  change _ = thetaG P (Eb P (forgetNormalized P.G x))
  exact (theta_bounded_forget P x).symm

/-- **Remark 8.14 for the Milnor fiber.** `𝒮_f = Θ 𝔼^◇ ∫^◇ [𝒳_f] = Vol([𝒳_f])`. -/
theorem remark_8_14_milnor {d : ℕ} (f : MvPolynomial (Fin d) ℂ) :
    milnorClass P Gv hv hntB f =
      puiseuxBoundedVFVolume P
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF P.hc P.G (milnorObject P f)))) :=
  remark_8_14 P Gv hv hntB (milnorObject P f)

/-- **The motivic Milnor fiber as a volume.** `Z_f ∈ R[T]†` and
`−lim_{T → ∞} Z_f(T) = Vol([𝒳_f])`. -/
theorem milnor_fiber_vol {d : ℕ} (f : MvPolynomial (Fin d) ℂ) :
    HasLimit Lunit (milnorZeta P Gv hv hntB f)
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc (puiseuxBoundedVFVolume P
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF P.hc P.G (milnorObject P f))))))) := by
  rw [← remark_8_14_milnor]
  exact theorem_8_11_milnor P Gv hv hntB f

end Final

end DiamondIntegral.Section8.VolComparison
