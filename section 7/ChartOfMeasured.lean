import «section 7».RealBase
import «section 7».LiftClasses
import «section 6».BoundedVariableUnaryMatching

/-! From Section 6's measured RV objects back to Section 4's charts.

A measured RV object `U` over the real parameters `S` (a definable domain of RV
tuples, a definable finite-to-one value map and a definable Gamma form) is read
as a chart over the base `⟨S, ∅⟩` with no Gamma names. Its measured object is
isomorphic to `U` (`measuredIso_chartOf`). When `U` is doubly bounded, the
chart is bounded and has no `∞` label. Consequently Section 7's lift
`liftCls` is surjective (Corollary 6.37 on Section 7's classes). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section6
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {k : ℕ}

theorem rv_preimage {n : ℕ} (A : Set (Fin n → CanonicalRV.RVSort M)) :
    (rawRVSpace (M := M) n).preimage A = rvValues '' A := by
  ext z
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨_, h, decode_rv ⟨z, hz⟩⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    have he : (rawRVSpace (M := M) n).decode ⟨rvValues t, ⟨t, rfl⟩⟩ = t :=
      rvValues_injective (decode_rv ⟨rvValues t, ⟨t, rfl⟩⟩)
    rw [he]
    exact ht

theorem decode_rvValues {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) (h : rvValues t ∈ (rawRVSpace (M := M) n).domain) :
    (rawRVSpace (M := M) n).decode ⟨rvValues t, h⟩ = t :=
  rvValues_injective (decode_rv ⟨rvValues t, h⟩)

/-- Measured objects with equal values have equal volume factors. -/
theorem volumeGamma_congr {n : ℕ} {U V : MeasuredRVObject (M := M) S n} {u : U.object.domain}
    {v : V.object.domain} (h : U.object.value u = V.object.value v) : U.volumeGamma u = V.volumeGamma v := by
  unfold MeasuredRVObject.volumeGamma
  generalize U.nonzero u = hu
  generalize V.nonzero v = hv
  revert hu hv
  rw [h]
  intro hu hv
  rfl

section Chart
variable (U : MeasuredRVObject (M := M) S k)

/-- The raw domain of `U`. -/
def rawDom : Set (Fin U.object.arity → M) := rvValues '' U.object.domain.carrier

theorem rawDom_sorted : ∀ x ∈ rawDom U, ∀ i, sortEval SortTag.rv (x i) := by
  rintro _ ⟨t, _, rfl⟩ i
  exact (t i).property

include hc in
theorem rawDom_definable :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin U.object.arity => .rv) (rawDom U) :=
  real_base hc (by rw [rawDom, ← rv_preimage]; exact U.object.domain.definable) (rawDom_sorted U)

/-- The domain point over a raw point. -/
def pt {w : Fin U.object.arity → M} (hw : w ∈ rawDom U) : U.object.domain := ⟨hw.choose, hw.choose_spec.1⟩

theorem pt_val {w : Fin U.object.arity → M} (hw : w ∈ rawDom U) : rvValues (pt U hw).val = w := hw.choose_spec.2

theorem pt_of (t : U.object.domain) (hw : rvValues t.val ∈ rawDom U) : pt U hw = t :=
  Subtype.ext (rvValues_injective (pt_val U hw))

/-- The raw value map. -/
def rawCoord (w : Fin U.object.arity → M) : Fin k → M :=
  if hw : w ∈ rawDom U then rvValues (U.object.value (pt U hw)) else fun _ => iRVOne

/-- The raw form. -/
def rawVol (w : Fin U.object.arity → M) : Values.Gamma (M := M) :=
  if hw : w ∈ rawDom U then gammaMapValue U.form (pt U hw) else 1

theorem mem_rawDom (t : U.object.domain) : rvValues t.val ∈ rawDom U := ⟨t.val, t.property, rfl⟩

theorem rawCoord_of (t : U.object.domain) : rawCoord U (rvValues t.val) = rvValues (U.object.value t) := by
  rw [rawCoord, dif_pos (mem_rawDom U t), pt_of U t]

theorem rawVol_of (t : U.object.domain) : rawVol U (rvValues t.val) = gammaMapValue U.form t := by
  rw [rawVol, dif_pos (mem_rawDom U t), pt_of U t]

include hc in
theorem rawCoord_graph :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (k + U.object.arity) => .rv)
      (graphOn (rawDom U) (rawCoord U)) := by
  let n := U.object.arity
  let ρ : Fin n ⊕ Fin k → Fin (k + n) := Sum.elim (headIndex k n) (tailIndex k n)
  have hrel := U.object.volume.graph_definable
  have hpre : S.Definable LRV ((fun w : Fin (k + n) → M => w ∘ ρ) ⁻¹'
      ((rawRVSpace (M := M) n).relation (rawRVSpace (M := M) k)
        (fun x y => ∃ a : U.object.domain, a.val = x ∧ (U.object.volume a).val = y))) :=
    hrel.preimage_comp ρ
  have hhead : ∀ w : Fin (k + n) → M, (w ∘ ρ) ∘ Sum.inl = w ∘ headIndex k n := fun _ => rfl
  have htail : ∀ w : Fin (k + n) → M, (w ∘ ρ) ∘ Sum.inr = w ∘ tailIndex k n := fun _ => rfl
  have he : graphOn (rawDom U) (rawCoord U) = (fun w : Fin (k + n) → M => w ∘ ρ) ⁻¹'
      ((rawRVSpace (M := M) n).relation (rawRVSpace (M := M) k)
        (fun x y => ∃ a : U.object.domain, a.val = x ∧ (U.object.volume a).val = y)) := by
    ext w
    constructor
    · rintro ⟨hd, hv⟩
      obtain ⟨t, ht, hw⟩ := hd
      let a : U.object.domain := ⟨t, ht⟩
      have hx : (w ∘ ρ) ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain := by
        rw [hhead, ← hw]
        exact ⟨t, rfl⟩
      have hval : w ∘ tailIndex k n = rvValues (U.object.value a) := by
        rw [← hv, ← hw]
        exact rawCoord_of U a
      have hy : (w ∘ ρ) ∘ Sum.inr ∈ (rawRVSpace (M := M) k).domain := by
        rw [htail, hval]
        exact ⟨_, rfl⟩
      refine ⟨hx, hy, a, ?_, ?_⟩
      · apply rvValues_injective
        rw [decode_rv]
        change rvValues t = (w ∘ ρ) ∘ Sum.inl
        rw [hhead, hw]
      · apply rvValues_injective
        rw [decode_rv]
        change rvValues (U.object.value a) = (w ∘ ρ) ∘ Sum.inr
        rw [htail, hval]
    · rintro ⟨hx, hy, a, ha, hb⟩
      have h1 : w ∘ headIndex k n = rvValues a.val := by
        rw [ha, decode_rv]
        rfl
      have h2 : w ∘ tailIndex k n = rvValues (U.object.value a) := by
        change w ∘ tailIndex k n = rvValues (U.object.volume a).val
        rw [hb, decode_rv]
        rfl
      refine ⟨?_, ?_⟩
      · rw [h1]
        exact mem_rawDom U a
      · rw [h1, h2]
        exact rawCoord_of U a
  rw [he]
  refine real_base hc hpre ?_
  intro w hw i
  rcases StrictCharts.block_cases k n i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · obtain ⟨hx, _, _⟩ := hw
    obtain ⟨t, ht⟩ := hx
    have := congrFun ht i'
    change (t i').val = w (headIndex k n i') at this
    rw [← this]
    exact (t i').property
  · obtain ⟨_, hy, _⟩ := hw
    obtain ⟨t, ht⟩ := hy
    have := congrFun ht i'
    change (t i').val = w (tailIndex k n i') at this
    rw [← this]
    exact (t i').property

include hc in
theorem rawVol_graph :
    RVVolumeMaps.VolumeDefinable (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (rawDom U) (rawVol U) := by
  let n := U.object.arity
  let ρ : Fin n ⊕ Fin 1 → Fin (n + 1) := Sum.elim Fin.succ (fun _ => 0)
  have hrel := U.form.graph_definable
  have hpre := hrel.preimage_comp ρ
  have he : RVVolumeMaps.volumeGraph (rawDom U) (rawVol U) = (fun w : Fin (n + 1) → M => w ∘ ρ) ⁻¹'
      ((rawRVSpace (M := M) n).relation (rawGammaPresentation (M := M))
        (fun x y => ∃ a : U.object.domain, a.val = x ∧ (U.form a).val = y)) := by
    ext w
    have hhead : (w ∘ ρ) ∘ Sum.inl = Fin.tail w := rfl
    have htail : (w ∘ ρ) ∘ Sum.inr = fun _ => w 0 := rfl
    constructor
    · rintro ⟨hd, hnz, hv⟩
      obtain ⟨t, ht, hw⟩ := hd
      let a : U.object.domain := ⟨t, ht⟩
      have hx : (w ∘ ρ) ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain := by
        rw [hhead, ← hw]
        exact ⟨t, rfl⟩
      have hy : (w ∘ ρ) ∘ Sum.inr ∈ (rawGammaPresentation (M := M)).domain := by
        rw [htail]
        exact hnz
      refine ⟨hx, hy, a, ?_, ?_⟩
      · apply rvValues_injective
        rw [decode_rv]
        change rvValues t = (w ∘ ρ) ∘ Sum.inl
        rw [hhead, hw]
      · change (U.form a).val = codeValue (((w ∘ ρ) ∘ Sum.inr) 0)
        rw [htail]
        change gammaMapValue U.form a = codeValue (w 0)
        rw [hv, ← hw]
        exact (rawVol_of U a).symm
    · rintro ⟨hx, hy, a, ha, hb⟩
      have h1 : Fin.tail w = rvValues a.val := by
        rw [← hhead, ha, decode_rv]
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]
        exact mem_rawDom U a
      · have := hy
        rw [htail] at this
        exact this
      · rw [h1, rawVol_of]
        exact hb.symm
  unfold RVVolumeMaps.VolumeDefinable
  rw [he]
  refine real_base hc hpre ?_
  intro w hw i
  refine Fin.cases ?_ (fun i' => ?_) i
  · exact hw.2.1.1
  · obtain ⟨hx, _, _⟩ := hw
    obtain ⟨t, ht⟩ := hx
    have := congrFun ht i'
    change (t i').val = w i'.succ at this
    rw [← this]
    exact (t i').property

/-- The chart of a measured RV object over `⟨S, ∅⟩`. -/
def chartOf : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k where
  arity := U.object.arity
  domain := rawDom U
  domain_definable := rawDom_definable hc U
  coordinate := rawCoord U
  coordinate_definable := rawCoord_graph hc U
  coordinate_proper := by
    rintro _ ⟨t, ht, rfl⟩ i
    let a : U.object.domain := ⟨t, ht⟩
    rw [rawCoord_of U a]
    exact ⟨(U.object.value a i).property, U.nonzero a i⟩
  finite_fibres := by
    intro t
    by_cases ht : ∃ t' : Fin k → CanonicalRV.RVSort M, rvValues t' = t
    · obtain ⟨t', rfl⟩ := ht
      have hF := U.finiteVolume ⟨t', Set.mem_univ _⟩
      apply (hF.image (fun a => rvValues a.val)).subset
      rintro w ⟨⟨s, hs, rfl⟩, hw⟩
      refine ⟨⟨s, hs⟩, ?_, rfl⟩
      apply Subtype.ext
      apply rvValues_injective
      change rvValues (U.object.value ⟨s, hs⟩) = rvValues t'
      rw [← rawCoord_of U ⟨s, hs⟩]
      exact hw
    · apply Set.Finite.subset Set.finite_empty
      rintro w ⟨⟨s, hs, rfl⟩, hw⟩
      exact ht ⟨_, (rawCoord_of U ⟨s, hs⟩).symm.trans hw⟩
  volume := rawVol U
  volume_definable := rawVol_graph hc U

/-- The measured object of `chartOf U` is isomorphic to `U`. -/
def measuredIso_chartOf : MeasuredRVIso (toMeasured hc (chartOf hc U)) U := by
  have hsub : (toMeasured hc (chartOf hc U)).object.domain.carrier ⊆ U.object.domain.carrier := by
    intro a ha
    obtain ⟨t, ht, he⟩ := (ha : rvValues a ∈ rawDom U)
    rw [← rvValues_injective he]
    exact ht
  let F : Map (toMeasured hc (chartOf hc U)).object.domain U.object.domain := Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => ?_, fun b => ?_⟩
    · have h := congrArg (fun x : U.object.domain => x.val) he
      exact Subtype.ext h
    exact ⟨⟨b.val, (mem_rawDom U b : rvValues b.val ∈ rawDom U)⟩, rfl⟩
  refine ⟨rvIsoOfFiniteFibres F hF (toMeasured hc (chartOf hc U)).finiteVolume U.finiteVolume
    (toMeasured hc (chartOf hc U)).nonzero U.nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  unfold MeasuredRVObject.totalWeight
  have hv : (toMeasured hc (chartOf hc U)).object.value a = U.object.value (F a) := by
    apply rvValues_injective
    change rawCoord U (rvValues a.val) = _
    exact rawCoord_of U (F a)
  rw [volumeGamma_congr hv]
  congr 1
  change rawVol U (rvValues a.val) = _
  exact rawVol_of U (F a)

end Chart

section Bounds
variable (U : MeasuredRVObject (M := M) S k) (hU : U.doublyBounded)

include hU in
theorem chartOf_noInfinity : MeasuredRVBounds.NoInfinity (chartOf hc U) := by
  rintro _ ⟨t, ht, rfl⟩ i
  exact ⟨(t i).property, fun he => hU.1.nonzero t ht i (Subtype.ext he)⟩

include hU in
theorem chartOf_bounded : RVMeasuredBounds.DomainBounded (chartOf hc U) := by
  obtain ⟨β, hβ⟩ := hU.1
  refine ⟨β, ?_⟩
  rintro _ ⟨t, ht, rfl⟩ i hi
  have hne : t i ≠ DiamondIntegral.Section2.rvZero M := fun he => hi.2 (congrArg Subtype.val he)
  have hv := DiamondIntegral.Section2.nonzero_rv_codeValue_val (t i) hne
  obtain ⟨h1, h2⟩ := hβ t ht i
  refine ⟨?_, ?_⟩
  · show (β⁻¹).val ≤ (codeValue (t i).val).val
    rw [hv]
    exact h1
  · show (codeValue (t i).val).val ≤ β.val
    rw [hv]
    exact h2

end Bounds

/-! ### Surjectivity of the lift on Section 7's classes -/

section Surjective
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.StrictCharts
open DiamondIntegral.Section6.DiamondLiftHomomorphism DiamondIntegral.Section6.DiamondGrothendieck
open DiamondIntegral.Section6.DiamondSurjectivity DiamondIntegral.Section6.DiamondLift
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (DiamondIntegral.Section2.VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : DiamondIntegral.Section2.ParameterBase M))
  (hv : ∀ x y : DiamondIntegral.Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (B₀ : DiamondIntegral.Section2.VFGeneratedFieldBase T) (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- The bounded chart of a doubly bounded measured RV object over `T`. -/
def objOf (U : MeasuredRVObject (M := M) (T : Set M) k) (hU : U.doublyBounded) : Obj (BT T) k :=
  ⟨chartOf hc U, chartOf_bounded hc U hU⟩

theorem positiveClass_objOf (U : MeasuredRVObject (M := M) (T : Set M) k) (hU : U.doublyBounded) :
    DiamondIntegral.Section3.positiveClass (rvPresentation (T : Set M) k)
        (dbObj hc h00 hκ hs T hsmall hΓ (objOf hc T U hU)) =
      DiamondIntegral.Section3.positiveClass _ ⟨U, hU⟩ := by
  have h1 := positiveClass_dbOf_eq hc h00 hκ hs T hsmall hΓ
    (strictChart_bounded h00 (chartOf hc U) (chartOf_bounded hc U hU))
    (fun x hx i => strictChart_infinityFree h00 (chartOf hc U) x hx i)
    (chartOf_bounded hc U hU) (chartOf_noInfinity hc U hU)
    ⟨RVMeasuredIsomorphisms.symm (strictIso h00 (chartOf hc U))⟩
  refine h1.trans ?_
  exact DiamondIntegral.Section3.positiveClass_iso _ ⟨measuredIso_chartOf hc U⟩

theorem liftCls_objOf (U : MeasuredRVObject (M := M) (T : Set M) k) (hU : U.doublyBounded) :
    liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls (objOf hc T U hU)) =
      vfClass G hc (liftObject U (measuredRVLift_properInvariant h00 hc hκ hs hv U hU)) := by
  change liftHom k G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt (rvCls hc h00 hκ hs T hsmall hΓ (cls _)) = _
  rw [rvCls_cls, positiveClass_objOf hc h00 hκ hs T hsmall hΓ U hU]
  exact liftHom_class (G := G) (k := k) h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt ⟨U, hU⟩

/-- Corollary 6.37 on Section 7's classes: `μ𝕃 : Cls → K₊ μVF^◇[k]` is
surjective. -/
theorem liftCls_surjective :
    Function.Surjective (liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt) := by
  have hgen : ∀ A : DiamondIntegral.Section6.DiamondCategory.VFObject (M := M) (T : Set M) k,
      vfClass G hc A ∈ AddMonoidHom.mrange (liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt) := by
    intro A
    by_cases hk : k = 0
    · subst hk
      obtain ⟨U, hU, hiso⟩ := exists_isomorphic_lift_zero (G := G) h00 hc lin hκ hs hv hsmall hΓ A
      exact ⟨_, (liftCls_objOf hc h00 hκ hs T hsmall hΓ hv B₀ hnt U hU).trans (vfClass_iso hc hiso).symm⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      obtain ⟨U, hU, hiso⟩ := exists_isomorphic_lift (G := G) h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt A
      exact ⟨_, (liftCls_objOf hc h00 hκ hs T hsmall hΓ hv B₀ hnt U hU).trans (vfClass_iso hc hiso).symm⟩
  intro x
  obtain ⟨f, rfl⟩ := AddCon.mk'_surjective x
  change (PositiveAdditiveGrothendieck.congruence (presentation G hc k)).mk' f ∈
    AddMonoidHom.mrange (liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt)
  refine Finsupp.induction f ?_ ?_
  · rw [map_zero]
    exact zero_mem _
  · intro a b f _ _ ih
    rw [map_add]
    refine add_mem ?_ ih
    rw [← Finsupp.smul_single_one, map_nsmul]
    exact nsmul_mem (hgen a) b

end Surjective

end DiamondIntegral.Section7.ChartOfMeasured
