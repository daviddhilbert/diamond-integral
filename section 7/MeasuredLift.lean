import «section 7».SpecialChainInduction

/-! Lemma 7.11 from the lift of any doubly bounded measured RV object.

`SpecialChainInduction.lemma_7_11` starts from the lift of a Section 4 chart.
The same argument applies to the lift `𝕃U` of any doubly bounded measured RV
object `U` of Section 6: `𝕃U` with its form is a chain set (`liftGood`), its
contraction is `U` (`contrLiftIso`), and so its class is `[U]` (`clsG_lift`).
Hence `lemma_7_11_measured`: along a relative aperture chain on `𝕃U`, the class
of the contraction `U_T` is reached from `[U]` by blowups. This avoids passing
through Lemma 6.33 (the chart of `U` and `U` have isomorphic lifts). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.MeasuredLift
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.SpecialChainStep DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.IsoOfMeasured
open DiamondIntegral.Section6.DiamondLift

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable (U : MeasuredRVObject (M := M) (T : Set M) (1 + k)) (hU : U.doublyBounded)

theorem mem_lift_iff (p : Mixed M (1 + k) U.object.arity) :
    p ∈ (rvLift U.object).carrier ↔
      ∃ h : p.2 ∈ U.object.domain.carrier, tupleRV M p.1 = U.object.value ⟨p.2, h⟩ := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hd : p.2 ∈ U.object.domain.carrier := hu ▸ u.property
    refine ⟨hd, ?_⟩
    have he : u = ⟨p.2, hd⟩ := Subtype.ext hu
    rw [← he, hv]
    rfl
  · rintro ⟨h, hv⟩
    refine ⟨⟨p.2, h⟩, rfl, ?_⟩
    rw [← hv]
    rfl

theorem lift_tagged : ∀ p ∈ (rvLift U.object).carrier, ∀ q ∈ (rvLift U.object).carrier,
    p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  obtain ⟨h1, e1⟩ := (mem_lift_iff U p).mp hp
  obtain ⟨h2, e2⟩ := (mem_lift_iff U q).mp hq
  rw [e1, e2]
  congr 1
  exact Subtype.ext he

include hU in
/-- The lift of a doubly bounded measured RV object, with its form, is a chain
set. -/
def liftGood : Good T (rvLift U.object) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      obtain ⟨hd, hv⟩ := (mem_lift_iff U p).mp hp
      apply (mem_lift_iff U q).mpr
      refine ⟨h2 ▸ hd, ?_⟩
      rw [← h1, hv]
      congr 1
      exact Subtype.ext h2
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := lift_fibre_finite U
  vfBounded := measuredRVLift_vfDoublyBounded _ hU
  rvBounded := by
    obtain ⟨β, hβ⟩ := hU.1
    refine ⟨β, fun p hp i => ?_⟩
    obtain ⟨u, hu, _⟩ := hp
    rw [← hu]
    exact hβ u.val u.property i
  form := liftForm U
  form_labels := fun p q he => congrArg U.form (Subtype.ext he)

theorem exists_lift_point (u : U.object.domain) :
    ∃ p ∈ (rvLift U.object).carrier, p.2 = u.val := by
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (U.object.value u)
  exact ⟨(x, u.val), (mem_lift_iff U _).mpr ⟨u.property, hx⟩, rfl⟩

/-- The contraction of the lift is the object itself. -/
def contrLiftIso : MeasuredRVIso (contr (liftGood U hU) (lift_tagged U)) U := by
  have hsub : (contr (liftGood U hU) (lift_tagged U)).object.domain.carrier ⊆ U.object.domain.carrier := by
    intro t ht
    obtain ⟨p, hp⟩ := pureRVTagQuotient_surjective _ (⟨t, ht⟩ : pureRVTagDomain (rvLift U.object))
    have he : p.val.2 = t := congrArg Subtype.val hp
    obtain ⟨h, _⟩ := (mem_lift_iff U p.val).mp p.property
    rw [← he]
    exact h
  let F := Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => Subtype.ext (congrArg (fun z : U.object.domain => z.val) he), fun b => ?_⟩
    obtain ⟨p, hp, he⟩ := exists_lift_point U b
    exact ⟨⟨b.val, he ▸ (pureRVTagQuotient _ ⟨p, hp⟩).property⟩, rfl⟩
  refine ⟨rvIsoOfFiniteFibres F hF (contr (liftGood U hU) (lift_tagged U)).finiteVolume
    U.finiteVolume (contr (liftGood U hU) (lift_tagged U)).nonzero U.nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ a
  unfold MeasuredRVObject.totalWeight
  have hv : (contr (liftGood U hU) (lift_tagged U)).object.value (pureRVTagQuotient _ p) =
      U.object.value (F (pureRVTagQuotient _ p)) := by
    change (preparedRVObject _ (lift_tagged U)).value _ = _
    rw [preparedRVObject_value]
    obtain ⟨h, e⟩ := (mem_lift_iff U p.val).mp p.property
    rw [e]
    rfl
  rw [volumeGamma_congr hv]
  congr 1
  rw [contractedMeasuredRVObject_form]
  rfl

include hU in
/-- The class of the lift is the class of the object. -/
theorem clsG_lift : clsG hc (liftGood U hU) = cls (objOf hc T U hU) := by
  unfold clsG
  apply cls_objOf_eq hc
  have e1 := contractionIso (lift_tagged U) (liftGood U hU).pullback (liftGood U hU).finite
    (liftGood U hU).vfBounded (liftGood U hU).form (liftGood U hU).form_labels
    (regularize_tagged _) (regularize_pullback _ (liftGood U hU).pullback)
    (regularize_finite _ (liftGood U hU).finite) (regularize_vfDoublyBounded _ (liftGood U hU).vfBounded)
    (regForm (liftGood U hU)) (regForm_labels _) (regularization _) (regularization_bijective _)
    (regularization_matching _ (lift_tagged U)) (fun _ => rfl) (fun p => regForm_apply (liftGood U hU) p)
  exact e1.symm.comp (contrLiftIso U hU)

include hU in
/-- Lemma 7.11 from the lift of a doubly bounded measured RV object `U`: along
a relative aperture chain on `𝕃U`, a chain set at the end carries the
transported form, and its class is reached from `[U]` by blowups. -/
theorem lemma_7_11_measured {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk (T : Set M) < κ) (h00 : M ⊨ Axioms.ACVF00) {s : ℕ}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)}
    {f : Map (rvLift U.object) B} (h : RelativeApertureChain (G := G) _ B f) :
    ∃ g' : Good T B, (∀ p, g'.form (f p) = liftForm U p) ∧
      ∃ m, BlowupSteps m (cls (objOf hc T U hU)) (clsG hc g') := by
  obtain ⟨g', hf, m, hm⟩ := relative_chain hc hκ hs hsmall h00 h (liftGood U hU)
  rw [clsG_lift hc U hU] at hm
  exact ⟨g', hf, m, hm⟩

end DiamondIntegral.Section7.MeasuredLift
