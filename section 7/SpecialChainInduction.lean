import «section 7».SpecialChainRel
import «section 6».ScalarApertureInclusion
import «section 6».UnaryApertureInclusion
import «section 7».BlowupCongruence
import HilbertMathlib.Foundation.Rewriting.Iteration

/-! Lemma 7.11 (`special:to:blowup:coa`) for chains.

Along a special covariant chain or a relative aperture chain, a chain set and
its transported form give a chain set at the end, whose class is reached from
the class of the start by blowups (`relative_chain`, `unary_chain`):
* identity, regularization and zero-centred steps keep the class
  (`clsG_reg`, `clsG_zc`);
* centripetal and relative steps are blowups of length one (`step_rel`; an
  original centripetal step is relative data with the same point map,
  `CentripetalData.relativeData`, and so is a unary relative step,
  `UnaryRelativeApertureData.exists_relativeData`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {r : ℕ}

/-! ### Transport of chain sets along equalities -/

section Transport
variable {T : LRV.Substructure M} {n : ℕ} {X X' : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}

/-- A chain set transported along an equality of sets. -/
def transport (h : X = X') (g : Good T X) : Good T X' := h ▸ g

theorem transport_form (h : X = X') (g : Good T X) (p : X) :
    (transport h g).form ⟨p.val, h ▸ p.property⟩ = g.form p := by
  subst h
  rfl

theorem clsG_transport (hc : CanonicalStructure.IsCanonical (M := M)) (h : X = X') (g : Good T X) :
    clsG hc (transport h g) = clsG hc g := by
  subst h
  rfl

end Transport

/-! ### Induction along chains -/

section Induction
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
variable (h00 : M ⊨ Axioms.ACVF00)

/-- The conclusion of Lemma 7.11 along a map `f : A → B`: every chain set
structure on `A` transports to one on `B` whose class is a blowup of the class
on `A`. -/
def Claim {s : ℕ} (A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M))
    (B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)) (f : Map A B) : Prop :=
  ∀ g : Good T A, ∃ g' : Good T B, (∀ p : A, g'.form (f p) = g.form p) ∧
    ∃ m, BlowupSteps m (clsG hc g) (clsG hc g')

theorem claim_comp {s t : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)}
    {C : DefSet (rawMixedSpace (M := M) (1 + k) t) (T : Set M)} {f : Map A B} {g : Map B C}
    (hf : Claim hc A B f) (hg : Claim hc B C g) : Claim hc A C (g.comp f) := by
  intro g0
  obtain ⟨g1, hf1, m1, hs1⟩ := hf g0
  obtain ⟨g2, hf2, m2, hs2⟩ := hg g1
  exact ⟨g2, fun p => (hf2 (f p)).trans (hf1 p), m1 + m2, hs1.trans hs2⟩

include hκ hs hsmall h00

/-- A relative step. -/
theorem claim_relative {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    (D : DiamondIntegral.Section6.RelativeApertureData (G := G) A) :
    Claim hc A D.map.image D.bijection := by
  intro g
  exact ⟨imageGood hc g D hκ hs hsmall h00, fun p => imageGood_form hc g D hκ hs hsmall h00 p, 1,
    Steps.single (step_rel hc g D hκ hs hsmall h00)⟩

/-- A step given by relative data with the same point map. -/
theorem claim_of_point {s : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)} (f : Map A B) (hs1 : s = 1 + r)
    (D : DiamondIntegral.Section6.RelativeApertureData (G := G) A)
    (hB : B.carrier = hs1 ▸ D.map.image.carrier) (hf : ∀ p : A, (f p).val = hs1 ▸ D.point p.val) :
    Claim hc A B f := by
  subst hs1
  have hE : D.map.image = B := DefSet.eq_of_carrier_eq hB.symm
  intro g
  refine ⟨transport hE (imageGood hc g D hκ hs hsmall h00), fun p => ?_, 1, ?_⟩
  · have hp : f p = ⟨(D.bijection p).val, hE ▸ (D.bijection p).property⟩ := Subtype.ext (hf p)
    rw [hp, transport_form, imageGood_form]
  · rw [clsG_transport]
    exact Steps.single (step_rel hc g D hκ hs hsmall h00)

/-- Special covariant chains. -/
theorem special_chain {s : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)} {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f) : Claim hc A B f := by
  induction h with
  | identity A _ =>
    intro g
    exact ⟨g, fun _ => rfl, 0, .refl _⟩
  | regularize A _ _ =>
    intro g
    refine ⟨regGood g, fun p => regForm_apply g p, 0, ?_⟩
    rw [clsG_reg]
    exact .refl _
  | centripetal A D =>
    exact claim_of_point hc hκ hs hsmall h00 D.bijection rfl D.relativeData
      (by rw [RelativeApertureData.image_carrier, CentripetalData.image_carrier]
          ext q
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, D.relativeData_point ⟨p, hp⟩⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, (D.relativeData_point ⟨p, hp⟩).symm⟩)
      (fun p => (D.relativeData_point p).symm)
  | zeroCentered A D =>
    intro g
    refine ⟨zcGood g D h00, fun p => zcGood_form g D h00 p, 0, ?_⟩
    rw [clsG_zc]
    exact .refl _
  | comp _ _ ihf ihg => exact claim_comp hc ihf ihg

/-- Lemma 7.11 along relative aperture chains. -/
theorem relative_chain {s : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)} {f : Map A B}
    (h : RelativeApertureChain (G := G) A B f) : Claim hc A B f := by
  induction h with
  | original h => exact special_chain hc hκ hs hsmall h00 h
  | relative A D => exact claim_relative hc hκ hs hsmall h00 D
  | comp _ _ ihf ihg => exact claim_comp hc ihf ihg

end Induction

/-! ### Lemma 7.11 from the lift of a chart -/

section Lift
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.SpecialChainStep DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.IsoOfMeasured
open DiamondIntegral.Section6.DiamondLift
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable (c : DiamondIntegral.Section4.RVMeasuredCharts.Chart (BT T) (1 + k))
variable (hU : (toMeasured hc c).doublyBounded)

theorem lift_tagged : ∀ p ∈ (rvLift (toMeasured hc c).object).carrier, ∀ q ∈ (rvLift (toMeasured hc c).object).carrier,
    p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  apply rvValues_injective
  rw [((mem_lift_iff hc c p).mp hp).2, ((mem_lift_iff hc c q).mp hq).2, he]

include hU in
/-- The lift of a doubly bounded chart, with its form, is a chain set. -/
def liftGood : Good T (rvLift (toMeasured hc c).object) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      apply (mem_lift_iff hc c q).mpr
      obtain ⟨hd, hv⟩ := (mem_lift_iff hc c p).mp hp
      rw [← h1, ← h2]
      exact ⟨hd, hv⟩
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := lift_fibre_finite (toMeasured hc c)
  vfBounded := measuredRVLift_vfDoublyBounded _ hU
  rvBounded := by
    obtain ⟨β, hβ⟩ := hU.1
    refine ⟨β, fun p hp i => ?_⟩
    obtain ⟨u, hu, _⟩ := hp
    rw [← hu]
    exact hβ u.val u.property i
  form := liftForm (toMeasured hc c)
  form_labels := fun p q he => congrArg (toMeasured hc c).form (Subtype.ext he)

theorem exists_lift_point {u : Fin c.arity → M} (hu : u ∈ c.domain) :
    ∃ p ∈ (rvLift (toMeasured hc c).object).carrier, rvValues p.2 = u := by
  have hs := c.domain_definable.proper u hu
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (rvTuple (c.coordinate u) (fun i => (c.coordinate_proper u hu i).1))
  refine ⟨(x, rvTuple u hs), (mem_lift_iff hc c _).mpr ⟨?_, ?_⟩, rvValues_rvTuple _ _⟩
  · rw [rvValues_rvTuple]
    exact hu
  · rw [hx, rvValues_rvTuple, rvValues_rvTuple]

/-- The contraction of the lift is the chart's measured object. -/
def contrLiftIso : MeasuredRVIso (contr (liftGood hc c hU) (lift_tagged hc c)) (toMeasured hc c) := by
  have hsub : (contr (liftGood hc c hU) (lift_tagged hc c)).object.domain.carrier ⊆
      (toMeasured hc c).object.domain.carrier := by
    intro t ht
    obtain ⟨p, hp⟩ := pureRVTagQuotient_surjective _ (⟨t, ht⟩ : pureRVTagDomain (rvLift (toMeasured hc c).object))
    have he : p.val.2 = t := congrArg Subtype.val hp
    have h := ((mem_lift_iff hc c p.val).mp p.property).1
    show rvValues t ∈ c.domain
    rw [← he]
    exact h
  let F := Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => Subtype.ext (congrArg (fun z : (toMeasured hc c).object.domain => z.val) he),
      fun b => ?_⟩
    obtain ⟨p, hp, he⟩ := exists_lift_point hc c b.property
    have hb : p.2 = b.val := rvValues_injective he
    exact ⟨⟨b.val, hb ▸ (pureRVTagQuotient _ ⟨p, hp⟩).property⟩, rfl⟩
  refine ⟨rvIsoOfFiniteFibres F hF (contr (liftGood hc c hU) (lift_tagged hc c)).finiteVolume
    (toMeasured hc c).finiteVolume (contr (liftGood hc c hU) (lift_tagged hc c)).nonzero (toMeasured hc c).nonzero,
    fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ a
  unfold MeasuredRVObject.totalWeight
  have hv : (contr (liftGood hc c hU) (lift_tagged hc c)).object.value (pureRVTagQuotient _ p) =
      (toMeasured hc c).object.value (F (pureRVTagQuotient _ p)) := by
    change (preparedRVObject _ (lift_tagged hc c)).value _ = _
    rw [preparedRVObject_value]
    apply rvValues_injective
    change rvValues (tupleRV M p.val.1) = c.coordinate (rvValues p.val.2)
    exact ((mem_lift_iff hc c p.val).mp p.property).2
  rw [volumeGamma_congr hv]
  congr 1
  rw [contractedMeasuredRVObject_form]
  rfl

include hU in
theorem clsG_lift (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c) :
    clsG hc (liftGood hc c hU) = cls (⟨c, hb⟩ : Obj (BT T) (1 + k)) := by
  unfold clsG
  apply (cls_eq_iff_measured hc).mpr
  have e1 := contractionIso (lift_tagged hc c) (liftGood hc c hU).pullback (liftGood hc c hU).finite
    (liftGood hc c hU).vfBounded (liftGood hc c hU).form (liftGood hc c hU).form_labels
    (regularize_tagged _) (regularize_pullback _ (liftGood hc c hU).pullback)
    (regularize_finite _ (liftGood hc c hU).finite) (regularize_vfDoublyBounded _ (liftGood hc c hU).vfBounded)
    (regForm (liftGood hc c hU)) (regForm_labels _) (regularization _) (regularization_bijective _)
    (regularization_matching _ (lift_tagged hc c)) (fun _ => rfl) (fun p => regForm_apply (liftGood hc c hU) p)
  exact ⟨((measuredIso_chartOf hc _).comp e1.symm).comp (contrLiftIso hc c hU)⟩

include hU in
/-- Lemma 7.11 (`special:to:blowup:coa`): for a special covariant chain `T`
(a relative aperture chain) on the lift of a doubly bounded object `U`, the
contraction `U_T` of the regularized image, with the induced form, has the
class of a blowup of `U` of length the number of centripetal steps. -/
theorem lemma_7_11 (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
    (h00 : M ⊨ Axioms.ACVF00) {s : ℕ} {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)}
    {f : Map (rvLift (toMeasured hc c).object) B} (h : RelativeApertureChain (G := G) _ B f) :
    ∃ g' : Good T B, (∀ p, g'.form (f p) = liftForm (toMeasured hc c) p) ∧
      ∃ m, BlowupSteps m (cls (⟨c, hb⟩ : Obj (BT T) (1 + k))) (clsG hc g') := by
  obtain ⟨g', hf, m, hm⟩ := relative_chain hc hκ hs hsmall h00 h (liftGood hc c hU)
  rw [clsG_lift hc c hU hb] at hm
  exact ⟨g', hf, m, hm⟩

end Lift

end DiamondIntegral.Section7.SpecialChainInduction
