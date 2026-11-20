import «section 7».Proposition724
import «section 7».Proposition724Zero
import «section 7».DiamondRing
import «section 7».RingClasses
import «section 4».RVBoundedDisjointPresentation

/-! Theorem 7.26 (`main:prop`), the graded ring isomorphism
`∫^◇ : K μVF^◇[*] ≅ K μRV^db[*] / J_var`, and Remark 7.25 (`thekernel`):
the kernel of the lift `μ𝕃 : K μRV^db[*] → K μVF^◇[*]` is `J_var`.

* `K μVF^◇[*]` is the ring presentation `DiamondRing.Ring` with unit the lift
  of the unit object of `μRV^db[0]`. `K μRV^db[*]` is Section 4's
  `RVBoundedRing.Ring`, and `J_var` is `manuscriptIdeal` (Notation 4.17).
* `liftRing : K μRV^db[*] → K μVF^◇[*]` is the lift, through Section 4's
  disjoint-union presentation (`RVBoundedDisjointPresentation`). It kills
  `J_var` by Lemma 7.12 (`liftQuot`).
* `integralRing : K μVF^◇[*] → K μRV^db[*] / J_var` sends an object to the
  class of a standard contraction in positive degree, through Proposition 7.24
  (`Proposition724.integralOf`), and through the degree-zero integral
  (`Proposition724Zero.integralZero`). It is multiplicative because every
  object is isomorphic to the lift of a chart object (`exists_chart_lift`,
  from Corollary 6.37 and Lemma 6.33). Products of isomorphic objects are
  isomorphic, and the lift of a product chart is the product of the lifts.
* `integralRing` and `liftQuot` are inverse (`integralRingEquiv`), and the
  kernel of `liftRing` is `J_var` (`remark_7_25`), with no cancellation in
  `K₊ μRV^db`.

The two product facts are hypotheses of this file (`ProductHyp`,
`LiftProductHyp`), discharged in their own files. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Theorem726
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondProduct DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section4 DiamondIntegral.Section4.RelativeAnnularGenerators
open DiamondIntegral.Section7.IntermediateFormsInput DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.RingClasses
open DiamondIntegral.Section7.Proposition724 DiamondIntegral.Section7.DiamondRing

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (T : LRV.Substructure M)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable (B₀ : VFGeneratedFieldBase T) (hntB : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-! ### Lifts of chart objects -/

/-- The lift of a chart object. -/
abbrev liftOf {k : ℕ} (a : Obj (BT T) k) : VFObject (M := M) (T : Set M) k :=
  liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1
    (measuredRVLift_properInvariant (G := G) h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2)

/-- The unit of `K μVF^◇[*]`: the lift of the unit object of `μRV^db[0]`. -/
abbrev unitObj : VFObject (M := M) (T : Set M) 0 :=
  liftOf G h00 hc hκ hs hv T hsmall hΓ (RVBoundedRing.unit (BT T))

/-- **`K μVF^◇[*]`.** -/
abbrev KVF := DiamondRing.Ring G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ)

/-- **`K μRV^db[*] / J_var`.** -/
abbrev QRV := RVBoundedRing.Ring (BT T) ⧸ manuscriptIdeal (BT T)

include B₀ hntB in
/-- **Every object is isomorphic to the lift of a chart object** (Corollary 6.37
with Lemma 6.33). -/
theorem exists_chart_lift {k : ℕ} (A : VFObject (M := M) (T : Set M) k) :
    ∃ a : Obj (BT T) k, Isomorphic G A (liftOf G h00 hc hκ hs hv T hsmall hΓ a) := by
  have hE := DiamondGroupoid.isomorphic_equivalence (G := G) (S := (T : Set M)) (n := k) h00 hc hκ.le hs hsmall hv
  obtain ⟨U, hU, hiso⟩ : ∃ U : MeasuredRVObject (M := M) (T : Set M) k, ∃ hU : U.doublyBounded,
      Isomorphic G A (liftObject U (measuredRVLift_properInvariant h00 hc hκ hs hv U hU)) := by
    rcases k with _ | n
    · exact DiamondSurjectivity.exists_isomorphic_lift_zero (G := G) h00 hc lin hκ hs hv hsmall hΓ A
    · exact DiamondSurjectivity.exists_isomorphic_lift (G := G) h00 hc lin hκ hs hv T B₀ hsmall hΓ hntB A
  refine ⟨objOf hc T U hU, hE.trans hiso ?_⟩
  let e : MeasuredRVIso U (dbObj hc h00 hκ hs T hsmall hΓ (objOf hc T U hU)).1 :=
    (measuredIso_chartOf hc U).symm.comp (MeasuredRVBridge.measuredIso hc (StrictCharts.strictIso h00 (chartOf hc U)))
  obtain ⟨F, -⟩ := lemma_6_33_diamond (G := G) h00 hc lin hκ hs hv T B₀ hsmall hΓ hntB e hU
    (dbObj hc h00 hκ hs T hsmall hΓ (objOf hc T U hU)).2 _ _
  exact ⟨F⟩

/-! ### The hypotheses of this file -/

/-- Products of isomorphic objects are isomorphic. -/
def ProductHyp : Prop :=
  ∀ (k l : ℕ) (A A' : VFObject (M := M) (T : Set M) k) (B B' : VFObject (M := M) (T : Set M) l),
    Isomorphic G A A' → Isomorphic G B B' →
      Isomorphic G (VFObject.product hc A B) (VFObject.product hc A' B')

/-- The lift of a product chart is the product of the lifts, up to the degree
cast `k + l = l + k`. -/
def LiftProductHyp : Prop :=
  ∀ (k l : ℕ) (a : Obj (BT T) k) (b : Obj (BT T) l),
    Isomorphic G (liftOf G h00 hc hκ hs hv T hsmall hΓ (RVBoundedCharts.product a b))
      ((Nat.add_comm k l) ▸ VFObject.product hc (liftOf G h00 hc hκ hs hv T hsmall hΓ a)
        (liftOf G h00 hc hκ hs hv T hsmall hΓ b))

theorem isomorphic_cast {k l : ℕ} (h : k = l) {A B : VFObject (M := M) (T : Set M) k}
    (hAB : Isomorphic G A B) : Isomorphic G (h ▸ A) (h ▸ B) := by
  subst h
  exact hAB

variable (hProd : ProductHyp G hc T) (hLiftProd : LiftProductHyp G h00 hc hκ hs hv T hsmall hΓ)

/-! ### The lift as a ring map -/

/-- The class of the lift of a chart object in `K μVF^◇[*]`. -/
theorem degreeHom_liftCls {k : ℕ} (a : Obj (BT T) k) :
    degreeHom G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ) k
        (liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hntB (cls a)) =
      ringClass G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ) (liftOf G h00 hc hκ hs hv T hsmall hΓ a) := by
  rw [liftCls_cls, degreeHom_vfClass]

include hLiftProd in
/-- The lift, as an invariant of Section 4's disjoint-union presentation. -/
def liftInvariant :
    RVFamilyDisjointPresentation.Invariant (RVBoundedDisjointPresentation.family (BT T))
      (KVF G h00 hc hκ hs hv T hsmall hΓ) where
  value k a ha := ringClass G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ)
    (liftOf G h00 hc hκ hs hv T hsmall hΓ (⟨a, ha⟩ : Obj (BT T) k))
  iso k a b ha hb f := by
    rw [← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB,
      ← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB,
      cls_eq_of_iso (a := (⟨a, ha⟩ : Obj (BT T) k)) (b := ⟨b, hb⟩) f]
  coproduct k a b ha hb := by
    rw [← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB,
      ← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB,
      ← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB, ← map_add, ← map_add]
    rfl
  unit := ringClass_one G hc _
  product k l a b ha hb := by
    refine (ringClass_iso G hc _ (hLiftProd k l ⟨a, ha⟩ ⟨b, hb⟩)).trans ?_
    rw [ringClass_cast, ringClass_product]
  empty k a ha h := by
    rw [← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB, cls_empty _ h, map_zero, map_zero]

/-- **The lift `μ𝕃 : K μRV^db[*] → K μVF^◇[*]` as a ring map.** -/
def liftRing : RVBoundedRing.Ring (BT T) →+* KVF G h00 hc hκ hs hv T hsmall hΓ :=
  (RVFamilyDisjointPresentation.lift _ (liftInvariant G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd)).comp
    (RVBoundedDisjointPresentation.fromChartRing (BT T))

theorem liftRing_objectClass {k : ℕ} (a : Obj (BT T) k) :
    liftRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd (RVBoundedRing.objectClass a) =
      ringClass G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ) (liftOf G h00 hc hκ hs hv T hsmall hΓ a) := by
  change RVFamilyDisjointPresentation.lift _ _ (RVBoundedDisjointPresentation.fromChartRing (BT T)
    (RVBoundedRing.objectClass a)) = _
  rw [RVBoundedDisjointPresentation.fromChartRing_class]
  exact RVFamilyDisjointPresentation.lift_objectClass _ _ _

/-- **`J_var` lies in the kernel of the lift** (Lemma 7.12). -/
theorem ideal_le_ker :
    manuscriptIdeal (BT T) ≤ RingHom.ker (liftRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨k, D, rfl⟩
  change liftRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd
    (RVBoundedRing.objectClass D.annularObject - RVBoundedRing.objectClass D.source) = 0
  rw [map_sub, liftRing_objectClass, liftRing_objectClass,
    ← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB,
    ← degreeHom_liftCls G h00 hc hκ hs hv T hsmall hΓ B₀ hntB,
    BlowupLiftGeneral.lemma_7_12 hc h00 hκ hs T hsmall hΓ hv B₀ hntB D, sub_self]

/-- The lift on `K μRV^db[*] / J_var`. -/
def liftQuot : QRV T →+* KVF G h00 hc hκ hs hv T hsmall hΓ :=
  Ideal.Quotient.lift _ (liftRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd)
    (fun _ hx => ideal_le_ker G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd hx)

theorem liftQuot_mk {k : ℕ} (a : Obj (BT T) k) :
    liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd (Ideal.Quotient.mk _ (RVBoundedRing.objectClass a)) =
      ringClass G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ) (liftOf G h00 hc hκ hs hv T hsmall hΓ a) :=
  liftRing_objectClass G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd a

/-! ### The integral as a ring map -/

section Integral
variable (hIF : IntermediateForms M G)

/-- Support data for `T` from its field base. -/
abbrev Vb : Set M := vfFieldNames B₀.field ∪ Set.range (vfValues (Fin.elim0 : Fin 0 → VF M))

/-- The class of a `μRV^db[k]` class modulo `J_var`. -/
def rvToQ (k : ℕ) : Cls (BT T) k →+ QRV T :=
  (Ideal.Quotient.mk (manuscriptIdeal (BT T))).toAddMonoidHom.comp clsRing

/-- `μIsp^db`-related classes have the same image modulo `J_var` (Remark 7.25, first half). -/
def ispToQ (n : ℕ) : IspQuot (BT T) n →+ QRV T :=
  AddCon.lift (ispCon (BT T) n) (rvToQ T (n + 1)) (fun x y h => by
    rw [AddCon.ker_rel]
    exact Ideal.Quotient.eq.mpr (ispRel_mem h))

/-- The integral in degree `k`, modulo `J_var`. -/
def intQ : ∀ k : ℕ, KPlus (T : Set M) G hc k →+ QRV T
  | 0 => (rvToQ T 0).comp (Proposition724Zero.integralZero G h00 hc)
  | n + 1 => (ispToQ T n).comp (integralOf h00 hc hκ hs hv (Vb T B₀) (support_of_base B₀ hntB).1
      (support_of_base B₀ hntB).2.1 (support_of_base B₀ hntB).2.2.1 (support_of_base B₀ hntB).2.2.2
      hsmall hΓ hIF)

theorem intQ_liftCls {k : ℕ} (x : Cls (BT T) k) :
    intQ G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF k
        (liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x) = rvToQ T k x := by
  rcases k with _ | n
  · change rvToQ T 0 (Proposition724Zero.integralZero G h00 hc _) = _
    rw [Proposition724Zero.integralZero_liftCls h00 hc hκ hs hv hsmall hΓ B₀ hntB x]
  · change ispToQ T n (integralOf h00 hc hκ hs hv _ _ _ _ _ hsmall hΓ hIF _) = _
    rw [integral_liftCls h00 hc hκ hs hv _ _ _ _ _ hsmall hΓ B₀ hntB hIF x]
    rfl

theorem intQ_cast {k l : ℕ} (h : k = l) (X : VFObject (M := M) (T : Set M) k) :
    intQ G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF l (vfClass G hc (h ▸ X)) =
      intQ G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF k (vfClass G hc X) := by
  subst h
  rfl

theorem intQ_lift {k : ℕ} (a : Obj (BT T) k) :
    intQ G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF k (vfClass G hc (liftOf G h00 hc hκ hs hv T hsmall hΓ a)) =
      Ideal.Quotient.mk _ (RVBoundedRing.objectClass a) := by
  rw [← liftCls_cls (G := G) hc h00 hκ hs T hsmall hΓ hv B₀ hntB a, intQ_liftCls]
  rfl

include hProd hLiftProd in
/-- The integral, as an invariant of the ring presentation of `K μVF^◇[*]`. -/
def integralInvariant :
    RingInvariant G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ) (QRV T) where
  value k A := intQ G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF k (vfClass G hc A)
  unit := by
    rw [intQ_lift, RVBoundedRing.objectClass_unit, map_one]
  product k l A B := by
    obtain ⟨a, ha⟩ := exists_chart_lift G h00 hc hκ hs hv T hsmall hΓ B₀ hntB A
    obtain ⟨b, hb⟩ := exists_chart_lift G h00 hc hκ hs hv T hsmall hΓ B₀ hntB B
    have hE := DiamondGroupoid.isomorphic_equivalence (G := G) (S := (T : Set M)) (n := l + k) h00 hc hκ.le hs
      hsmall hv
    have h2 := hE.trans (isomorphic_cast G T (Nat.add_comm k l) (hProd k l _ _ _ _ ha hb))
      (hE.symm (hLiftProd k l a b))
    rw [← intQ_cast G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF (Nat.add_comm k l), vfClass_iso hc h2,
      intQ_lift, vfClass_iso hc ha, vfClass_iso hc hb, intQ_lift, intQ_lift,
      RVBoundedRing.objectClass_product, map_mul]
  iso k A B h := by rw [vfClass_iso hc h]
  empty k := by rw [vfClass_empty, map_zero]
  scissor k U X hX hP := by rw [← map_add, vfClass_scissor]

/-- **The integral `∫^◇ : K μVF^◇[*] → K μRV^db[*] / J_var` as a ring map.** -/
def integralRing : KVF G h00 hc hκ hs hv T hsmall hΓ →+* QRV T :=
  DiamondRing.lift (integralInvariant G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF)

theorem integralRing_ringClass {k : ℕ} (A : VFObject (M := M) (T : Set M) k) :
    integralRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF
        (ringClass G hc (unitObj G h00 hc hκ hs hv T hsmall hΓ) A) =
      intQ G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hIF k (vfClass G hc A) :=
  lift_ringClass _ A

theorem integral_comp_lift :
    (integralRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF).comp
      (liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd) = RingHom.id (QRV T) := by
  apply Ideal.Quotient.ringHom_ext
  apply RVBoundedGrading.hom_ext (BT T)
  intro k a
  change integralRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF
    (liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd (Ideal.Quotient.mk _ (RVBoundedRing.objectClass a))) =
      Ideal.Quotient.mk _ (RVBoundedRing.objectClass a)
  rw [liftQuot_mk, integralRing_ringClass, intQ_lift]

theorem lift_comp_integral :
    (liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd).comp
      (integralRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF) =
      RingHom.id (KVF G h00 hc hκ hs hv T hsmall hΓ) := by
  apply DiamondRing.hom_ext
  intro k A
  obtain ⟨a, ha⟩ := exists_chart_lift G h00 hc hκ hs hv T hsmall hΓ B₀ hntB A
  change liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd
    (integralRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF _) = _
  rw [integralRing_ringClass, vfClass_iso hc ha, intQ_lift, liftQuot_mk]
  exact (ringClass_iso G hc _ ha).symm

/-- **Theorem 7.26 (`main:prop`), ring part.** The integral is a ring
isomorphism `K μVF^◇[*] ≅ K μRV^db[*] / J_var`, inverse to the map induced by
`μ𝕃`. -/
def integralRingEquiv : KVF G h00 hc hκ hs hv T hsmall hΓ ≃+* QRV T :=
  RingEquiv.ofRingHom (integralRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF)
    (liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd)
    (integral_comp_lift G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF)
    (lift_comp_integral G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF)

include hProd hIF in
/-- **Remark 7.25 (`thekernel`).** The kernel of the ring map
`μ𝕃 : K μRV^db[*] → K μVF^◇[*]` is the relative annular ideal `J_var`. -/
theorem remark_7_25 :
    RingHom.ker (liftRing G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd) = manuscriptIdeal (BT T) := by
  refine le_antisymm (fun x hx => ?_) (ideal_le_ker G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd)
  have h0 : liftQuot G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hLiftProd (Ideal.Quotient.mk _ x) = 0 := hx
  have h1 := RingHom.congr_fun (integral_comp_lift G h00 hc hκ hs hv T hsmall hΓ B₀ hntB hProd hLiftProd hIF)
    (Ideal.Quotient.mk _ x)
  rw [RingHom.comp_apply, h0, map_zero, RingHom.id_apply] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

end Integral

end DiamondIntegral.Section7.Theorem726
