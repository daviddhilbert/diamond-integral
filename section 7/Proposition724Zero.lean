import «section 7».SpecialStep
import «section 7».FiberwiseInput
import «section 6».DiamondLiftHomomorphism

/-! Proposition 7.24 (`kernel:L`) and the semigroup part of Theorem 7.26
(`main:prop`) in degree `0`.

The paper: "For `k = 0` there are no blowups and `μ𝕃` is the identity on
finite sets, so both conditions say that `U ≅ V`."

An object of `μVF^◇[0]` is a finite set of RV labels (over the empty VF tuple)
with a Gamma form. Section 6's degree-zero lift data (`zero_arity_measured_lift`)
read it as a doubly bounded measured RV object `rvObj A`, through a bijective
label map preserving the form (`zeroLabel`). The class of `rvObj A` in
`K₊ μRV^db[0]` is an invariant of the scissor presentation of `K₊ μVF^◇[0]`:

* isomorphic objects: a morphism of `μVF^◇[0]` has empty exceptional set
  (`vfDim < 0` is impossible) and empty Jacobian `1`, so it preserves the forms
  (`morphism_form`); the label maps turn it into a measured RV isomorphism
  (`isoOfMorphism`);
* the empty object: its RV object has empty domain;
* scissors: the RV object of a piece (complement) is the restriction
  (complementary restriction) of the RV object (`restrictIso`), and the class
  is additive over a definable piece of the domain (`cls_restrict_add`).

The induced additive map `integralZero : K₊ μVF^◇[0] → K₊ μRV^db[0]` is a left
inverse of `μ𝕃` (`integralZero_liftCls`): the RV object of the lift of `U` is
`U` (`isoOfLift`). With Corollary 6.37 (`ChartOfMeasured.liftCls_surjective`)
this gives Proposition 7.24 in degree `0` (`μIsp^db[0]` is equality,
`FiberwiseInput.ispRel_zero`) and the isomorphism
`K₊ μRV^db[0] ≃+ K₊ μVF^◇[0]`, with no hypotheses beyond the standing ones. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Proposition724Zero
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondSurjectivity DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.IsoOfMeasured DiamondIntegral.Section7.SpecialStep
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Degree-zero measured RV isomorphisms -/

section Iso
variable {S : Set M}

omit [M ⊨ Axioms.ACVF] in
/-- The inverse of a definable bijection is bijective. -/
theorem map_inverse_bijective {P Q : Space LRV M} {A : DefSet P S} {B : DefSet Q S}
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (f.inverse hf) :=
  ⟨fun p z he => by simpa only [Map.apply_inverse] using congrArg f he,
    fun p => ⟨f p, Map.inverse_apply f hf p⟩⟩

/-- In degree zero a bijection of RV label domains matching the forms is a
measured RV isomorphism: the volume factors are empty products. -/
def isoZero {U V : MeasuredRVObject (M := M) S 0} (F : Map U.object.domain V.object.domain)
    (hF : Function.Bijective F) (hform : ∀ u, gammaMapValue U.form u = gammaMapValue V.form (F u)) :
    MeasuredRVIso U V := by
  refine ⟨rvIsoOfFiniteFibres F hF U.finiteVolume V.finiteVolume U.nonzero V.nonzero, fun u => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  unfold MeasuredRVObject.totalWeight
  rw [hform u, volumeGamma_congr (show U.object.value u = V.object.value (F u) from funext (fun i => i.elim0))]

/-- **A morphism of `μVF^◇[0]` preserves the forms.** The exceptional set is
empty (its VF-dimension cannot be `< 0`) and the Jacobian of a map of `VF^0` is
`1`, so the measure identity says that the form ratio is `1`. -/
theorem morphism_form {A B : VFObject (M := M) S 0} (F : Morphism G A B) (p : A.carrier) :
    gammaMapValue A.form p = gammaMapValue B.form (F.map p) := by
  have hbad : p.val ∉ F.bad.carrier := by
    rcases F.bad_small with h | h
    · exact absurd h (Nat.not_lt_zero _)
    · intro hp
      rw [h] at hp
      exact hp
  obtain ⟨L, -, hdet⟩ := F.measure p hbad
  rw [Matrix.det_isEmpty] at hdet
  have hOne : vfValue (1 : VF M) = (1 : Gamma M).val :=
    (valueHom_eq_value (1 : VF M)).symm.trans ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)
  have h1 : gammaMapValue A.form p / gammaMapValue B.form (F.map p) = 1 :=
    Subtype.ext (hdet.symm.trans hOne)
  exact div_eq_one.mp h1

end Iso

/-! ### The measured RV object of an object of `μVF^◇[0]` -/

section Object
variable {S : Set M}

variable (G) in
/-- Section 6's degree-zero lift data of an object of `μVF^◇[0]`. -/
def zeroData (A : VFObject (M := M) S 0) : MeasuredRVLiftData (G := G) A.carrier A.form :=
  zero_arity_measured_lift (G := G) A.carrier A.proper A.form A.finiteRV

variable (G) in
/-- **The measured RV object of an object of `μVF^◇[0]`**: its finite set of RV
labels with the form. -/
def rvObj (A : VFObject (M := M) S 0) : MeasuredRVObject (M := M) S 0 :=
  liftDataObject (zeroData G A)

theorem rvObj_doublyBounded (A : VFObject (M := M) S 0) : (rvObj G A).doublyBounded :=
  liftDataObject_doublyBounded _

variable (G) in
/-- The label map of an object onto the domain of its RV object. -/
def zeroLabel (A : VFObject (M := M) S 0) : Map A.carrier (rvObj G A).object.domain :=
  (zeroData G A).labelMap

theorem zeroLabel_val (A : VFObject (M := M) S 0) (p : A.carrier) :
    (zeroLabel G A p).val = p.val.2 := by
  rw [zeroLabel, (zeroData G A).label_eq p]
  exact congrArg Prod.snd (zero_arity_measured_lift_map_value (G := G) A.carrier A.proper A.form A.finiteRV p)

theorem zeroLabel_form (A : VFObject (M := M) S 0) (p : A.carrier) :
    gammaMapValue (rvObj G A).form (zeroLabel G A p) = gammaMapValue A.form p :=
  (zeroData G A).form_preserves p

theorem zeroLabel_bijective (h00 : M ⊨ Axioms.ACVF00) (A : VFObject (M := M) S 0) :
    Function.Bijective (zeroLabel G A) := by
  constructor
  · intro p q he
    apply Subtype.ext
    apply Prod.ext (funext fun i => i.elim0)
    rw [← zeroLabel_val (G := G), ← zeroLabel_val (G := G), he]
  · intro u
    obtain ⟨p, hp⟩ := ((zeroData G A).special.bijective h00).2
      ⟨(fun i => i.elim0, u.val), ⟨u, rfl, funext fun i => i.elim0⟩⟩
    refine ⟨p, Subtype.ext ?_⟩
    rw [zeroLabel, (zeroData G A).label_eq p, hp]

/-- A morphism of `μVF^◇[0]` gives a measured RV isomorphism of the RV objects. -/
def isoOfMorphism (h00 : M ⊨ Axioms.ACVF00) {A B : VFObject (M := M) S 0} (F : Morphism G A B) :
    MeasuredRVIso (rvObj G A) (rvObj G B) := by
  have hA := zeroLabel_bijective (G := G) h00 A
  refine isoZero ((zeroLabel G B).comp (F.map.comp ((zeroLabel G A).inverse hA)))
    ((zeroLabel_bijective h00 B).comp (F.bijective.comp (map_inverse_bijective _ hA))) (fun u => ?_)
  obtain ⟨p, rfl⟩ := hA.2 u
  change _ = gammaMapValue (rvObj G B).form
    (zeroLabel G B (F.map ((zeroLabel G A).inverse hA (zeroLabel G A p))))
  rw [Map.inverse_apply, zeroLabel_form, zeroLabel_form]
  exact morphism_form F p

/-- In degree zero the label map of a lift is bijective. -/
theorem liftLabel_bijective (U : MeasuredRVObject (M := M) S 0) :
    Function.Bijective (liftLabelMap U.object) := by
  constructor
  · intro p q he
    apply Subtype.ext
    exact Prod.ext (funext fun i => i.elim0) (congrArg Subtype.val he)
  · intro u
    exact ⟨⟨(fun i => i.elim0, u.val), u, rfl, funext fun i => i.elim0⟩, Subtype.ext rfl⟩

/-- **The RV object of the lift of `U` is `U`.** -/
def isoOfLift (h00 : M ⊨ Axioms.ACVF00) (U : MeasuredRVObject (M := M) S 0)
    (hP : ProperInvariant S (rvLift U.object).carrier) :
    MeasuredRVIso (rvObj G (liftObject U hP)) U := by
  have hA := zeroLabel_bijective (G := G) h00 (liftObject U hP)
  refine isoZero ((liftLabelMap U.object).comp ((zeroLabel G (liftObject U hP)).inverse hA))
    ((liftLabel_bijective U).comp (map_inverse_bijective _ hA)) (fun u => ?_)
  obtain ⟨p, rfl⟩ := hA.2 u
  change _ = gammaMapValue U.form
    (liftLabelMap U.object ((zeroLabel G (liftObject U hP)).inverse hA (zeroLabel G (liftObject U hP) p)))
  rw [Map.inverse_apply, zeroLabel_form]
  rfl

/-- The RV object of the empty object has empty domain. -/
theorem rvObj_empty_domain (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M)) :
    (rvObj G (emptyObject (S := S) hc 0)).object.domain.carrier = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro u hu
  obtain ⟨p, -⟩ := (zeroLabel_bijective (G := G) h00 (emptyObject (S := S) hc 0)).2 ⟨u, hu⟩
  exact p.property

/-- **The RV object of a piece is a restriction of the RV object**, along any
definable set of labels matching the piece. -/
def restrictIso (h00 : M ⊨ Axioms.ACVF00) (U : VFObject (M := M) S 0)
    (Y : DefSet (rawMixedSpace (M := M) 0 U.labels) S) (hY : Y.carrier ⊆ U.carrier.carrier)
    (hPY : ProperInvariant S Y.carrier)
    (E : DefSet (rawRVSpace (M := M) (rvObj G U).object.arity) S)
    (hE : E.carrier ⊆ (rvObj G U).object.domain.carrier)
    (hmem : ∀ p : U.carrier, p.val ∈ Y.carrier ↔ (zeroLabel G U p).val ∈ E.carrier) :
    MeasuredRVIso (rvObj G (restrictObject U Y hY hPY)) ((rvObj G U).restrict E hE) := by
  have hR := zeroLabel_bijective (G := G) h00 (restrictObject U Y hY hPY)
  have hU := zeroLabel_bijective (G := G) h00 U
  let g : Map Y ((rvObj G U).restrict E hE).object.domain :=
    ((zeroLabel G U).restrict hY).corestrict (fun a => (hmem ⟨a.val, hY a.property⟩).mp a.property)
  have hg : Function.Bijective g := by
    constructor
    · intro a b he
      have he' := congrArg Subtype.val he
      have h : zeroLabel G U ⟨a.val, hY a.property⟩ = zeroLabel G U ⟨b.val, hY b.property⟩ :=
        Subtype.ext he'
      have hab := congrArg Subtype.val (hU.1 h)
      exact Subtype.ext hab
    · intro e
      obtain ⟨p, hp⟩ := hU.2 ⟨e.val, hE e.property⟩
      have hpE : (zeroLabel G U p).val ∈ E.carrier := by
        rw [hp]
        exact e.property
      have hpY : p.val ∈ Y.carrier := (hmem p).mpr hpE
      have hp' := congrArg Subtype.val hp
      exact ⟨⟨p.val, hpY⟩, Subtype.ext hp'⟩
  refine isoZero (g.comp ((zeroLabel G (restrictObject U Y hY hPY)).inverse hR))
    (hg.comp (map_inverse_bijective _ hR)) (fun u => ?_)
  obtain ⟨q, rfl⟩ := hR.2 u
  change _ = gammaMapValue ((rvObj G U).restrict E hE).form
    (g ((zeroLabel G (restrictObject U Y hY hPY)).inverse hR (zeroLabel G (restrictObject U Y hY hPY) q)))
  rw [Map.inverse_apply, zeroLabel_form]
  change gammaMapValue U.form ⟨q.val, hY q.property⟩ =
    gammaMapValue (rvObj G U).form (zeroLabel G U ⟨q.val, hY q.property⟩)
  rw [zeroLabel_form]

end Object

/-! ### Classes -/

section Classes
variable (hc : CanonicalStructure.IsCanonical (M := M)) (T : LRV.Substructure M)

/-- Isomorphic doubly bounded measured RV objects have the same class. -/
theorem cls_objOf_iso {k : ℕ} {U V : MeasuredRVObject (M := M) (T : Set M) k} (hU : U.doublyBounded)
    (hV : V.doublyBounded) (e : MeasuredRVIso U V) : cls (objOf hc T U hU) = cls (objOf hc T V hV) :=
  (cls_eq_iff_measured hc).mpr ⟨((measuredIso_chartOf hc U).comp e).comp (measuredIso_chartOf hc V).symm⟩

/-- The class of a doubly bounded measured RV object is additive over a
definable piece of its domain and the complement. -/
theorem cls_restrict_add {k : ℕ} (W : MeasuredRVObject (M := M) (T : Set M) k) (hW : W.doublyBounded)
    (D : DefSet (rawRVSpace (M := M) W.object.arity) (T : Set M)) (hD : D.carrier ⊆ W.object.domain.carrier) :
    cls (objOf hc T (W.restrict D hD) (W.restrict_doublyBounded D hD hW)) +
        cls (objOf hc T (restrictCompl W D) (W.restrict_doublyBounded _ _ hW)) =
      cls (objOf hc T W hW) := by
  have hI : DefinableOverBase (BT T) (fun _ : Fin W.object.arity => .rv) (rvValues '' D.carrier) :=
    real_base hc (by rw [← rv_preimage]; exact D.definable) (by rintro _ ⟨t, -, rfl⟩ i; exact (t i).property)
  have hmem : ∀ a ∈ W.object.domain.carrier, a ∈ D.carrier ↔ rvValues a ∈ rvValues '' D.carrier :=
    fun a _ => ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, he⟩ => rvValues_injective he ▸ hb⟩
  rw [cls_partition (objOf hc T W hW) _ hI]
  congr 1
  · exact (cls_eq_iff_measured hc).mpr ⟨(measuredIso_chartOf hc _).comp (pieceIso hc W _ hI D hD hmem).symm⟩
  · exact (cls_eq_iff_measured hc).mpr ⟨(measuredIso_chartOf hc _).comp (cpieceIso hc W _ hI D hmem).symm⟩

/-- The object of a class representative recovers the class. -/
theorem cls_objOf_dbObj (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M)) {k : ℕ} (a : Obj (BT T) k) :
    cls (objOf hc T (dbObj hc h00 hκ hs T hsmall hΓ a).1 (dbObj hc h00 hκ hs T hsmall hΓ a).2) = cls a :=
  (cls_eq_iff_measured hc).mpr
    ⟨(measuredIso_chartOf hc _).comp (measuredIso hc (StrictCharts.strictIso h00 a.toChart)).symm⟩

end Classes

/-! ### The invariant of the scissor presentation of `K₊ μVF^◇[0]` -/

section Invariant
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}

variable (G) in
/-- **The class of an object of `μVF^◇[0]`** in `K₊ μRV^db[0]`: the class of its
RV object. -/
def zeroClass (A : VFObject (M := M) (T : Set M) 0) : Cls (BT T) 0 :=
  cls (objOf hc T (rvObj G A) (rvObj_doublyBounded A))

include h00 in
/-- Isomorphic objects have the same class. -/
theorem zeroClass_iso {A B : VFObject (M := M) (T : Set M) 0} (h : Isomorphic G A B) :
    zeroClass G hc A = zeroClass G hc B := by
  obtain ⟨F⟩ := h
  exact cls_objOf_iso hc T _ _ (isoOfMorphism h00 F)

include h00 in
/-- The empty object has class `0`. -/
theorem zeroClass_empty : zeroClass G hc (emptyObject (S := (T : Set M)) hc 0) = 0 := by
  apply cls_empty
  change rvValues '' (rvObj G (emptyObject (S := (T : Set M)) hc 0)).object.domain.carrier = ∅
  rw [rvObj_empty_domain h00 hc, Set.image_empty]

include h00 in
/-- The class of the lift of a doubly bounded measured RV object is its class. -/
theorem zeroClass_lift (U : MeasuredRVObject (M := M) (T : Set M) 0) (hU : U.doublyBounded)
    (hP : ProperInvariant (T : Set M) (rvLift U.object).carrier) :
    zeroClass G hc (liftObject U hP) = cls (objOf hc T U hU) :=
  cls_objOf_iso hc T _ _ (isoOfLift h00 U hP)

include h00 in
/-- The class is additive over scissors. -/
theorem zeroClass_scissor (U : VFObject (M := M) (T : Set M) 0)
    (X : DefSet (rawMixedSpace (M := M) 0 U.labels) (T : Set M)) (hX : X.carrier ⊆ U.carrier.carrier)
    (hP : ProperInvariant (T : Set M) X.carrier) :
    zeroClass G hc (restrictObject U X hX hP) + zeroClass G hc (complObject U X hP) = zeroClass G hc U := by
  have hU := zeroLabel_bijective (G := G) h00 U
  let W := rvObj G U
  have hW : W.doublyBounded := rvObj_doublyBounded U
  let D : DefSet (rawRVSpace (M := M) W.object.arity) (T : Set M) := ((zeroLabel G U).restrict hX).image
  have hD : D.carrier ⊆ W.object.domain.carrier := by
    rintro _ ⟨a, rfl⟩
    exact ((zeroLabel G U).restrict hX a).property
  have hmemX : ∀ p : U.carrier, p.val ∈ X.carrier ↔ (zeroLabel G U p).val ∈ D.carrier := by
    intro p
    constructor
    · intro h
      exact ⟨⟨p.val, h⟩, rfl⟩
    · rintro ⟨a, ha⟩
      have h : zeroLabel G U ⟨a.val, hX a.property⟩ = zeroLabel G U p := Subtype.ext ha
      rw [← hU.1 h]
      exact a.property
  have hmemC : ∀ p : U.carrier, p.val ∈ (U.carrier.sdiff X).carrier ↔
      (zeroLabel G U p).val ∈ (W.object.domain.sdiff D).carrier := fun p =>
    ⟨fun h => ⟨(zeroLabel G U p).property, fun hd => h.2 ((hmemX p).mpr hd)⟩,
      fun h => ⟨p.property, fun hx => h.2 ((hmemX p).mp hx)⟩⟩
  have h1 : zeroClass G hc (restrictObject U X hX hP) =
      cls (objOf hc T (W.restrict D hD) (W.restrict_doublyBounded D hD hW)) :=
    cls_objOf_iso hc T _ _ (restrictIso h00 U X hX hP D hD hmemX)
  have h2 : zeroClass G hc (complObject U X hP) =
      cls (objOf hc T (restrictCompl W D) (W.restrict_doublyBounded _ _ hW)) :=
    cls_objOf_iso hc T _ _ (restrictIso h00 U (U.carrier.sdiff X) (fun _ h => h.1) (U.proper.diff hP)
      (W.object.domain.sdiff D) (fun _ h => h.1) hmemC)
  rw [h1, h2]
  exact cls_restrict_add hc T W hW D hD

/-- **The class is an invariant of the scissor presentation** of `K₊ μVF^◇[0]`. -/
def zeroInvariant :
    PositiveAdditiveGrothendieck.Invariant (presentation (S := (T : Set M)) G hc 0) (A := Cls (BT T) 0) where
  toFun := zeroClass G hc
  iso h := zeroClass_iso h00 hc h
  empty := zeroClass_empty h00 hc
  scissor := by
    rintro a b c d ⟨U, X, hX, hP, rfl, rfl, hcU, rfl⟩
    subst hcU
    rw [zeroClass_empty h00 hc, add_zero]
    exact zeroClass_scissor h00 hc _ X hX hP

variable (G) in
/-- **The bounded integral in degree `0`**, `∫⁺ : K₊ μVF^◇[0] → K₊ μRV^db[0]`
(`μIsp^db[0]` is trivial): the class of the RV object. -/
def integralZero : KPlus (T : Set M) G hc 0 →+ Cls (BT T) 0 :=
  PositiveAdditiveGrothendieck.lift _ (zeroInvariant h00 hc)

theorem integralZero_vfClass (A : VFObject (M := M) (T : Set M) 0) :
    integralZero G h00 hc (vfClass G hc A) = zeroClass G hc A :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

end Invariant

/-! ### Proposition 7.24 and Theorem 7.26 in degree `0` -/

section Main
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M} (hsmall : Cardinal.mk (T : Set M) < κ)
variable (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable (B₀ : VFGeneratedFieldBase T) (hntB : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- **`∫⁺ μ𝕃 = id` in degree `0`**: the RV object of the lift of `U` is `U`. -/
theorem integralZero_liftCls (x : Cls (BT T) 0) :
    integralZero G h00 hc (liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x) = x := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  rw [liftCls_cls, integralZero_vfClass, zeroClass_lift h00 hc _ (dbObj hc h00 hκ hs T hsmall hΓ a).2]
  exact cls_objOf_dbObj hc T h00 hκ hs hsmall hΓ a

/-- `μ𝕃` is injective in degree `0`. -/
theorem liftCls_zero_injective :
    Function.Injective (liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB) :=
  Function.LeftInverse.injective (integralZero_liftCls h00 hc hκ hs hv hsmall hΓ B₀ hntB)

/-- **Proposition 7.24 (`kernel:L`), degree `0`.** For classes `x`, `y` of
`μRV^db[0]`: `μ𝕃 x = μ𝕃 y` in `K₊ μVF^◇[0]` if and only if `x = y`. -/
theorem proposition_7_24_zero (x y : Cls (BT T) 0) :
    liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x =
        liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB y ↔ x = y :=
  (liftCls_zero_injective h00 hc hκ hs hv hsmall hΓ B₀ hntB).eq_iff

/-- Proposition 7.24 in degree `0`, in the `μIsp^db` form of the positive-degree
statement (`μIsp^db[0]` is equality). -/
theorem proposition_7_24_zero_isp (x y : Cls (BT T) 0) :
    liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x =
        liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB y ↔ IspRel x y := by
  rw [ispRel_zero]
  exact proposition_7_24_zero h00 hc hκ hs hv hsmall hΓ B₀ hntB x y

/-- `μ𝕃 : K₊ μRV^db[0] → K₊ μVF^◇[0]` is bijective (Corollary 6.37 and
Proposition 7.24). -/
theorem liftCls_zero_bijective :
    Function.Bijective (liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB) :=
  ⟨liftCls_zero_injective h00 hc hκ hs hv hsmall hΓ B₀ hntB,
    ChartOfMeasured.liftCls_surjective hc (G := G) h00 hκ hs T hsmall hΓ hv B₀ hntB⟩

/-- **`K₊ μRV^db[0] ≃+ K₊ μVF^◇[0]`**, induced by `μ𝕃`. -/
def liftClsZeroEquiv : Cls (BT T) 0 ≃+ KPlus (T : Set M) G hc 0 :=
  AddEquiv.ofBijective (liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB)
    (liftCls_zero_bijective h00 hc hκ hs hv hsmall hΓ B₀ hntB)

theorem liftClsZeroEquiv_apply (x : Cls (BT T) 0) :
    liftClsZeroEquiv h00 hc hκ hs hv hsmall hΓ B₀ hntB x =
      liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x :=
  rfl

include hκ hs hv hsmall hΓ B₀ hntB in
/-- **Theorem 7.26 (`main:prop`), semigroup part, degree `0`.** The integral
`∫⁺ : K₊ μVF^◇[0] → K₊ μRV^db[0]` is bijective: it is the inverse of `μ𝕃`. -/
theorem integralZero_bijective : Function.Bijective (integralZero G h00 hc (T := T)) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ChartOfMeasured.liftCls_surjective hc (G := G) h00 hκ hs T hsmall hΓ hv B₀ hntB a
    obtain ⟨y, rfl⟩ := ChartOfMeasured.liftCls_surjective hc (G := G) h00 hκ hs T hsmall hΓ hv B₀ hntB b
    rw [integralZero_liftCls h00 hc hκ hs hv hsmall hΓ B₀ hntB,
      integralZero_liftCls h00 hc hκ hs hv hsmall hΓ B₀ hntB] at hab
    rw [hab]
  · intro x
    exact ⟨_, integralZero_liftCls h00 hc hκ hs hv hsmall hΓ B₀ hntB x⟩

/-- The characterization in Theorem 7.26, degree `0`: `∫⁺ [A] = [U]` if and only
if `[A] = [μ𝕃 U]`. -/
theorem integralZero_eq_iff (a : KPlus (T : Set M) G hc 0) (x : Cls (BT T) 0) :
    integralZero G h00 hc a = x ↔ a = liftCls (G := G) (k := 0) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x := by
  conv_lhs => rw [← integralZero_liftCls h00 hc hκ hs hv hsmall hΓ B₀ hntB x]
  exact (integralZero_bijective h00 hc hκ hs hv hsmall hΓ B₀ hntB).1.eq_iff

/-- `∫⁺` in degree `0` is the inverse of the isomorphism induced by `μ𝕃`. -/
theorem integralZero_eq_symm (a : KPlus (T : Set M) G hc 0) :
    integralZero G h00 hc a = (liftClsZeroEquiv h00 hc hκ hs hv hsmall hΓ B₀ hntB).symm a := by
  rw [integralZero_eq_iff h00 hc hκ hs hv hsmall hΓ B₀ hntB]
  exact ((liftClsZeroEquiv h00 hc hκ hs hv hsmall hΓ B₀ hntB).apply_symm_apply a).symm

end Main

end DiamondIntegral.Section7.Proposition724Zero
