import «section 4».RESDimensionFreeRing
import «section 4».RESOrdinaryDisjointPresentation
import «section 4».RVTaggedCoproductClasses

/-! Definition 4.1 (`df:res`): the dimension-free category RES and its
Grothendieck ring.

Objects are the objects of RES[*] with the label forgotten: definable RV
sets over the original base with finite value support (`Object`).
Morphisms are all definable bijections (`Iso`). The Grothendieck ring
`Ring B` is presented directly from this category: one generator per
object, with relations for definable bijections, the empty object, the
unit, cartesian products and tagged disjoint unions.

Every object underlies a RES[k] object (`chart`, `exists_label`), using
the finite-to-one label replacing the RV coordinate `0` by `1`. The
headline `definition_4_1_identification` identifies `Ring B` with
`RESDimensionFreeRing.Ring B` (the ordinary RES ring modulo underlying
bijections across degrees), sending the class of `U` to the class of any
RES[k] object `(U, f)`, compatibly with the forgetful map from the graded
ordinary RES ring. No Hrushovski–Kazhdan result is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESDimensionFreeCategory
open RVMeasuredCharts RVMeasuredProductProperties FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### Objects and morphisms -/

/-- An object of the dimension-free category RES: a definable RV set over the
original base with finitely many value patterns (including `∞`). This is a
RES[*] object with its label forgotten. -/
structure Object (B : Base (M := M)) where
  arity : ℕ
  domain : Set (Fin arity → M)
  domain_definable : DefinableOverBase B (fun _ : Fin arity => .rv) domain
  finite_values : (Set.range (fun u : domain => fun i : Fin arity =>
    Values.vrv ⟨u.val i, domain_definable.proper u.val u.property i⟩)).Finite

/-- A morphism of RES: a definable bijection between the underlying sets. -/
structure Iso {B : Base (M := M)} (U V : Object B) where
  equiv : U.domain ≃ V.domain
  graph_definable : DefinableOverBase B (fun _ : Fin (V.arity + U.arity) => .rv)
    {w | ∃ u : U.domain, w = join V.arity U.arity u.val (equiv u).val}

/-- Forget the label (and volume form) of a RES[k] object. -/
def ofRES {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : Object B :=
  ⟨a.arity, a.domain, a.domain_definable, a.finite_values⟩

theorem eq_of_domain {B : Base (M := M)} {n : ℕ} (D D' : Set (Fin n → M)) (h : D = D')
    (hD : DefinableOverBase B (fun _ : Fin n => .rv) D) (hD' : DefinableOverBase B (fun _ : Fin n => .rv) D')
    (hf : (Set.range (fun u : D => fun i : Fin n => Values.vrv ⟨u.val i, hD.proper u.val u.property i⟩)).Finite)
    (hf' : (Set.range (fun u : D' => fun i : Fin n => Values.vrv ⟨u.val i, hD'.proper u.val u.property i⟩)).Finite) :
    (⟨n, D, hD, hf⟩ : Object B) = ⟨n, D', hD', hf'⟩ := by
  subst h
  rfl

/-! ### Every object underlies a RES[k] object -/

/-- The RV coordinate with `0` replaced by `1`; at most two-to-one. -/
def unzero (x : M) : M := if x = iRVZero then iRVOne else x

/-- The label into `RV^K` (`n ≤ K`): `unzero` on each coordinate, then `1`. -/
def label (n K : ℕ) (u : Fin n → M) : Fin K → M :=
  fun i => if h : i.val < n then unzero (u ⟨i.val, h⟩) else iRVOne

def unzeroGraph : Set (Fin 2 → M) := {w | iRV (w 0) ∧ w 1 = unzero (w 0)}

omit hM in
theorem unzero_of_ne {x : M} (h : x ≠ iRVZero) : unzero x = x := by
  unfold unzero
  exact ite_eq_right h

omit hM in
theorem unzero_zero : unzero (iRVZero (M := M)) = iRVOne := by
  unfold unzero
  exact ite_eq_left rfl

theorem unzero_nonzero {x : M} (hx : iRV x) : NonzeroRV (unzero x) := by
  by_cases h : x = iRVZero
  · rw [h, unzero_zero]
    exact ⟨Transfer.rv_one_mem hM, RVCalc.rv_one_ne_zero hM⟩
  · rw [unzero_of_ne h]
    exact ⟨hx, h⟩

theorem unzeroGraph_definable (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin 2 => .rv) (unzeroGraph (M := M)) := by
  have h01 : DefinableOverBase B (fun _ : Fin 2 => .rv) ({![iRVZero, iRVOne]} : Set (Fin 2 → M)) :=
    tuple_singleton_definable_base B _ _ (by
      intro i; fin_cases i
      · exact RVNamedTuples.zero_definable B
      · exact RVNamedTuples.one_definable B)
  have h00 : DefinableOverBase B (fun _ : Fin 2 => .rv) ({![iRVZero, iRVZero]} : Set (Fin 2 → M)) :=
    tuple_singleton_definable_base B _ _ (by
      intro i; fin_cases i <;> exact RVNamedTuples.zero_definable B)
  have hdiag : DefinableOverBase B (fun _ : Fin 2 => .rv)
      ((fun x : Fin 1 → M => x ∘ (fun _ : Fin 2 => (0 : Fin 1))) ''
        sortedUniverse (fun _ : Fin 1 => SortTag.rv)) :=
    (real_definableOverBase B _ _ (sortedUniverse_definable B.real (fun _ : Fin 1 => SortTag.rv))).image_real
      (fun _ : Fin 2 => (0 : Fin 1))
  convert h01.union (hdiag.sdiff h00) using 1
  ext w
  constructor
  · rintro ⟨hw, he⟩
    by_cases h0 : w 0 = iRVZero
    · left
      rw [h0, unzero_zero] at he
      funext i; fin_cases i
      · exact h0
      · exact he
    · right
      refine ⟨⟨fun _ => w 0, fun _ => hw, ?_⟩, ?_⟩
      · funext i; fin_cases i
        · rfl
        · exact ((unzero_of_ne h0).symm.trans he.symm)
      · intro hz
        exact h0 (congrFun hz 0)
  · rintro (hw | ⟨⟨x, hx, rfl⟩, hz⟩)
    · rw [hw]
      exact ⟨Transfer.rv_zero_mem hM, unzero_zero.symm⟩
    · have h0 : x 0 ≠ iRVZero := by
        intro h0
        apply hz
        funext i; fin_cases i <;> exact h0
      exact ⟨hx 0, (unzero_of_ne h0).symm⟩

theorem label_proper (n K : ℕ) (u : Fin n → M) (hu : ∀ i, iRV (u i)) : Proper (label n K u) := by
  intro i
  by_cases h : i.val < n
  · simp only [label, dite_eq_left h]
    exact unzero_nonzero (hu _)
  · simp only [label, dite_eq_right h]
    exact ⟨Transfer.rv_one_mem hM, RVCalc.rv_one_ne_zero hM⟩

omit hM in
theorem label_finite_fibres {n K : ℕ} (hK : n ≤ K) (D : Set (Fin n → M)) (t : Fin K → M) :
    {u | u ∈ D ∧ label n K u = t}.Finite := by
  apply (Set.Finite.pi (t := fun j : Fin n => ({t ⟨j.val, lt_of_lt_of_le j.2 hK⟩, iRVZero} : Set M))
    (fun _ => Set.toFinite _)).subset
  rintro u ⟨_, hu⟩ j _
  have he := congrFun hu ⟨j.val, lt_of_lt_of_le j.2 hK⟩
  simp only [label, dite_eq_left j.2] at he
  by_cases h0 : u j = iRVZero
  · exact Or.inr h0
  · left
    rw [unzero_of_ne h0] at he
    exact he

theorem label_graph_definable (B : Base (M := M)) {n : ℕ} (D : Set (Fin n → M))
    (hD : DefinableOverBase B (fun _ : Fin n => .rv) D) (K : ℕ) :
    DefinableOverBase B (fun _ : Fin (K + n) => .rv) (graphOn D (label n K)) := by
  let S : Set (Fin (K + n) → M) := sortedUniverse (fun _ : Fin (K + n) => SortTag.rv)
  let A : Fin K → Set (Fin (K + n) → M) := fun i =>
    {w | w ∈ S ∧ w (tailIndex K n i) = label n K (w ∘ headIndex K n) i}
  have hA : ∀ i, DefinableOverBase B (fun _ : Fin (K + n) => .rv) (A i) := by
    intro i
    by_cases h : i.val < n
    · have hp := (unzeroGraph_definable B).preimage_real (fun _ : Fin (K + n) => SortTag.rv)
        ![headIndex K n ⟨i.val, h⟩, tailIndex K n i]
      convert hp using 1
      ext w
      change (w ∈ S ∧ w (tailIndex K n i) = label n K (w ∘ headIndex K n) i) ↔
        ((iRV (w (headIndex K n ⟨i.val, h⟩)) ∧
          w (tailIndex K n i) = unzero (w (headIndex K n ⟨i.val, h⟩))) ∧ w ∈ S)
      simp only [label, dite_eq_left h, Function.comp_apply]
      exact ⟨fun hw => ⟨⟨hw.1 _, hw.2⟩, hw.1⟩, fun hw => ⟨hw.2, hw.1.2⟩⟩
    · have hp := (tuple_singleton_definable_base B (fun _ : Fin 1 => SortTag.rv)
        (fun _ => iRVOne) (fun _ => RVNamedTuples.one_definable B)).preimage_real
        (fun _ : Fin (K + n) => SortTag.rv) (fun _ : Fin 1 => tailIndex K n i)
      convert hp using 1
      ext w
      change (w ∈ S ∧ w (tailIndex K n i) = label n K (w ∘ headIndex K n) i) ↔
        ((fun _ : Fin 1 => w (tailIndex K n i)) = (fun _ => iRVOne) ∧ w ∈ S)
      simp only [label, dite_eq_right h]
      constructor
      · rintro ⟨hw, he⟩
        exact ⟨funext fun _ => he, hw⟩
      · rintro ⟨he, hw⟩
        exact ⟨hw, congrFun he 0⟩
  have h0 := hD.preimage_real (fun _ : Fin (K + n) => SortTag.rv) (headIndex K n)
  have hall := DefinableOverBase.finite_iInter Finset.univ A (fun i _ => hA i)
  convert h0.inter hall using 1
  ext w
  constructor
  · rintro ⟨hw, he⟩
    have hS : w ∈ S := by
      apply GammaBoundedProducts.all_coordinates K n (fun x => iRV x) w
      · intro i
        exact hD.proper _ hw i
      · intro i
        have hl := (label_proper n K _ (hD.proper _ hw) i).1
        rw [he] at hl
        exact hl
    refine ⟨⟨hw, hS⟩, hS, fun i _ => ⟨hS, ?_⟩⟩
    exact (congrFun he i).symm
  · rintro ⟨⟨hw, _⟩, _, hall⟩
    exact ⟨hw, funext fun i => ((hall i (Finset.mem_univ i)).2).symm⟩

/-- The object `U` with the label `label`, as a RES[K] object, `arity U ≤ K`. -/
def chartAt {B : Base (M := M)} (U : Object B) (K : ℕ) (hK : U.arity ≤ K) : RESChart B K where
  arity := U.arity
  domain := U.domain
  domain_definable := U.domain_definable
  coordinate := label U.arity K
  coordinate_definable := label_graph_definable B U.domain U.domain_definable K
  coordinate_proper := fun u hu => label_proper U.arity K u (U.domain_definable.proper u hu)
  finite_fibres := label_finite_fibres hK U.domain
  volume := fun _ => 1
  volume_definable := constant_volume_definable B _ U.domain_definable 1 (GammaGroupNames.one_definable_base B)
  finite_values := U.finite_values

/-- The canonical RES[arity U] object underlying `U`. -/
def chart {B : Base (M := M)} (U : Object B) : RESChart B U.arity := chartAt U U.arity le_rfl

theorem ofRES_chartAt {B : Base (M := M)} (U : Object B) (K : ℕ) (hK : U.arity ≤ K) :
    ofRES (chartAt U K hK) = U := rfl

theorem ofRES_chart {B : Base (M := M)} (U : Object B) : ofRES (chart U) = U := rfl

/-- Every RES object underlies a RES[k] object for some `k`. -/
theorem exists_label {B : Base (M := M)} (U : Object B) : ∃ k, ∃ a : RESChart B k, ofRES a = U :=
  ⟨U.arity, chart U, rfl⟩

/-! ### Morphisms and RES underlying bijections -/

def Iso.refl {B : Base (M := M)} (U : Object B) : Iso U U :=
  ⟨(RVUnderlyingIsomorphisms.refl (chart U).toChart).equiv,
    (RVUnderlyingIsomorphisms.refl (chart U).toChart).graph_definable⟩

def Iso.symm {B : Base (M := M)} {U V : Object B} (e : Iso U V) : Iso V U :=
  let F : RVUnderlyingIsomorphisms.Iso (chart U).toChart (chart V).toChart := ⟨e.equiv, e.graph_definable⟩
  ⟨(RVUnderlyingIsomorphisms.symm F).equiv, (RVUnderlyingIsomorphisms.symm F).graph_definable⟩

/-- A morphism between the underlying objects is an underlying bijection of RES charts. -/
def Iso.toChart {B : Base (M := M)} {k l : ℕ} {a : RESChart B k} {b : RESChart B l}
    (e : Iso (ofRES a) (ofRES b)) : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart :=
  ⟨e.equiv, e.graph_definable⟩

/-- An underlying bijection of RES charts is a morphism of the underlying objects. -/
def Iso.ofChart {B : Base (M := M)} {k l : ℕ} {a : RESChart B k} {b : RESChart B l}
    (F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart) : Iso (ofRES a) (ofRES b) :=
  ⟨F.equiv, F.graph_definable⟩

def Iso.ofEq {B : Base (M := M)} {U V : Object B} (h : U = V) : Iso U V := h ▸ Iso.refl U

/-! ### Unit, products and disjoint unions -/

/-- The one-point object. -/
def unit (B : Base (M := M)) : Object B := ofRES (RESChartRing.unit B)

/-- The cartesian product; its domain is `productSet U.domain V.domain`. -/
def product {B : Base (M := M)} (U V : Object B) : Object B := ofRES (resProduct (chart U) (chart V))

theorem product_domain {B : Base (M := M)} (U V : Object B) :
    (product U V).domain = RVRealProducts.productSet U.domain V.domain := rfl

/-- The tagged disjoint union of two RV sets: `{0} × U × {0}^n ∪ {1} × {0}^m × V`. -/
def taggedSet (B : Base (M := M)) {m n : ℕ} (U : Set (Fin m → M)) (V : Set (Fin n → M)) :
    Set (Fin (n + (m + 1)) → M) :=
  RVRealProducts.productSet (RVRealProducts.productSet (RVNamedTuples.tagZero B).domain U)
      (RVNamedTuples.zeros B n).domain ∪
    RVRealProducts.productSet (RVRealProducts.productSet (RVNamedTuples.tagOne B).domain
      (RVNamedTuples.zeros B m).domain) V

/-- The tagged coproduct of two same-degree charts depends only on the underlying sets. -/
theorem coproduct_domain {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    (RVTaggedCoproduct.coproduct a b).domain = taggedSet B a.domain b.domain := by
  change (RVTaggedCoproduct.leftData a b).domain ∪ (RVTaggedCoproduct.rightData a b).domain = _
  rw [RVTaggedCoproduct.leftData, RVNamedTuples.castGrade_domain]
  rfl

/-- The disjoint union, realised with labels of the common degree `arity U + arity V`. -/
def sum {B : Base (M := M)} (U V : Object B) : Object B :=
  ofRES (RVTaggedCoproductProperties.resCoproduct (chartAt U (U.arity + V.arity) (Nat.le_add_right _ _))
    (chartAt V (U.arity + V.arity) (Nat.le_add_left _ _)))

theorem sum_domain {B : Base (M := M)} (U V : Object B) :
    (sum U V).domain = taggedSet B U.domain V.domain :=
  coproduct_domain _ _

/-- The tagged coproduct of any two same-degree RES objects underlies `sum`. -/
theorem ofRES_coproduct {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    ofRES (RVTaggedCoproductProperties.resCoproduct a b) = sum (ofRES a) (ofRES b) := by
  unfold sum ofRES
  exact eq_of_domain _ _ ((coproduct_domain a.toChart b.toChart).trans
    (coproduct_domain (chartAt (ofRES a) _ (Nat.le_add_right _ _)).toChart
      (chartAt (ofRES b) _ (Nat.le_add_left _ _)).toChart).symm) _ _ _ _

/-! ### The Grothendieck ring -/

def symbol {B : Base (M := M)} (U : Object B) : FreeCommRing (Object B) := FreeCommRing.of U

inductive Relation (B : Base (M := M)) : FreeCommRing (Object B) → Prop where
  | unit : Relation B (symbol (unit B) - 1)
  | product (U V : Object B) : Relation B (symbol (product U V) - symbol U * symbol V)
  | iso (U V : Object B) (e : Iso U V) : Relation B (symbol U - symbol V)
  | empty (U : Object B) (h : U.domain = ∅) : Relation B (symbol U)
  | sum (U V : Object B) : Relation B (symbol (sum U V) - symbol U - symbol V)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Object B)) := Ideal.span {r | Relation B r}

/-- K(RES): the Grothendieck ring of the dimension-free category RES under
disjoint unions and cartesian products. -/
def Ring (B : Base (M := M)) := FreeCommRing (Object B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} (U : Object B) : Ring B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol U)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Object B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit (B : Base (M := M)) : objectClass (unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product {B : Base (M := M)} (U V : Object B) :
    objectClass (product U V) = objectClass U * objectClass V := by
  have h := relation_zero B _ (Relation.product U V)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} {U V : Object B} (e : Iso U V) :
    objectClass U = objectClass V := by
  have h := relation_zero B _ (Relation.iso U V e)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} (U : Object B) (h : U.domain = ∅) :
    objectClass U = 0 := relation_zero B _ (Relation.empty U h)

theorem objectClass_sum {B : Base (M := M)} (U V : Object B) :
    objectClass (sum U V) = objectClass U + objectClass V := by
  have h := relation_zero B _ (Relation.sum U V)
  rw [map_sub, map_sub, sub_sub] at h
  exact sub_eq_zero.mp h

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : Object B → R
  unit : value (unit B) = 1
  product : ∀ U V, value (product U V) = value U * value V
  iso : ∀ U V, Iso U V → value U = value V
  empty : ∀ U : Object B, U.domain = ∅ → value U = 0
  sum : ∀ U V, value (sum U V) = value U + value V

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    FreeCommRing (Object B) →+* R := FreeCommRing.lift f.value

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (U : Object B) : freeMap B f (symbol U) = f.value U := FreeCommRing.lift_of _ _

theorem invariant_relation_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (r : FreeCommRing (Object B)) (hr : Relation B r) : freeMap B f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, f.unit, sub_self]
  | product U V => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.product, sub_self]
  | iso U V e => rw [map_sub, freeMap_symbol, freeMap_symbol, f.iso U V e, sub_self]
  | empty U h => rw [freeMap_symbol, f.empty U h]
  | sum U V =>
    rw [map_sub, map_sub, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.sum, sub_sub, sub_self]

def lift (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : Ring B →+* R :=
  Ideal.Quotient.lift _ (freeMap B f) (by
    have hle : relationIdeal B ≤ RingHom.ker (freeMap B f) :=
      Ideal.span_le.mpr (fun r hr => invariant_relation_zero B f r hr)
    intro r hr
    exact hle hr)

theorem lift_objectClass (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (U : Object B) : lift B f (objectClass U) = f.value U := freeMap_symbol B f U

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R] (f g : Ring B →+* R)
    (h : ∀ U : Object B, f (objectClass U) = g (objectClass U)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  exact h

/-! ### Forgetting labels: the map from the graded ordinary RES ring -/

def familyInvariant (B : Base (M := M)) :
    RVOrdinaryFamilyPresentation.Invariant (RESOrdinaryDisjointPresentation.family B) (Ring B) where
  value k a ha := objectClass (ofRES (⟨a, ha⟩ : RESChart B k))
  iso _ _ _ _ _ f := objectClass_iso (Iso.ofChart (RVUnderlyingIsomorphisms.ofFixed f))
  coproduct _ a b ha hb :=
    (congrArg objectClass (ofRES_coproduct (⟨a, ha⟩ : RESChart B _) (⟨b, hb⟩ : RESChart B _))).trans
      (objectClass_sum _ _)
  unit := objectClass_unit B
  product _ _ a b ha hb := objectClass_product (ofRES (⟨a, ha⟩ : RESChart B _)) (ofRES (⟨b, hb⟩ : RESChart B _))
  empty _ a ha h := objectClass_empty (ofRES (⟨a, ha⟩ : RESChart B _)) h

/-- The forgetful ring map K(RES[*]) → K(RES), `[(U, f)] ↦ [U]`. -/
def forgetLabel (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* Ring B :=
  (RVOrdinaryFamilyPresentation.lift (RESOrdinaryDisjointPresentation.family B) (familyInvariant B)).comp
    (RESOrdinaryDisjointPresentation.equivalence B).symm.toRingHom

theorem forgetLabel_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    forgetLabel B (RESOrdinaryRing.objectClass a) = objectClass (ofRES a) := by
  have hs : (RESOrdinaryDisjointPresentation.equivalence B).symm (RESOrdinaryRing.objectClass a) =
      RESOrdinaryDisjointPresentation.objectClass a :=
    (RingEquiv.symm_apply_eq _).mpr (RESOrdinaryDisjointPresentation.toChartRing_class B a).symm
  change RVOrdinaryFamilyPresentation.lift _ (familyInvariant B)
    ((RESOrdinaryDisjointPresentation.equivalence B).symm (RESOrdinaryRing.objectClass a)) = _
  rw [hs]
  exact RVOrdinaryFamilyPresentation.lift_objectClass _ (familyInvariant B) _

/-- The forgetful ring map from the measured graded RES ring. -/
def forgetMeasured (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B :=
  (forgetLabel B).comp (RESOrdinaryRing.forget B)

theorem forgetMeasured_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    forgetMeasured B (RESChartRing.objectClass a) = objectClass (ofRES a) := by
  change forgetLabel B (RESOrdinaryRing.forget B (RESChartRing.objectClass a)) = _
  rw [RESOrdinaryRing.forget_objectClass, forgetLabel_objectClass]

/-! ### Identification with `RESDimensionFreeRing.Ring` -/

theorem dimensionFree_class_eq {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l)
    (h : ofRES a = ofRES b) :
    RESDimensionFreeRing.objectClass a = RESDimensionFreeRing.objectClass b :=
  RESDimensionFreeRing.objectClass_iso a b (Iso.toChart (Iso.ofEq h))

theorem dimensionFree_empty {B : Base (M := M)} {k : ℕ} (a : RESChart B k) (h : a.domain = ∅) :
    RESDimensionFreeRing.objectClass a = 0 := by
  change RESDimensionFreeRing.quotient B (RESOrdinaryRing.objectClass a) = 0
  rw [RESOrdinaryRing.objectClass_empty a h, map_zero]

theorem dimensionFree_coproduct {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    RESDimensionFreeRing.objectClass (RVTaggedCoproductProperties.resCoproduct a b) =
      RESDimensionFreeRing.objectClass a + RESDimensionFreeRing.objectClass b := by
  change RESDimensionFreeRing.quotient B (RESOrdinaryRing.objectClass _) =
    RESDimensionFreeRing.quotient B (RESOrdinaryRing.objectClass a) +
      RESDimensionFreeRing.quotient B (RESOrdinaryRing.objectClass b)
  rw [RVTaggedCoproductClasses.ordinary_res_coproduct_class, map_add]

def dimensionFreeInvariant (B : Base (M := M)) : Invariant B (RESDimensionFreeRing.Ring B) where
  value U := RESDimensionFreeRing.objectClass (chart U)
  unit := (dimensionFree_class_eq (chart (unit B)) (RESChartRing.unit B) rfl).trans
    (RESDimensionFreeRing.objectClass_unit B)
  product U V := (dimensionFree_class_eq (chart (product U V)) (resProduct (chart U) (chart V)) rfl).trans
    (RESDimensionFreeRing.objectClass_product (chart U) (chart V))
  iso U V e := RESDimensionFreeRing.objectClass_iso (chart U) (chart V) (Iso.toChart e)
  empty U h := dimensionFree_empty (chart U) h
  sum U V := by
    rw [dimensionFree_class_eq (chart (sum U V)) _ (ofRES_chart (sum U V)), dimensionFree_coproduct,
      dimensionFree_class_eq (chartAt U (U.arity + V.arity) (Nat.le_add_right _ _)) (chart U) rfl,
      dimensionFree_class_eq (chartAt V (U.arity + V.arity) (Nat.le_add_left _ _)) (chart V) rfl]

/-- K(RES) → `RESDimensionFreeRing.Ring`, `[U] ↦ [(U, label)]`. -/
def toDimensionFree (B : Base (M := M)) : Ring B →+* RESDimensionFreeRing.Ring B :=
  lift B (dimensionFreeInvariant B)

theorem toDimensionFree_objectClass (B : Base (M := M)) (U : Object B) :
    toDimensionFree B (objectClass U) = RESDimensionFreeRing.objectClass (chart U) :=
  lift_objectClass B (dimensionFreeInvariant B) U

theorem forgetLabel_degreeIdeal (B : Base (M := M)) :
    ∀ x ∈ RESDimensionFreeRing.degreeIdeal B, forgetLabel B x = 0 := by
  have hle : RESDimensionFreeRing.degreeIdeal B ≤ RingHom.ker (forgetLabel B) := by
    apply Ideal.span_le.mpr
    rintro x ⟨k, l, a, b, F, rfl⟩
    change forgetLabel B _ = 0
    rw [map_sub, forgetLabel_objectClass, forgetLabel_objectClass, objectClass_iso (Iso.ofChart F), sub_self]
  intro x hx
  exact hle hx

/-- `RESDimensionFreeRing.Ring` → K(RES), induced by forgetting labels. -/
def fromDimensionFree (B : Base (M := M)) : RESDimensionFreeRing.Ring B →+* Ring B :=
  Ideal.Quotient.lift (RESDimensionFreeRing.degreeIdeal B) (forgetLabel B) (forgetLabel_degreeIdeal B)

theorem fromDimensionFree_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    fromDimensionFree B (RESDimensionFreeRing.objectClass a) = objectClass (ofRES a) :=
  (Ideal.Quotient.lift_mk _ _ _).trans (forgetLabel_objectClass B a)

theorem from_to (B : Base (M := M)) :
    (fromDimensionFree B).comp (toDimensionFree B) = RingHom.id (Ring B) := by
  apply hom_ext B
  intro U
  change fromDimensionFree B (toDimensionFree B (objectClass U)) = objectClass U
  rw [toDimensionFree_objectClass, fromDimensionFree_objectClass, ofRES_chart]

theorem to_from (B : Base (M := M)) :
    (toDimensionFree B).comp (fromDimensionFree B) = RingHom.id (RESDimensionFreeRing.Ring B) := by
  apply Ideal.Quotient.ringHom_ext
  apply RESOrdinaryRing.hom_ext B
  intro k a
  change toDimensionFree B (fromDimensionFree B (RESDimensionFreeRing.objectClass a)) =
    RESDimensionFreeRing.objectClass a
  rw [fromDimensionFree_objectClass, toDimensionFree_objectClass]
  exact dimensionFree_class_eq _ _ rfl

/-- K(RES) ≃ `RESDimensionFreeRing.Ring`. -/
def equivalence (B : Base (M := M)) : Ring B ≃+* RESDimensionFreeRing.Ring B :=
  RingEquiv.ofRingHom (toDimensionFree B) (fromDimensionFree B) (to_from B) (from_to B)

theorem equivalence_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    equivalence B (objectClass (ofRES a)) = RESDimensionFreeRing.objectClass a :=
  (toDimensionFree_objectClass B (ofRES a)).trans (dimensionFree_class_eq (chart (ofRES a)) a rfl)

theorem equivalence_objectClass_of_eq (B : Base (M := M)) {k : ℕ} (a : RESChart B k) (U : Object B)
    (h : ofRES a = U) : equivalence B (objectClass U) = RESDimensionFreeRing.objectClass a := by
  subst h
  exact equivalence_objectClass B a

theorem equivalence_forgetLabel (B : Base (M := M)) :
    (equivalence B).toRingHom.comp (forgetLabel B) = RESDimensionFreeRing.quotient B := by
  apply RESOrdinaryRing.hom_ext B
  intro k a
  change equivalence B (forgetLabel B (RESOrdinaryRing.objectClass a)) = RESDimensionFreeRing.objectClass a
  rw [forgetLabel_objectClass, equivalence_objectClass]

theorem equivalence_forgetMeasured (B : Base (M := M)) :
    (equivalence B).toRingHom.comp (forgetMeasured B) =
      (RESDimensionFreeRing.quotient B).comp (RESOrdinaryRing.forget B) := by
  change ((equivalence B).toRingHom.comp (forgetLabel B)).comp (RESOrdinaryRing.forget B) = _
  rw [equivalence_forgetLabel]

theorem equivalence_symm_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    (equivalence B).symm (RESDimensionFreeRing.objectClass a) = objectClass (ofRES a) :=
  (RingEquiv.symm_apply_eq _).mpr (equivalence_objectClass B a).symm

/-- Definition 4.1: the Grothendieck ring K(RES) of the dimension-free category
(objects: RES[*] objects with the label forgotten; morphisms: all definable
bijections; sum: disjoint union; product: cartesian product) is isomorphic to
`RESDimensionFreeRing.Ring`, by a ring isomorphism sending `[U]` to the class
of any RES[k] object `(U, f)` and commuting with the forgetful maps from the
graded ordinary and measured RES rings. Every object admits such a label. -/
theorem definition_4_1_identification (B : Base (M := M)) :
    ∃ e : Ring B ≃+* RESDimensionFreeRing.Ring B,
      (∀ (U : Object B) (k : ℕ) (a : RESChart B k), ofRES a = U →
        e (objectClass U) = RESDimensionFreeRing.objectClass a) ∧
      e.toRingHom.comp (forgetLabel B) = RESDimensionFreeRing.quotient B ∧
      e.toRingHom.comp (forgetMeasured B) = (RESDimensionFreeRing.quotient B).comp (RESOrdinaryRing.forget B) ∧
      (∀ U : Object B, ∃ k, ∃ a : RESChart B k, ofRES a = U) :=
  ⟨equivalence B, fun U _ a h => equivalence_objectClass_of_eq B a U h, equivalence_forgetLabel B,
    equivalence_forgetMeasured B, exists_label⟩

end DiamondIntegral.Section4.RESDimensionFreeCategory
