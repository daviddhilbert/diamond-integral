import «section 4».GammaRestrictedRVFiniteFamilies

/-! The ring presentation with finite formally tagged bounded Gamma unions.
Disjoint-union additivity and all actual RV-contracted family
isomorphisms introduce exactly the existing single-chart ring. Both
comparison maps preserve the single charts and the finite family sums. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedRVFiniteUnionPresentation
open GammaBoundedRVCharts GammaBoundedProducts GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Family (B : Base (M := M)) (n : ℕ) where
  size : ℕ
  chart : Fin size → BoundedChart B n

def single {B : Base (M := M)} {n : ℕ} (a : BoundedChart B n) : Family B n := ⟨1, fun _ => a⟩
abbrev Generator (B : Base (M := M)) := Σ n, Family B n

def symbol {B : Base (M := M)} {n : ℕ} (a : Family B n) : FreeCommRing (Generator B) := FreeCommRing.of ⟨n, a⟩
def singleSymbol {B : Base (M := M)} {n : ℕ} (a : BoundedChart B n) : FreeCommRing (Generator B) := symbol (single a)

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (singleSymbol (GammaBoundedRVCharts.unit B) - 1)
  | product {n m : ℕ} (a : BoundedChart B m) (b : BoundedChart B n) :
      Relation B (singleSymbol (GammaBoundedRVCharts.product a b) - singleSymbol a * singleSymbol b)
  | singleIso {n : ℕ} (a b : BoundedChart B n) (f : GammaRVChartPresentation.RVVolumeIso a.toChart b.toChart) :
      Relation B (singleSymbol a - singleSymbol b)
  | empty (n : ℕ) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
      Relation B (singleSymbol (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) (DomainBounded.empty n) μ hμ))
  | scissor (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
      (hI : GammaDefinable B I) (hJ : GammaDefinable B J) (hbI : DomainBounded I) (hbJ : DomainBounded J) (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
      (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
      Relation B (singleSymbol (ofTotal B n (I ∪ J) hU (hbI.union hbJ) μ hμ) + singleSymbol (ofTotal B n (I ∩ J) hN (hbI.subset Set.inter_subset_left) μ hμ) -
        singleSymbol (ofTotal B n I hI hbI μ hμ) - singleSymbol (ofTotal B n J hJ hbJ μ hμ))
  | family {n : ℕ} (a : Family B n) : Relation B (symbol a - ∑ i, singleSymbol (a.chart i))
  | iso {n : ℕ} (a b : Family B n) (f : GammaRVFamilyIsomorphisms.Iso (fun i => (a.chart i).toChart) (fun j => (b.chart j).toChart)) : Relation B (symbol a - symbol b)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}
def Ring (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} {n : ℕ} (a : Family B n) : Ring B := Ideal.Quotient.mk _ (symbol a)
def singleClass {B : Base (M := M)} {n : ℕ} (a : BoundedChart B n) : Ring B := objectClass (single a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem class_family {B : Base (M := M)} {n : ℕ} (a : Family B n) : objectClass a = ∑ i, singleClass (a.chart i) := by
  have h := relation_zero B _ (Relation.family a)
  rw [map_sub, map_sum] at h
  exact sub_eq_zero.mp h

theorem class_unit (B : Base (M := M)) : singleClass (GammaBoundedRVCharts.unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem class_product {B : Base (M := M)} {n m : ℕ} (a : BoundedChart B m) (b : BoundedChart B n) :
    singleClass (GammaBoundedRVCharts.product a b) = singleClass a * singleClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem class_singleIso {B : Base (M := M)} {n : ℕ} {a b : BoundedChart B n} (f : GammaRVChartPresentation.RVVolumeIso a.toChart b.toChart) :
    singleClass a = singleClass b := by
  have h := relation_zero B _ (Relation.singleIso a b f)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem class_iso {B : Base (M := M)} {n : ℕ} {a b : Family B n} (f : GammaRVFamilyIsomorphisms.Iso (fun i => (a.chart i).toChart) (fun j => (b.chart j).toChart)) :
    objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b f)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem class_empty (B : Base (M := M)) (n : ℕ)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    singleClass (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) (DomainBounded.empty n) μ hμ) = 0 :=
  relation_zero B _ (Relation.empty n μ hμ)

theorem class_scissor (B : Base (M := M)) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J) (hbI : DomainBounded I) (hbJ : DomainBounded J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    singleClass (ofTotal B n (I ∪ J) hU (hbI.union hbJ) μ hμ) + singleClass (ofTotal B n (I ∩ J) hN (hbI.subset Set.inter_subset_left) μ hμ) =
      singleClass (ofTotal B n I hI hbI μ hμ) + singleClass (ofTotal B n J hJ hbJ μ hμ) := by
  have h := relation_zero B _ (Relation.scissor n I J hI hJ hbI hbJ hU hN μ hμ)
  rw [map_sub, map_sub, map_add, sub_sub] at h
  exact sub_eq_zero.mp h

def evaluation {B : Base (M := M)} {n : ℕ} (a : Family B n) : GammaBoundedRVPresentation.ChartRing B :=
  GammaRestrictedRVFiniteFamilies.Bounded.familyClass a.chart

theorem evaluation_single {B : Base (M := M)} {n : ℕ} (a : BoundedChart B n) :
    evaluation (single a) = GammaBoundedRVPresentation.objectClass a := by
  change (∑ _ : Fin 1, GammaBoundedRVPresentation.objectClass a) = GammaBoundedRVPresentation.objectClass a
  rw [Fin.sum_univ_one]

def freeMap (B : Base (M := M)) : FreeCommRing (Generator B) →+* GammaBoundedRVPresentation.ChartRing B :=
  FreeCommRing.lift (fun a => evaluation a.2)

theorem freeMap_symbol (B : Base (M := M)) {n : ℕ} (a : Family B n) : freeMap B (symbol a) = evaluation a := FreeCommRing.lift_of _ _
theorem freeMap_single (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    freeMap B (singleSymbol a) = GammaBoundedRVPresentation.objectClass a := (freeMap_symbol B (single a)).trans (evaluation_single a)

theorem freeMap_relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) : freeMap B r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_single, GammaBoundedRVPresentation.class_unit, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_single, freeMap_single, freeMap_single, GammaBoundedRVPresentation.class_product, sub_self]
  | singleIso a b f => rw [map_sub, freeMap_single, freeMap_single, GammaBoundedRVPresentation.class_iso f, sub_self]
  | empty n μ hμ => rw [freeMap_single]; exact GammaBoundedRVPresentation.class_empty B n μ hμ
  | scissor n I J hI hJ hbI hbJ hU hN μ hμ =>
    simp only [map_sub, map_add, freeMap_single, sub_sub]
    exact sub_eq_zero.mpr (GammaBoundedRVPresentation.class_scissor B n I J hI hJ hbI hbJ hU hN μ hμ)
  | family a =>
    simp only [map_sub, map_sum, freeMap_symbol, freeMap_single]
    exact sub_self _
  | iso a b f =>
    rw [map_sub, freeMap_symbol, freeMap_symbol]
    exact sub_eq_zero.mpr (GammaRestrictedRVFiniteFamilies.Bounded.familyClass_iso f)

def toChartRing (B : Base (M := M)) : Ring B →+* GammaBoundedRVPresentation.ChartRing B :=
  Ideal.Quotient.lift _ (freeMap B) (by
    have hle : relationIdeal B ≤ RingHom.ker (freeMap B) := Ideal.span_le.mpr (fun r hr => freeMap_relation_zero B r hr)
    exact fun r hr => hle hr)

theorem toChart_class (B : Base (M := M)) {n : ℕ} (a : Family B n) : toChartRing B (objectClass a) = evaluation a := freeMap_symbol B a
theorem toChart_single (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    toChartRing B (singleClass a) = GammaBoundedRVPresentation.objectClass a := freeMap_single B a

def fromChartInvariant (B : Base (M := M)) : GammaBoundedRVPresentation.Invariant B (Ring B) where
  value _ a := singleClass a
  unit := class_unit B
  product _ _ a b := class_product a b
  iso _ _ _ f := class_singleIso f
  empty := class_empty B
  scissor := class_scissor B

def fromChartRing (B : Base (M := M)) : GammaBoundedRVPresentation.ChartRing B →+* Ring B :=
  GammaBoundedRVPresentation.lift B (fromChartInvariant B)

theorem fromChart_class (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n) :
    fromChartRing B (GammaBoundedRVPresentation.objectClass a) = singleClass a :=
  GammaBoundedRVPresentation.lift_class B (fromChartInvariant B) a

theorem to_from (B : Base (M := M)) : (toChartRing B).comp (fromChartRing B) = RingHom.id _ := by
  apply GammaBoundedRVPresentation.hom_ext B
  intro n a
  change toChartRing B (fromChartRing B (GammaBoundedRVPresentation.objectClass a)) = GammaBoundedRVPresentation.objectClass a
  rw [fromChart_class, toChart_single]

theorem from_to (B : Base (M := M)) : (fromChartRing B).comp (toChartRing B) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  change fromChartRing B (toChartRing B (objectClass a.2)) = objectClass a.2
  rw [toChart_class]
  change fromChartRing B (∑ i, GammaBoundedRVPresentation.objectClass (a.2.chart i)) = _
  rw [map_sum]
  simp only [fromChart_class]
  exact (class_family a.2).symm

def equivalence (B : Base (M := M)) : Ring B ≃+* GammaBoundedRVPresentation.ChartRing B :=
  RingEquiv.ofBijective (toChartRing B) ⟨(by
    intro x y h
    have he := congrArg (fromChartRing B) h
    exact (RingHom.congr_fun (from_to B) x).symm.trans (he.trans (RingHom.congr_fun (from_to B) y))), (by
    intro y
    exact ⟨fromChartRing B y, RingHom.congr_fun (to_from B) y⟩)⟩


theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R] (f g : Ring B →+* R)
    (h : ∀ n (a : Family B n), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

end DiamondIntegral.Section4.GammaBoundedRVFiniteUnionPresentation
