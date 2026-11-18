import «section 4».PositiveChartPresentation
import «section 4».RVBoundedBalancedTensor
import «section 3».BalancedSquare

/-! Remark 4.10 (`tensor:bd`) at the positive level. The product construction
gives a homomorphism of positive (scissor) semirings
`μΨ^db : K₊ μRES[*] ⊗ K₊ μΓ^db[*] → K₊ μRV^db[*]`.

The positive semirings are presented by the same actual charts and relations
as the chart rings of this section (isomorphisms, unit, products, empty
charts, scissors), with no subtraction:
* `resRelations`: measured RES charts;
* `rvRelations`: doubly bounded measured RV charts;
* `gammaRelations`: doubly bounded measured Γ charts;
* `finiteRelations`: finite measured Γ charts, the balancing coefficients.

The RES inclusion `ofRES` and the Γ lift `sharp` respect the relations, and
agree on finite Γ charts (`square`). Hence the balanced tensor map
`comparison : K₊ μRES ⊗_{K₊ μΓ^fin} K₊ μΓ^db → K₊ μRV^db` with
`comparison (x ⊗ y) = ofRES x * sharp y`, and the map on the plain tensor over
`ℕ` (`comparisonNat`). The ring-level comparison of
`RVBoundedBalancedTensor` is its group completion on generators
(`comparison_toRing`). No tensor injectivity or surjectivity is asserted. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedPositiveTensor
open PositiveChartPresentation RVMeasuredCharts RVMeasuredProductProperties
open GammaOrderLogic GammaDefinableMaps GammaBoundedProducts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### The four positive presentations -/

/-- Measured RES charts. -/
def resRelations (B : Base (M := M)) : ChartRelations (RESChartRing.Generator B) where
  iso x y := ∃ k, ∃ a b : RESChart B k, Nonempty (Iso a.toChart b.toChart) ∧ x = ⟨k,a⟩ ∧ y = ⟨k,b⟩
  unit := ⟨0,RESChartRing.unit B⟩
  product x y := ⟨y.1 + x.1,resProduct x.2 y.2⟩
  empty x := x.2.domain = ∅
  scissor x y z w := ∃ k, ∃ a b c d : RESChart B k,
    RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart ∧
      x = ⟨k,c⟩ ∧ y = ⟨k,d⟩ ∧ z = ⟨k,a⟩ ∧ w = ⟨k,b⟩

/-- Doubly bounded measured RV charts. -/
def rvRelations (B : Base (M := M)) : ChartRelations (RVBoundedRing.Generator B) where
  iso x y := ∃ k, ∃ a b : RVBoundedCharts.BoundedChart B k,
    Nonempty (Iso a.toChart b.toChart) ∧ x = ⟨k,a⟩ ∧ y = ⟨k,b⟩
  unit := ⟨0,RVBoundedRing.unit B⟩
  product x y := ⟨y.1 + x.1,RVBoundedCharts.product x.2 y.2⟩
  empty x := x.2.domain = ∅
  scissor x y z w := ∃ k, ∃ a b c d : RVBoundedCharts.BoundedChart B k,
    RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart ∧
      x = ⟨k,c⟩ ∧ y = ⟨k,d⟩ ∧ z = ⟨k,a⟩ ∧ w = ⟨k,b⟩

/-- Doubly bounded measured Γ charts. -/
def gammaRelations (B : Base (M := M)) : ChartRelations (GammaBoundedRVPresentation.Generator B) where
  iso x y := ∃ n, ∃ a b : GammaBoundedRVCharts.BoundedChart B n,
    Nonempty (GammaRVChartPresentation.RVVolumeIso a.toChart b.toChart) ∧ x = ⟨n,a⟩ ∧ y = ⟨n,b⟩
  unit := ⟨0,GammaBoundedRVCharts.unit B⟩
  product x y := ⟨y.1 + x.1,GammaBoundedRVCharts.product x.2 y.2⟩
  empty x := ∃ (n : ℕ) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ),
    x = ⟨n,GammaBoundedRVCharts.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n)
      (DomainBounded.empty n) μ hμ⟩
  scissor x y z w := ∃ (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaDefinable B I) (hJ : GammaDefinable B J) (hbI : DomainBounded I) (hbJ : DomainBounded J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ),
    x = ⟨n,GammaBoundedRVCharts.ofTotal B n (I ∪ J) hU (hbI.union hbJ) μ hμ⟩ ∧
    y = ⟨n,GammaBoundedRVCharts.ofTotal B n (I ∩ J) hN (hbI.subset Set.inter_subset_left) μ hμ⟩ ∧
    z = ⟨n,GammaBoundedRVCharts.ofTotal B n I hI hbI μ hμ⟩ ∧
    w = ⟨n,GammaBoundedRVCharts.ofTotal B n J hJ hbJ μ hμ⟩

/-- Finite measured Γ charts. -/
def finiteRelations (B : Base (M := M)) : ChartRelations (GammaFiniteRVPresentation.Generator B) where
  iso x y := ∃ n, ∃ a b : GammaFiniteRVCharts.FiniteChart B n,
    Nonempty (GammaRVChartPresentation.RVVolumeIso a.toChart b.toChart) ∧ x = ⟨n,a⟩ ∧ y = ⟨n,b⟩
  unit := ⟨0,GammaFiniteRVCharts.unit B⟩
  product x y := ⟨y.1 + x.1,GammaFiniteRVCharts.product x.2 y.2⟩
  empty x := ∃ (n : ℕ) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ),
    x = ⟨n,GammaFiniteRVCharts.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n)
      Set.finite_empty μ hμ⟩
  scissor x y z w := ∃ (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaDefinable B I) (hJ : GammaDefinable B J) (hiI : I.Finite) (hiJ : J.Finite)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ),
    x = ⟨n,GammaFiniteRVCharts.ofTotal B n (I ∪ J) hU (hiI.union hiJ) μ hμ⟩ ∧
    y = ⟨n,GammaFiniteRVCharts.ofTotal B n (I ∩ J) hN (hiI.subset Set.inter_subset_left) μ hμ⟩ ∧
    z = ⟨n,GammaFiniteRVCharts.ofTotal B n I hI hiI μ hμ⟩ ∧
    w = ⟨n,GammaFiniteRVCharts.ofTotal B n J hJ hiJ μ hμ⟩

/-- `K₊ μRES[*]`. -/
abbrev RESPositive (B : Base (M := M)) := (resRelations B).KPlus
/-- `K₊ μRV^db[*]`. -/
abbrev RVPositive (B : Base (M := M)) := (rvRelations B).KPlus
/-- `K₊ μΓ^db[*]`. -/
abbrev GammaPositive (B : Base (M := M)) := (gammaRelations B).KPlus
/-- The finite Γ coefficient semiring. -/
abbrev FinitePositive (B : Base (M := M)) := (finiteRelations B).KPlus

/-! ### The product maps -/

/-- The RES inclusion `K₊ μRES[*] → K₊ μRV^db[*]`. -/
def ofRES (B : Base (M := M)) : RESPositive B →+* RVPositive B := (resRelations B).lift {
  value x := (rvRelations B).cls ⟨x.1,RVBoundedCharts.ofRES x.2⟩
  iso := by
    rintro x y ⟨k,a,b,⟨F⟩,rfl,rfl⟩
    exact (rvRelations B).cls_iso ⟨k,RVBoundedCharts.ofRES a,RVBoundedCharts.ofRES b,⟨F⟩,rfl,rfl⟩
  unit := (rvRelations B).cls_unit
  product x y := (rvRelations B).cls_product ⟨x.1,RVBoundedCharts.ofRES x.2⟩ ⟨y.1,RVBoundedCharts.ofRES y.2⟩
  empty := by
    rintro ⟨k,a⟩ h
    exact (rvRelations B).cls_empty (a := ⟨k,RVBoundedCharts.ofRES a⟩) h
  scissor := by
    rintro x y z w ⟨k,a,b,c,d,h,rfl,rfl,rfl,rfl⟩
    exact (rvRelations B).cls_scissor ⟨k,RVBoundedCharts.ofRES a,RVBoundedCharts.ofRES b,
      RVBoundedCharts.ofRES c,RVBoundedCharts.ofRES d,h,rfl,rfl,rfl,rfl⟩ }

@[simp] theorem ofRES_cls (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    ofRES B ((resRelations B).cls ⟨k,a⟩) = (rvRelations B).cls ⟨k,RVBoundedCharts.ofRES a⟩ :=
  (resRelations B).lift_cls _ _

/-- The Γ lift `K₊ μΓ^db[*] → K₊ μRV^db[*]`. -/
def sharp (B : Base (M := M)) : GammaPositive B →+* RVPositive B := (gammaRelations B).lift {
  value x := (rvRelations B).cls ⟨x.1,GammaBoundedRVCharts.sharp x.2⟩
  iso := by
    rintro x y ⟨n,a,b,⟨F⟩,rfl,rfl⟩
    exact (rvRelations B).cls_iso ⟨n,_,_,⟨RVSharpCharts.sharpIso F⟩,rfl,rfl⟩
  unit := ((rvRelations B).cls_iso ⟨0,_,_,⟨GammaBoundedRVCharts.sharpUnitIso B⟩,rfl,rfl⟩).trans
    (rvRelations B).cls_unit
  product x y := ((rvRelations B).cls_iso ⟨_,_,_,⟨GammaBoundedRVCharts.sharpProductIso x.2 y.2⟩,rfl,rfl⟩).trans
    ((rvRelations B).cls_product ⟨x.1,GammaBoundedRVCharts.sharp x.2⟩ ⟨y.1,GammaBoundedRVCharts.sharp y.2⟩)
  empty := by
    rintro x ⟨n,μ,hμ,rfl⟩
    exact (rvRelations B).cls_empty (RVSharpScissors.sharp_empty B n μ hμ)
  scissor := by
    rintro x y z w ⟨n,I,J,hI,hJ,_,_,hU,hN,μ,hμ,rfl,rfl,rfl,rfl⟩
    exact (rvRelations B).cls_scissor ⟨n,_,_,_,_,RVSharpScissors.sharp_scissor B n I J hI hJ hU hN μ hμ,
      rfl,rfl,rfl,rfl⟩ }

@[simp] theorem sharp_cls (B : Base (M := M)) {n : ℕ} (a : GammaBoundedRVCharts.BoundedChart B n) :
    sharp B ((gammaRelations B).cls ⟨n,a⟩) = (rvRelations B).cls ⟨n,GammaBoundedRVCharts.sharp a⟩ :=
  (gammaRelations B).lift_cls _ _

/-- Finite Γ charts as RES charts (their RV lift has finitely many values). -/
def finiteToRES (B : Base (M := M)) : FinitePositive B →+* RESPositive B := (finiteRelations B).lift {
  value x := (resRelations B).cls ⟨x.1,GammaFiniteRVCharts.sharp x.2⟩
  iso := by
    rintro x y ⟨n,a,b,⟨F⟩,rfl,rfl⟩
    exact (resRelations B).cls_iso ⟨n,_,_,⟨RVSharpCharts.sharpIso F⟩,rfl,rfl⟩
  unit := ((resRelations B).cls_iso ⟨0,_,_,⟨GammaFiniteRVCharts.sharpUnitIso B⟩,rfl,rfl⟩).trans
    (resRelations B).cls_unit
  product x y := ((resRelations B).cls_iso ⟨_,_,_,⟨GammaFiniteRVCharts.sharpProductIso x.2 y.2⟩,rfl,rfl⟩).trans
    ((resRelations B).cls_product ⟨x.1,GammaFiniteRVCharts.sharp x.2⟩ ⟨y.1,GammaFiniteRVCharts.sharp y.2⟩)
  empty := by
    rintro x ⟨n,μ,hμ,rfl⟩
    exact (resRelations B).cls_empty (RVSharpScissors.sharp_empty B n μ hμ)
  scissor := by
    rintro x y z w ⟨n,I,J,hI,hJ,_,_,hU,hN,μ,hμ,rfl,rfl,rfl,rfl⟩
    exact (resRelations B).cls_scissor ⟨n,_,_,_,_,RVSharpScissors.sharp_scissor B n I J hI hJ hU hN μ hμ,
      rfl,rfl,rfl,rfl⟩ }

@[simp] theorem finiteToRES_cls (B : Base (M := M)) {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) :
    finiteToRES B ((finiteRelations B).cls ⟨n,a⟩) = (resRelations B).cls ⟨n,GammaFiniteRVCharts.sharp a⟩ :=
  (finiteRelations B).lift_cls _ _

/-- Finite Γ charts are doubly bounded. -/
def finiteToGamma (B : Base (M := M)) : FinitePositive B →+* GammaPositive B := (finiteRelations B).lift {
  value x := (gammaRelations B).cls ⟨x.1,GammaFiniteRVCharts.bounded x.2⟩
  iso := by
    rintro x y ⟨n,a,b,⟨F⟩,rfl,rfl⟩
    exact (gammaRelations B).cls_iso ⟨n,GammaFiniteRVCharts.bounded a,GammaFiniteRVCharts.bounded b,⟨F⟩,rfl,rfl⟩
  unit := (gammaRelations B).cls_unit
  product x y := (gammaRelations B).cls_product ⟨x.1,GammaFiniteRVCharts.bounded x.2⟩
    ⟨y.1,GammaFiniteRVCharts.bounded y.2⟩
  empty := by
    rintro x ⟨n,μ,hμ,rfl⟩
    exact (gammaRelations B).cls_empty ⟨n,μ,hμ,rfl⟩
  scissor := by
    rintro x y z w ⟨n,I,J,hI,hJ,hiI,hiJ,hU,hN,μ,hμ,rfl,rfl,rfl,rfl⟩
    exact (gammaRelations B).cls_scissor ⟨n,I,J,hI,hJ,GammaFiniteBounds.finite_domain_bounded I hiI,
      GammaFiniteBounds.finite_domain_bounded J hiJ,hU,hN,μ,hμ,rfl,rfl,rfl,rfl⟩ }

@[simp] theorem finiteToGamma_cls (B : Base (M := M)) {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) :
    finiteToGamma B ((finiteRelations B).cls ⟨n,a⟩) =
      (gammaRelations B).cls ⟨n,GammaFiniteRVCharts.bounded a⟩ :=
  (finiteRelations B).lift_cls _ _

/-- The two product maps agree on the finite Γ coefficients. -/
theorem square (B : Base (M := M)) :
    (ofRES B).comp (finiteToRES B) = (sharp B).comp (finiteToGamma B) := by
  apply (finiteRelations B).hom_ext
  rintro ⟨n,a⟩
  change ofRES B (finiteToRES B ((finiteRelations B).cls ⟨n,a⟩)) =
    sharp B (finiteToGamma B ((finiteRelations B).cls ⟨n,a⟩))
  rw [finiteToRES_cls,ofRES_cls,finiteToGamma_cls,sharp_cls]
  rfl

instance resAlgebra (B : Base (M := M)) : Algebra (FinitePositive B) (RESPositive B) :=
  (finiteToRES B).toAlgebra

instance gammaAlgebra (B : Base (M := M)) : Algebra (FinitePositive B) (GammaPositive B) :=
  (finiteToGamma B).toAlgebra

/-- The positive balanced tensor `K₊ μRES[*] ⊗_{K₊ μΓ^fin} K₊ μΓ^db[*]`. -/
abbrev Source (B : Base (M := M)) := RESPositive B ⊗[FinitePositive B] GammaPositive B

/-- Remark 4.10: the product construction `μΨ^db` at the positive level. -/
def comparison (B : Base (M := M)) : Source B →+* RVPositive B :=
  DiamondIntegral.Section3.balancedSquareMap (ofRES B) (sharp B) (square B)

@[simp] theorem comparison_tmul (B : Base (M := M)) (x : RESPositive B) (y : GammaPositive B) :
    comparison B (x ⊗ₜ[FinitePositive B] y) = ofRES B x * sharp B y := rfl

/-- On generators: the class of an RES chart times the class of a doubly
bounded Γ chart goes to the class of the product of the RES chart with the
RV lift of the Γ chart. -/
theorem comparison_charts (B : Base (M := M)) {k n : ℕ} (a : RESChart B k)
    (b : GammaBoundedRVCharts.BoundedChart B n) :
    comparison B ((resRelations B).cls ⟨k,a⟩ ⊗ₜ[FinitePositive B] (gammaRelations B).cls ⟨n,b⟩) =
      (rvRelations B).cls ⟨n + k,RVBoundedCharts.product (RVBoundedCharts.ofRES a) (GammaBoundedRVCharts.sharp b)⟩ := by
  rw [comparison_tmul,ofRES_cls,sharp_cls]
  exact ((rvRelations B).cls_product ⟨k,RVBoundedCharts.ofRES a⟩ ⟨n,GammaBoundedRVCharts.sharp b⟩).symm

/-- The same product map on the plain tensor product over `ℕ`. -/
def comparisonNat (B : Base (M := M)) : RESPositive B ⊗[ℕ] GammaPositive B →+* RVPositive B :=
  (Algebra.TensorProduct.lift (ofRES B).toNatAlgHom (sharp B).toNatAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem comparisonNat_tmul (B : Base (M := M)) (x : RESPositive B) (y : GammaPositive B) :
    comparisonNat B (x ⊗ₜ[ℕ] y) = ofRES B x * sharp B y := rfl

/-! ### Comparison with the chart rings -/

/-- Positive RES classes in the RES chart ring. -/
def resToRing (B : Base (M := M)) : RESPositive B →+* RESChartRing.Ring B := (resRelations B).lift {
  value x := RESChartRing.objectClass x.2
  iso := by
    rintro x y ⟨k,a,b,⟨F⟩,rfl,rfl⟩
    exact RESChartRing.objectClass_iso F
  unit := RESChartRing.objectClass_unit B
  product x y := RESChartRing.objectClass_product x.2 y.2
  empty := by
    rintro ⟨k,a⟩ h
    exact RESChartRing.objectClass_empty a h
  scissor := by
    rintro x y z w ⟨k,a,b,c,d,h,rfl,rfl,rfl,rfl⟩
    exact RESChartRing.objectClass_scissor a b c d h }

/-- Positive RV^db classes in the bounded RV chart ring. -/
def rvToRing (B : Base (M := M)) : RVPositive B →+* RVBoundedRing.Ring B := (rvRelations B).lift {
  value x := RVBoundedRing.objectClass x.2
  iso := by
    rintro x y ⟨k,a,b,⟨F⟩,rfl,rfl⟩
    exact RVBoundedRing.objectClass_iso F
  unit := RVBoundedRing.objectClass_unit B
  product x y := RVBoundedRing.objectClass_product x.2 y.2
  empty := by
    rintro ⟨k,a⟩ h
    exact RVBoundedRing.objectClass_empty a h
  scissor := by
    rintro x y z w ⟨k,a,b,c,d,h,rfl,rfl,rfl,rfl⟩
    exact RVBoundedRing.objectClass_scissor a b c d h }

/-- Positive Γ^db classes in the bounded Γ chart ring. -/
def gammaToRing (B : Base (M := M)) : GammaPositive B →+* GammaBoundedRVPresentation.ChartRing B :=
  (gammaRelations B).lift {
  value x := GammaBoundedRVPresentation.objectClass x.2
  iso := by
    rintro x y ⟨n,a,b,⟨F⟩,rfl,rfl⟩
    exact GammaBoundedRVPresentation.class_iso F
  unit := GammaBoundedRVPresentation.class_unit B
  product x y := GammaBoundedRVPresentation.class_product x.2 y.2
  empty := by
    rintro x ⟨n,μ,hμ,rfl⟩
    exact GammaBoundedRVPresentation.class_empty B n μ hμ
  scissor := by
    rintro x y z w ⟨n,I,J,hI,hJ,hbI,hbJ,hU,hN,μ,hμ,rfl,rfl,rfl,rfl⟩
    exact GammaBoundedRVPresentation.class_scissor B n I J hI hJ hbI hbJ hU hN μ hμ }

@[simp] theorem resToRing_cls (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    resToRing B ((resRelations B).cls ⟨k,a⟩) = RESChartRing.objectClass a :=
  (resRelations B).lift_cls _ _

@[simp] theorem rvToRing_cls (B : Base (M := M)) {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    rvToRing B ((rvRelations B).cls ⟨k,a⟩) = RVBoundedRing.objectClass a :=
  (rvRelations B).lift_cls _ _

@[simp] theorem gammaToRing_cls (B : Base (M := M)) {n : ℕ} (a : GammaBoundedRVCharts.BoundedChart B n) :
    gammaToRing B ((gammaRelations B).cls ⟨n,a⟩) = GammaBoundedRVPresentation.objectClass a :=
  (gammaRelations B).lift_cls _ _

theorem rvToRing_ofRES (B : Base (M := M)) :
    (rvToRing B).comp (ofRES B) = (RVBoundedMaps.ofRES B).comp (resToRing B) := by
  apply (resRelations B).hom_ext
  rintro ⟨k,a⟩
  change rvToRing B (ofRES B ((resRelations B).cls ⟨k,a⟩)) =
    RVBoundedMaps.ofRES B (resToRing B ((resRelations B).cls ⟨k,a⟩))
  rw [ofRES_cls,rvToRing_cls,resToRing_cls,RVBoundedMaps.ofRES_class]

theorem rvToRing_sharp (B : Base (M := M)) :
    (rvToRing B).comp (sharp B) = (GammaBoundedRVMaps.sharp B).comp (gammaToRing B) := by
  apply (gammaRelations B).hom_ext
  rintro ⟨n,a⟩
  change rvToRing B (sharp B ((gammaRelations B).cls ⟨n,a⟩)) =
    GammaBoundedRVMaps.sharp B (gammaToRing B ((gammaRelations B).cls ⟨n,a⟩))
  rw [sharp_cls,rvToRing_cls,gammaToRing_cls,GammaBoundedRVMaps.sharp_class]

/-- The ring-level bounded comparison of `RVBoundedBalancedTensor` is the
group completion of the positive one: on positive classes, the two agree. -/
theorem comparison_toRing (B : Base (M := M)) (x : RESPositive B) (y : GammaPositive B) :
    RVBoundedBalancedTensor.comparison B (resToRing B x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] gammaToRing B y) =
      rvToRing B (comparison B (x ⊗ₜ[FinitePositive B] y)) := by
  rw [RVBoundedBalancedTensor.comparison_tmul,comparison_tmul,map_mul]
  rw [← RingHom.comp_apply (rvToRing B) (ofRES B),rvToRing_ofRES,
    ← RingHom.comp_apply (rvToRing B) (sharp B),rvToRing_sharp]
  rfl

end DiamondIntegral.Section4.RVBoundedPositiveTensor
