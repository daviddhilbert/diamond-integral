import «section 4».GammaRVIdentityIso
import «section 4».RVForgetScissors
import «section 4».GammaBoundedProducts

/-! Actual Gamma objects without volume forms and their original-base
RV-contracted bijections. Unlike measured Gamma morphisms, these impose
no volume equation. Their full proper RV preimages have actual ordinary
RV bijections induced by the supplied lift. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryCharts
open GammaOrderLogic GammaDefinableMaps GammaRVChartPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Chart (B : Base (M := M)) (n : ℕ) where
  support : Set (Fin n → Values.Gamma (M := M))
  support_definable : GammaDefinable B support

def ofSet (B : Base (M := M)) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) : Chart B n := ⟨I, hI⟩

def ofWeighted {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n) : Chart B n := ⟨a.support, a.support_definable⟩

def toWeighted {B : Base (M := M)} {n : ℕ} (a : Chart B n) : GammaWeightedCharts.Chart B n :=
  GammaChartOperations.ofTotal B n a.support a.support_definable (fun _ => 1)
    (constant_definable B 1 (GammaGroupNames.one_definable_base B))

theorem ofWeighted_toWeighted {B : Base (M := M)} {n : ℕ} (a : Chart B n) : ofWeighted (toWeighted a) = a := rfl

def unit (B : Base (M := M)) : Chart B 0 := ofWeighted (GammaChartOperations.unit B)
def product {B : Base (M := M)} {n m : ℕ} (a : Chart B m) (b : Chart B n) : Chart B (n + m) :=
  ofWeighted (GammaChartOperations.product (toWeighted a) (toWeighted b))
def empty (B : Base (M := M)) (n : ℕ) : Chart B n := ofSet B n ∅ (GammaIntegerFamilies.empty_definable_base B n)
def union {B : Base (M := M)} {n : ℕ} (a b : Chart B n) : Chart B n :=
  ofSet B n (a.support ∪ b.support) (GammaQuantifierLogic.union_definable_base B _ _ a.support_definable b.support_definable)
def inter {B : Base (M := M)} {n : ℕ} (a b : Chart B n) : Chart B n :=
  ofSet B n (a.support ∩ b.support) (GammaRelationLogic.inter_definable_base B _ _ a.support_definable b.support_definable)

theorem ofWeighted_product {B : Base (M := M)} {n m : ℕ} (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n) :
    ofWeighted (GammaChartOperations.product a b) = product (ofWeighted a) (ofWeighted b) := rfl

structure Iso {B : Base (M := M)} {n : ℕ} (a b : Chart B n) where
  map : (Fin n → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M))
  graph_definable : GammaDefinable B (GammaBijectiveRelations.graphOn a.support map)
  bijective : Set.BijOn map a.support b.support
  lift : (Fin n → M) → (Fin n → M)
  lift_definable : DefinableOverBase B (fun _ : Fin (n + n) => .rv) (rawGraphOn a.support lift)
  lift_bijective : Set.BijOn lift (sharp a.support) (sharp b.support)
  contraction : ∀ z ∈ sharp a.support, codeValues (lift z) = map (codeValues z)

def ofMeasured {B : Base (M := M)} {n : ℕ} {a b : GammaWeightedCharts.Chart B n} (f : RVVolumeIso a b) : Iso (ofWeighted a) (ofWeighted b) where
  map := f.map
  graph_definable := f.graph_definable
  bijective := f.bijective
  lift := f.lift
  lift_definable := f.lift_definable
  lift_bijective := f.lift_bijective
  contraction := f.contraction

def sameSupportIso {B : Base (M := M)} {n : ℕ} (a b : Chart B n) (h : a.support = b.support) : Iso a b :=
  ofMeasured (GammaRVIdentityIso.sameDomainIso (toWeighted a) (toWeighted b) h (fun _ _ => rfl))

def sharpChart {B : Base (M := M)} {n : ℕ} (a : Chart B n) : RVMeasuredCharts.Chart B n := RVSharpCharts.sharpChart (toWeighted a)

def sharpIso {B : Base (M := M)} {n : ℕ} {a b : Chart B n} (f : Iso a b) :
    RVForgetScissors.UnderlyingIso (sharpChart a) (sharpChart b) := by
  apply RVForgetScissors.ofMap (sharpChart a) (sharpChart b) f.lift
  · change DefinableOverBase B (fun _ : Fin (n + n) => .rv) (RVMeasuredCharts.graphOn (sharp a.support) f.lift)
    have he : RVMeasuredCharts.graphOn (sharp a.support) f.lift = rawGraphOn a.support f.lift := by
      ext w
      change (_ ∧ _ = _) ↔ (_ ∧ _ = _)
      exact and_congr_right (fun _ => eq_comm)
    rw [he]
    exact f.lift_definable
  · exact f.lift_bijective

structure BoundedChart (B : Base (M := M)) (n : ℕ) extends Chart B n where
  domain_bounded : GammaBoundedProducts.DomainBounded support

structure FiniteChart (B : Base (M := M)) (n : ℕ) extends Chart B n where
  finite_support : support.Finite

end DiamondIntegral.Section4.GammaOrdinaryCharts
