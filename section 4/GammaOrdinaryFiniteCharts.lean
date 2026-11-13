import «section 4».GammaOrdinarySharpObjects
import «section 4».GammaFiniteRVCharts
import «section 4».RESOrdinaryRing

/-! Actual finite ordinary Gamma objects and their ordinary RES sharp
objects. All proper RV fibres are retained, with no chosen RV section. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteCharts
open GammaOrdinaryCharts GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ofSet (B : Base (M := M)) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hi : I.Finite) : FiniteChart B n :=
  ⟨GammaOrdinaryCharts.ofSet B n I hI, hi⟩
def ofMeasured {B : Base (M := M)} {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) : FiniteChart B n :=
  ⟨GammaOrdinaryCharts.ofWeighted a.toChart, a.finite_support⟩
def toWeighted {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : GammaFiniteRVCharts.FiniteChart B n :=
  ⟨GammaOrdinaryCharts.toWeighted a.toChart, a.finite_support⟩
def unit (B : Base (M := M)) : FiniteChart B 0 := ofMeasured (GammaFiniteRVCharts.unit B)
def product {B : Base (M := M)} {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) : FiniteChart B (n + m) :=
  ofMeasured (GammaFiniteRVCharts.product (toWeighted a) (toWeighted b))

theorem ofMeasured_toWeighted {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : ofMeasured (toWeighted a) = a := rfl

theorem ofMeasured_product {B : Base (M := M)} {n m : ℕ} (a : GammaFiniteRVCharts.FiniteChart B m) (b : GammaFiniteRVCharts.FiniteChart B n) :
    ofMeasured (GammaFiniteRVCharts.product a b) = product (ofMeasured a) (ofMeasured b) := rfl

theorem product_toChart {B : Base (M := M)} {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) :
    (product a b).toChart = GammaOrdinaryCharts.product a.toChart b.toChart := rfl

def sharp {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : RVMeasuredCharts.RESChart B n := GammaFiniteRVCharts.sharp (toWeighted a)

def sharpIso {B : Base (M := M)} {n : ℕ} {a b : FiniteChart B n} (f : GammaOrdinaryCharts.Iso a.toChart b.toChart) :
    RVForgetScissors.UnderlyingIso (sharp a).toChart (sharp b).toChart := GammaOrdinaryCharts.sharpIso f

theorem sharp_unit (B : Base (M := M)) : RESOrdinaryRing.objectClass (sharp (unit B)) = 1 :=
  (RESOrdinaryRing.objectClass_iso (RVForgetScissors.ofMeasured (GammaFiniteRVCharts.sharpUnitIso B))).trans (RESOrdinaryRing.objectClass_unit B)

theorem sharp_product {B : Base (M := M)} {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) :
    RESOrdinaryRing.objectClass (sharp (product a b)) = RESOrdinaryRing.objectClass (sharp a) * RESOrdinaryRing.objectClass (sharp b) := by
  have he := RESOrdinaryRing.objectClass_iso (a := sharp (product a b))
    (b := GammaFiniteRVCharts.sharp (GammaFiniteRVCharts.product (toWeighted a) (toWeighted b))) (GammaOrdinarySharpObjects.sameSupportIso
    (toWeighted (product a b)).toChart (GammaFiniteRVCharts.product (toWeighted a) (toWeighted b)).toChart rfl)
  exact he.trans ((RESOrdinaryRing.objectClass_iso (RVForgetScissors.ofMeasured
    (GammaFiniteRVCharts.sharpProductIso (toWeighted a) (toWeighted b)))).trans (RESOrdinaryRing.objectClass_product _ _))

end DiamondIntegral.Section4.GammaOrdinaryFiniteCharts
