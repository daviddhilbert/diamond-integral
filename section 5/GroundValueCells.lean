import «section 5».ValueInducedRectangles
import «section 3».GammaGroundRVFiniteValueFibres
import «section 3».GammaGroundFiniteCoverPartition

/-!
Actual original-ground definitions for the value-cell assembly of 5.12.
The ambient spaces are RV-unit tuples and Gamma tuples. No RV lift of an
active Gamma value is named. This file supplies the definability bridge;
the subsequent angular/global assembly remains separate.
-/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {n m N : ℕ}

def groundSupportPattern
    (G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (s : Finset (Fin N)) : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)) where
  carrier := {γ | ∀ i, γ ∈ (G i).carrier ↔ i ∈ s}
  definable := by
    let A := fun i => if i ∈ s then G i else (G i).compl
    have h := GammaGroundDefinable.iInter (fun i => (A i).definable)
    apply h.congr
    intro γ
    simp only [Set.mem_iInter]
    constructor
    · intro h i
      by_cases hi : i ∈ s
      · exact ⟨fun _ => hi, fun _ => by simpa [A, hi] using h i⟩
      · have hh : γ ∉ (G i).carrier := by simpa [A, hi, GammaGroundDefSet.compl] using h i
        exact ⟨fun hg => (hh hg).elim, fun hs => (hi hs).elim⟩
    · intro h i
      by_cases hi : i ∈ s
      · simpa [A, hi] using (h i).mpr hi
      · have hh : γ ∉ (G i).carrier := fun hg => hi ((h i).mp hg)
        simpa [A, hi, GammaGroundDefSet.compl] using hh

def groundResiduePattern
    (R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (β : Fin n → Values.Gamma (M := M))
    (hβ : ∀ i, GammaDefinableClosureAtBase B (β i)) (s : Finset (Fin N)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) where
  carrier := rectangleResidueCell rvUnitTupleValues (fun i => (R i).carrier) β s
  definable := by
    have h := GammaGroundDefinable.iUnion
      (fun i : s => (gammaGroundRVUnitValueFibre (R i.val) β hβ).definable)
    apply h.congr
    intro r
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hr, he⟩
      exact ⟨he, i.val, i.property, hr⟩
    · rintro ⟨he, i, hi, hr⟩
      exact ⟨⟨i, hi⟩, hr, he⟩

def groundMixedActiveMap
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m)))) :
    GammaGroundMap T (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
  (GammaGroundMap.ofGlobal (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
    (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp
      (GammaGroundMap.ofGlobal T (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))
        (universalProductFst _ _ B.real) (fun _ => Set.mem_univ _))

def groundMixedValueMap
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m)))) :=
  (groundMixedActiveMap T).pair
    (GammaGroundMap.ofGlobal T
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
      (universalProductSnd _ _ B.real) (fun _ => Set.mem_univ _))

theorem groundMixedValueMap_image
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m)))) :
    (groundMixedValueMap T).image.carrier = Prod.map rvUnitTupleValues id '' T.carrier := by
  ext q
  exact ⟨fun ⟨x, hx⟩ => ⟨x.val, x.property, hx⟩,
    fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩

def groundValuePattern
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m))))
    (G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (β : Fin n → Values.Gamma (M := M))
    (hβ : ∀ i, GammaDefinableClosureAtBase B (β i)) (s : Finset (Fin N)) :=
  (groundMixedValueMap T).image.inter
    ((⟨{β}, gammaGroundGammaPower_predicate_definable _
      (fullGamma_tuple_singleton_definable β hβ)⟩ :
      GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))).prod
      (groundSupportPattern G s))

theorem groundValuePattern_carrier
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod
      ((volumeGammaSpace hc).power (Fin m))))
    (G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (β : Fin n → Values.Gamma (M := M))
    (hβ : ∀ i, GammaDefinableClosureAtBase B (β i)) (s : Finset (Fin N)) :
    (groundValuePattern T G β hβ s).carrier =
      rectangleValueCell rvUnitTupleValues id T.carrier (fun i => (G i).carrier) β s := by
  ext q
  change (q ∈ (groundMixedValueMap T).image.carrier ∧
    q.1 ∈ ({β} : Set (Fin n → Values.Gamma (M := M))) ∧
    ∀ i, q.2 ∈ (G i).carrier ↔ i ∈ s) ↔ _
  rw [groundMixedValueMap_image]
  rfl

end DiamondIntegral.Section5
