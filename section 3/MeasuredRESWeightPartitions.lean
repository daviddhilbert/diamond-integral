import «section 3».RESGammaWeightFiniteness
import «section 3».MeasuredDegreeZeroWeightScalars
import «section 3».GammaGroundEqualizers
import «section 3».GammaGroundMeasuredRVFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r : ℕ}

def gammaGroundMeasuredRESWeightFibre (X : GammaGroundMeasuredRESObject hc B r)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) :=
  X.obj.combinedWeightForm.equalizer (gammaGroundConstantForm X.obj.underlying.domain δ hδ)

theorem gammaGroundMeasuredRESWeightFibre_mem (X : GammaGroundMeasuredRESObject hc B r)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (x : (rawRVSpace X.obj.underlying.arity).Carrier) :
    x ∈ (gammaGroundMeasuredRESWeightFibre X δ hδ).carrier ↔
      ∃ a : X.obj.underlying.domain, a.val = x ∧ X.obj.combinedWeight a = δ := by
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,(X.obj.combinedWeightForm_value a).symm.trans he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,(X.obj.combinedWeightForm_value a).trans he⟩

/-- Finite disjoint measured RES restrictions preserve the positive
class and every original label and form. -/
theorem gammaGroundMeasuredRESDirectSumClass_finite_partition {ι : Type} [Fintype ι]
    (X : GammaGroundMeasuredRESObject hc B r)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.obj.underlying.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundMeasuredRESDirectSumClass X = ∑ i,
      gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hh : gammaGroundMeasuredRESClass X = ∑ i,
      gammaGroundMeasuredRESClass (X.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
    apply gammaGroundMeasuredRESToRVKPlus_injective
    simpa only [map_sum,gammaGroundMeasuredRESToRVKPlus_class,GammaGroundMeasuredRESObject.restrict] using
      gammaGroundMeasuredRVClass_finite_partition X.obj A hd hcov
  have h := congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) r) hh
  simpa only [gammaGroundMeasuredRESDirectSumClass,map_sum] using h

/-- An arbitrary measured RES coefficient has a finite original-ground
partition into coefficients of constant combined weight. -/
theorem gammaGroundMeasuredRES_constant_weight_partition {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (X : GammaGroundMeasuredRESObject hc B r) :
    ∃ N : ℕ, ∃ δ : Fin N → Values.Gamma (M := M),
      ∃ Q : Fin N → GammaGroundDefSet hc B (rawRVSpace X.obj.underlying.arity),
      (∀ i, GammaDefinableClosureAtBase B (δ i)) ∧
      (∀ i, (Q i).carrier ⊆ X.obj.underlying.domain.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (Q i).carrier (Q j).carrier) ∧
      (∀ x, x ∈ X.obj.underlying.domain.carrier ↔ ∃ i, x ∈ (Q i).carrier) ∧
        ∀ i (a : X.obj.underlying.domain), a.val ∈ (Q i).carrier → X.obj.combinedWeight a = δ i := by
  obtain ⟨hfin,hn⟩ := gammaGroundMeasuredRES_combined_weight_finite_named hκ hs h00 hsmall hγsmall X
  let D := Set.range X.obj.combinedWeight
  let : Fintype D := hfin.fintype
  let e := (Fintype.equivFin D).symm
  let δ := fun i => (e i).val
  have hd (i) : GammaDefinableClosureAtBase B (δ i) := by
    obtain ⟨a,ha⟩ := (e i).property
    change GammaDefinableClosureAtBase B (e i).val
    exact ha ▸ hn a
  let Q := fun i => gammaGroundMeasuredRESWeightFibre X (δ i) (hd i)
  refine ⟨Fintype.card D,δ,Q,hd,?_,?_,?_,?_⟩
  · intro i
    exact X.obj.combinedWeightForm.equalizer_subset _
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,hax⟩ := (gammaGroundMeasuredRESWeightFibre_mem X (δ i) (hd i) x).mp hx
    obtain ⟨b,hb,hbx⟩ := (gammaGroundMeasuredRESWeightFibre_mem X (δ j) (hd j) x).mp hy
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    have he : δ i = δ j := hax.symm.trans ((congrArg X.obj.combinedWeight hab).trans hbx)
    exact hij (e.injective (Subtype.ext he))
  · intro x
    constructor
    · intro hx
      let a : X.obj.underlying.domain := ⟨x,hx⟩
      let v : D := ⟨X.obj.combinedWeight a,Set.mem_range_self a⟩
      obtain ⟨i,hi⟩ := e.surjective v
      refine ⟨i,(gammaGroundMeasuredRESWeightFibre_mem X (δ i) (hd i) x).mpr ⟨a,rfl,?_⟩⟩
      exact (congrArg Subtype.val hi).symm
    · rintro ⟨i,hi⟩
      exact X.obj.combinedWeightForm.equalizer_subset _ hi
  · intro i a ha
    obtain ⟨b,hb,he⟩ := (gammaGroundMeasuredRESWeightFibre_mem X (δ i) (hd i) a.val).mp ha
    have hab : b = a := Subtype.ext hb
    exact (congrArg X.obj.combinedWeight hab).symm.trans he
end DiamondIntegral.Section3
