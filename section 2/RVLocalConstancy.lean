import «section 2».Conventions
import Section8.RVFibreGeneric

/-!
# Generic constancy of the output RV labels

This connects actual single-valued VF-to-RV-infinity maps to the companion
library's local-constancy theorem for whole RV fibres. It imposes no topology
on RV and preserves all output labels, including the zero tag. The generic
dimension conclusion has the explicit real-base, canonical-model and
saturation hypotheses of the reused theorem.
-/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

/-- The full graph on actual typed VF and RV coordinates. -/
def rvFunctionGraph (f : (Fin n → VF M) → Fin m → RVInfinity M) :
    Set (Fin n ⊕ Fin m → M) :=
  {z | ∃ a : Fin n → VF M, vfValues a = z ∘ Sum.inl ∧
    rvValues (f a) = z ∘ Sum.inr}

omit hM in
@[simp] theorem rvFunctionGraph_fibre
    (f : (Fin n → VF M) → Fin m → RVInfinity M) (a : Fin n → VF M) :
    rvFibre (rvFunctionGraph f) a = {f a} := by
  ext t
  change (∃ x : Fin n → VF M, vfValues x = vfValues a ∧
    rvValues (f x) = rvValues t) ↔ t = f a
  constructor
  · rintro ⟨x, hx, ht⟩
    have he : x = a := funext (fun i => Subtype.ext (congrFun hx i))
    subst x
    exact (funext (fun i => Subtype.ext (congrFun ht i))).symm
  · rintro rfl
    exact ⟨a, rfl, rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section Topological

/-- Local constancy concerns the VF input topology and equality of RV labels. -/
def RVFunctionLocallyConstantAt (f : (Fin n → VF M) → Fin m → RVInfinity M)
    (a : Fin n → VF M) : Prop :=
  ∃ U, IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, f b = f a

theorem rvFunctionLocallyConstantAt_iff_fibre
    (f : (Fin n → VF M) → Fin m → RVInfinity M) (a : Fin n → VF M) :
    RVFunctionLocallyConstantAt f a ↔
      rvLocallyConstantAt (rvFibre (rvFunctionGraph f)) a := by
  constructor
  · rintro ⟨U, hU, ha, h⟩
    refine ⟨U, hU, ha, fun b hb => ?_⟩
    simp only [rvFunctionGraph_fibre, h b hb]
  · rintro ⟨U, hU, ha, h⟩
    refine ⟨U, hU, ha, fun b hb => ?_⟩
    exact Set.singleton_injective (by simpa only [rvFunctionGraph_fibre] using h b hb)

theorem rvFunctionLocallyConstant_zero_arity
    (f : (Fin 0 → VF M) → Fin m → RVInfinity M) (a : Fin 0 → VF M) :
    RVFunctionLocallyConstantAt f a :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ _,
    fun b _ => congrArg f (Subsingleton.elim b a)⟩

end Topological

theorem rvFunction_locallyConstant_of_independent
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (f : (Fin n → VF M) → Fin m → RVInfinity M)
    (hf : S.Definable LRV (rvFunctionGraph f))
    (a : Fin n → VF M) (ha : AlgebraicIndependent (vfParameterField S) a) :
    RVFunctionLocallyConstantAt f a :=
  (rvFunctionLocallyConstantAt_iff_fibre f a).mpr
    (rvFibre_locallyConstant_of_independent hc hv hf a ha)

/-- One definable open locus covers all generic inputs. The dimension is
the companion library's VF dimension, with all source and target RV labels
retained in the graph; no inference from one large fibre is used. -/
theorem rvFunction_locallyConstant_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hn : 0 < n)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF M) → Fin m → RVInfinity M)
    (hf : S.Definable LRV (rvFunctionGraph f)) :
    ∃ U : Set (Fin n → M), ∃ hU : S.Definable LRV U,
      U ⊆ vfRawUniverse n ∧
      vfDim (rawRVSpace (M := M) 1)
        (vfObjectOfRaw ((vfRawUniverse_definable S n).inter hU.compl)) < n ∧
      IsOpen {a : Fin n → VF M | vfValues a ∈ U} ∧
      ∀ a : Fin n → VF M, vfValues a ∈ U → RVFunctionLocallyConstantAt f a := by
  obtain ⟨U, hU, hsort, hdim, hopen, hloc⟩ :=
    lemma_8_9_canonical hc hs hsmall hn hv hf
  exact ⟨U, hU, hsort, hdim, hopen,
    fun a ha => (rvFunctionLocallyConstantAt_iff_fibre f a).mpr (hloc a ha)⟩

end DiamondIntegral.Section2
