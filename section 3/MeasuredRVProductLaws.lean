import «section 3».MeasuredRVProducts
import Section4.RVProductAssociativity
import Section4.RVProductUnits

/-! Coordinate reindexing and the actual pointwise measured cartesian
associativity, symmetry and unit bijections. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l j n : ℕ}

def RVObject.reindexVolume (U : RVObject (M := M) S k) (e : Fin n ≃ Fin k) :
    RVObject S n where
  arity := U.arity
  domain := U.domain
  volume := (rvReindexMap S e).comp U.volume
  finite := Map.finiteFibres_of_injective (rvReindexMap_bijective S e).1 |>.comp U.finite
  nonzero a i := U.nonzero a (e i)

def MeasuredRVObject.reindexVolume (U : MeasuredRVObject (M := M) S k)
    (e : Fin n ≃ Fin k) : MeasuredRVObject S n :=
  ⟨U.underlying.reindexVolume e, { toFun := U.form.toFun, graph := U.form.graph, graph_spec := U.form.graph_spec }⟩

@[simp] theorem MeasuredRVObject.reindex_combinedWeight
    (U : MeasuredRVObject (M := M) S k) (e : Fin n ≃ Fin k) (a : U.underlying.domain) :
    (U.reindexVolume e).combinedWeight a = U.combinedWeight a := by
  unfold MeasuredRVObject.combinedWeight
  change U.form.toFun a * (∏ i, Section2.rvFiniteValue (U.underlying.target a (e i))) = _
  exact congrArg (fun t : Section2.Gamma M => U.form.toFun a * t)
    (e.prod_comp (fun i => Section2.rvFiniteValue (U.underlying.target a i)))

@[simp] theorem MeasuredRVObject.product_combined_pair
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l)
    (a : U.underlying.domain) (b : V.underlying.domain) :
    (U.product hc V).combinedWeight (rvPackPair U.underlying.domain V.underlying.domain a b) =
      U.combinedWeight a * V.combinedWeight b := by
  rw [MeasuredRVObject.product_combinedWeight]
  simp only [rvProductLeft, rvProductRight, Map.comp_apply, rvUnpack_pair]
  rfl

def measuredRVProductAssocHom (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l)
    (W : MeasuredRVObject (M := M) S j) :
    MeasuredRVHom ((U.product hc V).product hc W)
      ((U.product hc (V.product hc W)).reindexVolume (finCongr (Nat.add_assoc k l j))) where
  bijection := ⟨rvProductAssocMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj
    W.underlying.toCompanion.obj, rvProductAssocMap_bijective _ _ _⟩
  preserves p := by
    obtain ⟨ab, c, rfl⟩ := exists_rvPackPair (U.product hc V).underlying.domain W.underlying.domain p
    obtain ⟨a, b, rfl⟩ := exists_rvPackPair U.underlying.domain V.underlying.domain ab
    rw [MeasuredRVObject.reindex_combinedWeight]
    change _ = (U.product hc (V.product hc W)).combinedWeight
      (rvProductAssocMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj W.underlying.toCompanion.obj _)
    have he := rvProductAssocMap_pair U.underlying.toCompanion.obj V.underlying.toCompanion.obj
      W.underlying.toCompanion.obj a b c
    calc
      _ = (U.combinedWeight a * V.combinedWeight b) * W.combinedWeight c := by
        simp only [MeasuredRVObject.product_combined_pair]
      _ = U.combinedWeight a * (V.combinedWeight b * W.combinedWeight c) := mul_assoc _ _ _
      _ = (U.product hc (V.product hc W)).combinedWeight
          (rvPackPair U.underlying.domain (V.product hc W).underlying.domain a
            (rvPackPair V.underlying.domain W.underlying.domain b c)) := by
        simp only [MeasuredRVObject.product_combined_pair]
      _ = _ := congrArg (U.product hc (V.product hc W)).combinedWeight he.symm

theorem rvProductSwapMap_pair (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (a : U.domain) (b : V.domain) :
    rvProductSwapMap U.toCompanion.obj V.toCompanion.obj (rvPackPair U.domain V.domain a b) =
      rvPackPair V.domain U.domain b a := by
  apply (rvUnpack_bijective V.domain U.domain).1
  change rvUnpack V.toCompanion.obj.domain U.toCompanion.obj.domain
    (rvProductSwapMap U.toCompanion.obj V.toCompanion.obj
      (rvPackPair U.toCompanion.obj.domain V.toCompanion.obj.domain a b)) = _
  rw [rvProductSwapMap_unpack, rvUnpack_pair, rvUnpack_pair]
  rfl

def measuredRVProductCommHom (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l) :
    MeasuredRVHom (U.product hc V)
      ((V.product hc U).reindexVolume (finAddFlip : Fin (k + l) ≃ Fin (l + k))) where
  bijection := ⟨rvProductSwapMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj,
    rvProductSwapMap_bijective _ _⟩
  preserves p := by
    obtain ⟨a, b, rfl⟩ := exists_rvPackPair U.underlying.domain V.underlying.domain p
    rw [MeasuredRVObject.reindex_combinedWeight, rvProductSwapMap_pair]
    simp only [MeasuredRVObject.product_combined_pair]
    exact mul_comm _ _

@[simp] theorem MeasuredRVObject.unit_combinedWeight
    (hc : CanonicalStructure.IsCanonical (M := M)) (a : (MeasuredRVObject.unit hc S).underlying.domain) :
    (MeasuredRVObject.unit hc S).combinedWeight a = 1 := by
  simp [MeasuredRVObject.combinedWeight, MeasuredRVObject.unit]

def measuredRVProductRightUnitHom (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) :
    MeasuredRVHom (U.product hc (MeasuredRVObject.unit hc S)) U where
  bijection := ⟨rvProductRightUnitMap U.underlying.toCompanion.obj,
    rvProductRightUnitMap_bijective _⟩
  preserves p := by
    rw [MeasuredRVObject.product_combinedWeight, MeasuredRVObject.unit_combinedWeight, mul_one]
    rfl

end DiamondIntegral.Section3
