import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions.SumProd

/-!
# The projective line with its two affine charts

The topology is final for the ordinary affine chart and the reciprocal
chart. It uses the field's given topology and requires no local compactness.
The carrier wraps Option so it cannot inherit Option's disjoint-sum topology.
-/

set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace DiamondIntegral.Section2

structure ProjectiveLine (K : Type*) where
  point : Option K

namespace ProjectiveLine
variable {K : Type*} [Field K]

def finite (x : K) : ProjectiveLine K := ⟨some x⟩
def infinity : ProjectiveLine K := ⟨none⟩

noncomputable def reciprocalChart (x : K) : ProjectiveLine K := by
  classical
  exact if x = 0 then infinity else finite x⁻¹

noncomputable def reciprocal (p : ProjectiveLine K) : ProjectiveLine K :=
  match p.point with
  | none => finite 0
  | some x => reciprocalChart x

theorem finite_injective : Function.Injective (finite (K := K)) := by
  intro x y h
  exact Option.some.inj (congrArg ProjectiveLine.point h)

@[simp] theorem reciprocal_finite (x : K) : reciprocal (finite x) = reciprocalChart x := rfl

@[simp] theorem reciprocal_reciprocalChart (x : K) : reciprocal (reciprocalChart x) = finite x := by
  classical
  by_cases hx : x = 0 <;> simp [reciprocalChart,reciprocal,hx,finite,infinity]

theorem reciprocal_involutive : Function.Involutive (reciprocal (K := K)) := by
  rintro ⟨p⟩
  cases p with
  | none => simp [reciprocal,reciprocalChart,infinity,finite]
  | some x => exact reciprocal_reciprocalChart x

private noncomputable def atlas : K ⊕ K → ProjectiveLine K := Sum.elim finite reciprocalChart

noncomputable instance topology [TopologicalSpace K] : TopologicalSpace (ProjectiveLine K) :=
  TopologicalSpace.coinduced atlas inferInstance

variable [TopologicalSpace K]

theorem isOpen_iff_charts (U : Set (ProjectiveLine K)) :
    IsOpen U ↔ IsOpen (finite ⁻¹' U) ∧ IsOpen (reciprocalChart ⁻¹' U) := by
  change IsOpen (atlas ⁻¹' U) ↔ _
  rw [isOpen_sum_iff]
  rfl

theorem continuous_finite : Continuous (finite (K := K)) :=
  continuous_def.mpr (fun U hU => ((isOpen_iff_charts U).mp hU).1)

theorem continuous_reciprocalChart : Continuous (reciprocalChart (K := K)) :=
  continuous_def.mpr (fun U hU => ((isOpen_iff_charts U).mp hU).2)

theorem continuous_reciprocal : Continuous (reciprocal (K := K)) := by
  apply continuous_def.mpr
  intro U hU
  obtain ⟨h0,h1⟩ := (isOpen_iff_charts U).mp hU
  apply (isOpen_iff_charts _).mpr
  constructor
  · exact h1
  · have he : reciprocalChart ⁻¹' (reciprocal ⁻¹' U) = finite ⁻¹' U := by
      ext x
      change reciprocal (reciprocalChart x) ∈ U ↔ finite x ∈ U
      rw [reciprocal_reciprocalChart]
    exact he.symm ▸ h0

noncomputable def reciprocalHomeomorph : ProjectiveLine K ≃ₜ ProjectiveLine K where
  toFun := reciprocal
  invFun := reciprocal
  left_inv := reciprocal_involutive
  right_inv := reciprocal_involutive
  continuous_toFun := continuous_reciprocal
  continuous_invFun := continuous_reciprocal

variable [T1Space K] [ContinuousInv₀ K]

theorem isOpenMap_finite : IsOpenMap (finite (K := K)) := by
  intro U hU
  apply (isOpen_iff_charts _).mpr
  constructor
  · simpa only [Set.preimage_image_eq _ finite_injective] using hU
  · have he : reciprocalChart ⁻¹' (finite '' U) = ({(0 : K)}ᶜ ∩ (Inv.inv : K → K) ⁻¹' U) := by
      ext x
      classical
      by_cases hx : x = 0
      · subst x
        simp [reciprocalChart,infinity,finite]
      · simp [reciprocalChart,hx,finite,Set.mem_image]
    rw [he]
    exact continuousOn_inv₀.isOpen_inter_preimage isClosed_singleton.isOpen_compl hU

theorem isOpenEmbedding_finite : IsOpenEmbedding (finite (K := K)) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_finite finite_injective isOpenMap_finite

theorem isOpenEmbedding_reciprocalChart : IsOpenEmbedding (reciprocalChart (K := K)) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_reciprocalChart
  · intro x y h
    apply finite_injective
    have he := congrArg reciprocal h
    rwa [reciprocal_reciprocalChart,reciprocal_reciprocalChart] at he
  · change IsOpenMap (reciprocal ∘ finite)
    exact (reciprocalHomeomorph (K := K)).isOpenMap.comp (isOpenMap_finite (K := K))

end ProjectiveLine
end DiamondIntegral.Section2
