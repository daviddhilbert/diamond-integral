import «section 4».GammaBoundedRVCharts

/-! Every finite Gamma domain is doubly bounded in every finite arity,
without Archimedean assumptions or definable RV lifts. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteBounds
open GammaBoundedProducts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem finite_domain_bounded {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : I.Finite) :
    DomainBounded I := by
  let S : Set (Values.Gamma (M := M)) := ⋃ z ∈ I, Set.range z
  have hS : S.Finite := hI.biUnion (fun z _ => Set.finite_range z)
  obtain ⟨l, hl⟩ := hS.bddBelow
  obtain ⟨b, hb⟩ := hS.bddAbove
  refine ⟨max b l⁻¹, ?_⟩
  intro z hz i
  have hm : z i ∈ S := Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, Set.mem_range_self i⟩⟩
  have hi : (max b l⁻¹)⁻¹ ≤ l := by
    simpa only [inv_inv] using inv_le_inv_iff.mpr (le_max_right b l⁻¹)
  exact ⟨hi.trans (hl hm), (hb hm).trans (le_max_left b l⁻¹)⟩

theorem singleton_bounded {n : ℕ} (α : Fin n → Values.Gamma (M := M)) :
    DomainBounded ({α} : Set (Fin n → Values.Gamma (M := M))) := finite_domain_bounded _ (Set.finite_singleton α)

def boundedChart {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n) (ha : a.support.Finite) :
    GammaBoundedRVCharts.BoundedChart B n := ⟨a, finite_domain_bounded a.support ha⟩

end DiamondIntegral.Section4.GammaFiniteBounds
