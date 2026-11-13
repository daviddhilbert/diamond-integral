import «section 4».GammaOrdinarySharpObjects

/-! The sharp operation sends ordinary Gamma scissor squares to actual
ordinary RV scissor squares. This set-level result also applies inside
RES when the Gamma supports are finite. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinarySharpScissors
open GammaOrdinaryCharts GammaRVChartPresentation RVForgetScissors
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pack (n : ℕ) (u : Fin n → M) : Σ k : ℕ, Fin k → M := ⟨n, u⟩

theorem packedDomain_sharp {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    packedDomain (RVSharpCharts.sharpChart a) = pack n '' sharp a.support := by
  ext p
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.val, u.property, hu⟩
  · rintro ⟨u, hu, hp⟩
    exact ⟨⟨u, hu⟩, hp⟩

theorem sharp_scissor {B : Base (M := M)} {n : ℕ} (a b c d : Chart B n) (h : GammaOrdinaryRing.Scissor a b c d) :
    RVForgetScissors.Scissor (sharpChart a) (sharpChart b) (sharpChart c) (sharpChart d) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · have hu : sharp c.support = sharp a.support ∪ sharp b.support := by
      rw [h.1]
      ext z
      change (Proper z ∧ codeValues z ∈ a.support ∪ b.support) ↔ (Proper z ∧ codeValues z ∈ a.support) ∨ (Proper z ∧ codeValues z ∈ b.support)
      simp only [Set.mem_union]
      tauto
    change packedDomain (RVSharpCharts.sharpChart (toWeighted c)) =
      packedDomain (RVSharpCharts.sharpChart (toWeighted a)) ∪ packedDomain (RVSharpCharts.sharpChart (toWeighted b))
    rw [packedDomain_sharp, packedDomain_sharp, packedDomain_sharp]
    change pack n '' sharp c.support = pack n '' sharp a.support ∪ pack n '' sharp b.support
    rw [hu, Set.image_union]
  · have hi : sharp d.support = sharp a.support ∩ sharp b.support := by
      rw [h.2]
      ext z
      change (Proper z ∧ codeValues z ∈ a.support ∩ b.support) ↔ (Proper z ∧ codeValues z ∈ a.support) ∧ (Proper z ∧ codeValues z ∈ b.support)
      simp only [Set.mem_inter_iff]
      tauto
    change packedDomain (RVSharpCharts.sharpChart (toWeighted d)) =
      packedDomain (RVSharpCharts.sharpChart (toWeighted a)) ∩ packedDomain (RVSharpCharts.sharpChart (toWeighted b))
    rw [packedDomain_sharp, packedDomain_sharp, packedDomain_sharp]
    change pack n '' sharp d.support = pack n '' sharp a.support ∩ pack n '' sharp b.support
    rw [hi]
    have hinj : Set.InjOn (pack (M := M) n) Set.univ := by
      intro u hu v hv he
      exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact hinj.image_inter (Set.subset_univ _) (Set.subset_univ _)

end DiamondIntegral.Section4.GammaOrdinarySharpScissors
