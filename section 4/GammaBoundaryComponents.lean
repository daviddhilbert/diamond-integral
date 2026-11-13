import «section 4».GammaBoundaryConstancy
import «section 4».GammaCellUnboundedSections

/-! Boundary-free open bands, rays and lines in a definable Gamma fibre
have constant membership. A single member of such a component makes the
whole component part of the original set. These are semantic statements,
prior to assembling a finite cylindrical decomposition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryComponents
open GammaOrderLogic GammaBoundaryConstancy GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) {n : ℕ}
variable (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
include h00 hR

theorem mem_iff_on_upperRay (y : Fin n → Values.Gamma (M := M)) (a : Values.Gamma (M := M))
    (hno : ∀ t, a < t → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (x z : Values.Gamma (M := M)) (hx : a < x) (hz : a < z) :
    Fin.cons x y ∈ R ↔ Fin.cons z y ∈ R := by
  rcases le_total x z with hxz | hzx
  · exact mem_iff_of_no_boundary_between h00 B R hR y x z hxz
      (fun t hxt _ => hno t (hx.trans_le hxt))
  · exact (mem_iff_of_no_boundary_between h00 B R hR y z x hzx
      (fun t hzt _ => hno t (hz.trans_le hzt))).symm

theorem mem_iff_on_lowerRay (y : Fin n → Values.Gamma (M := M)) (a : Values.Gamma (M := M))
    (hno : ∀ t, t < a → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (x z : Values.Gamma (M := M)) (hx : x < a) (hz : z < a) :
    Fin.cons x y ∈ R ↔ Fin.cons z y ∈ R := by
  rcases le_total x z with hxz | hzx
  · exact mem_iff_of_no_boundary_between h00 B R hR y x z hxz
      (fun t _ htz => hno t (htz.trans_lt hz))
  · exact (mem_iff_of_no_boundary_between h00 B R hR y z x hzx
      (fun t _ htx => hno t (htx.trans_lt hx))).symm

theorem mem_iff_on_line (y : Fin n → Values.Gamma (M := M))
    (hno : ∀ t, Fin.cons t y ∉ GammaFamilyBoundary.Boundary R) (x z : Values.Gamma (M := M)) :
    Fin.cons x y ∈ R ↔ Fin.cons z y ∈ R := by
  rcases le_total x z with hxz | hzx
  · exact mem_iff_of_no_boundary_between h00 B R hR y x z hxz (fun t _ _ => hno t)
  · exact (mem_iff_of_no_boundary_between h00 B R hR y z x hzx (fun t _ _ => hno t)).symm

theorem band_subset (C : Set (Fin n → Values.Gamma (M := M)))
    (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hno : ∀ y ∈ C, ∀ t, l y < t → t < u y → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (hex : ∀ y ∈ C, ∃ t, l y < t ∧ t < u y ∧ Fin.cons t y ∈ R) : bandCell C l u ⊆ R := by
  intro z hz
  obtain ⟨t, hlt, htu, htR⟩ := hex (Fin.tail z) hz.1
  have he := mem_iff_on_open_interval h00 B R hR (Fin.tail z) (l (Fin.tail z)) (u (Fin.tail z))
    (hno (Fin.tail z) hz.1) t (z 0) ⟨hlt, htu⟩ hz.2
  have hr := he.mp htR
  simpa only [Fin.cons_self_tail] using hr

theorem upperRay_subset (C : Set (Fin n → Values.Gamma (M := M)))
    (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hno : ∀ y ∈ C, ∀ t, l y < t → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (hex : ∀ y ∈ C, ∃ t, l y < t ∧ Fin.cons t y ∈ R) : upperRayCell C l ⊆ R := by
  intro z hz
  obtain ⟨t, hlt, htR⟩ := hex (Fin.tail z) hz.1
  have hr := (mem_iff_on_upperRay h00 B R hR (Fin.tail z) (l (Fin.tail z))
    (hno (Fin.tail z) hz.1) t (z 0) hlt hz.2).mp htR
  simpa only [Fin.cons_self_tail] using hr

theorem lowerRay_subset (C : Set (Fin n → Values.Gamma (M := M)))
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hno : ∀ y ∈ C, ∀ t, t < u y → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (hex : ∀ y ∈ C, ∃ t, t < u y ∧ Fin.cons t y ∈ R) : lowerRayCell C u ⊆ R := by
  intro z hz
  obtain ⟨t, htu, htR⟩ := hex (Fin.tail z) hz.1
  have hr := (mem_iff_on_lowerRay h00 B R hR (Fin.tail z) (u (Fin.tail z))
    (hno (Fin.tail z) hz.1) t (z 0) htu hz.2).mp htR
  simpa only [Fin.cons_self_tail] using hr

theorem line_subset (C : Set (Fin n → Values.Gamma (M := M)))
    (hno : ∀ y ∈ C, ∀ t, Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (hex : ∀ y ∈ C, ∃ t, Fin.cons t y ∈ R) : lineCell C ⊆ R := by
  intro z hz
  obtain ⟨t, htR⟩ := hex (Fin.tail z) hz
  have hr := (mem_iff_on_line h00 B R hR (Fin.tail z) (hno (Fin.tail z) hz) t (z 0)).mp htR
  simpa only [Fin.cons_self_tail] using hr

end DiamondIntegral.Section4.GammaBoundaryComponents
