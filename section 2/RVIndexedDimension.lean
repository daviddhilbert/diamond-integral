import «section 2».Conventions
import Section4.VFDimensionFibres
import Section4.CoordinateMaps

/-!
# RV-indexed families do not raise VF dimension

The author identifies this as the dimension principle behind the original
proof of 2.44. The companion's Lemma 4.3 proves the maximum-fibre equality
for actual definable maps to RV-coded spaces. These corollaries retain its
canonical-model, genuine saturation and original-base smallness hypotheses.
The dimension here is the companion's finite-map VF dimension; no unproved
identification with the section's direct interior-based dimension is used.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_indexed_dimension_le
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} {Q : Space LRV M} (hQ : Q.RVCoded)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet Q S}
    (f : Map A B) (k : ℕ)
    (hfibre : ∀ b : B, ∀ c : Q.domain, ∀ he : Q.decode c = b.val,
      vfDim Δ (f.fibre b c he) ≤ k) :
    vfDim Δ A ≤ k := by
  rw [SpecialTransformations.Section4.lemma_4_3 hc hκ hs hsmall Δ hΔ hQ f]
  exact ciSup_le' (fun p => hfibre p.1 p.2.val p.2.property)

/-- The strict bound includes empty families when the threshold is positive. -/
theorem rv_indexed_dimension_lt
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} {Q : Space LRV M} (hQ : Q.RVCoded)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet Q S}
    (f : Map A B) (k : ℕ) (hk : 0 < k)
    (hfibre : ∀ b : B, ∀ c : Q.domain, ∀ he : Q.decode c = b.val,
      vfDim Δ (f.fibre b c he) < k) :
    vfDim Δ A < k := by
  have hle := rv_indexed_dimension_le hc hκ hs hsmall Δ hΔ hQ f (k-1)
    (fun b c he => Nat.le_sub_one_of_lt (hfibre b c he))
  exact hle.trans_lt (Nat.sub_lt hk (by decide))

/-- Projecting the family, in particular forgetting its RV labels to take
the union of its VF fibres, preserves the strict dimension bound. -/
theorem rv_indexed_image_dimension_lt
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    {n r m s : ℕ} {Q : Space LRV M} (hQ : Q.RVCoded)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet Q S}
    {C : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) (g : Map A C) (k : ℕ) (hk : 0 < k)
    (hfibre : ∀ b : B, ∀ c : Q.domain, ∀ he : Q.decode c = b.val,
      vfDim Δ (f.fibre b c he) < k) :
    vfDim Δ g.image < k :=
  (vfDim_image_le hc hs hsmall Δ hΔ g).trans_lt
    (rv_indexed_dimension_lt hc hκ hs hsmall Δ hΔ hQ f k hk hfibre)

end DiamondIntegral.Section2
