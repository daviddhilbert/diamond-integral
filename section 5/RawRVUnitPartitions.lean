import «section 5».NativeRVSetValues
import «section 3».GammaGroundBijectionRestrictions

/-! Actual RV partitions and their native values transport through
original-ground bijections, including raw/nonzero RV presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem groundBijection_inverseImage_at {P Q : Space LRV M}
    {X : GammaGroundDefSet hc B P} {Y : GammaGroundDefSet hc B Q}
    (e : GammaGroundBijection X Y) (A : GammaGroundDefSet hc B Q) (x : X) :
    x.val ∈ (e.inverseImage A).carrier ↔ (e.map x).val ∈ A.carrier := by
  constructor
  · rintro ⟨a,ha,hm⟩
    have he : a = x := Subtype.ext ha
    rw [he] at hm
    exact hm
  · intro hm
    exact ⟨x,rfl,hm⟩

theorem groundBijection_pullback_partition {P Q : Space LRV M}
    {X : GammaGroundDefSet hc B P} {Y : GammaGroundDefSet hc B Q}
    (e : GammaGroundBijection X Y) {ι : Type} [Fintype ι] (A : ι → GammaGroundDefSet hc B Q)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ y, y ∈ Y.carrier ↔ ∃ i, y ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint (e.inverseImage (A i)).carrier (e.inverseImage (A j)).carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (e.inverseImage (A i)).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,hi⟩ ⟨b,hb,hj⟩
    have he : b = a := Subtype.ext (hb.trans ha.symm)
    rw [he] at hj
    exact Set.disjoint_left.mp (hd i j hij) hi hj
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (hcov (e.map ⟨x,hx⟩).val).mp (e.map ⟨x,hx⟩).property
      exact ⟨i,⟨x,hx⟩,rfl,hi⟩
    · rintro ⟨i,a,ha,_⟩
      exact ha ▸ a.property

theorem nativeRVSetValue_raw_unit_bijection
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {p q : ℕ} (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) q)) (e : GammaGroundBijection X Y) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind Y :=
  nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    ((gammaGroundRVUnitPresentationBijection Y).comp e)

end DiamondIntegral.Section5
