import «section 3».GammaGroundEssentialVFComposition

/-! Equality of the maps on independent points is exactly agreement
outside a Gamma-ground definable set of smaller manuscript VF dimension. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3.GammaGroundEssentialVFMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

theorem genericEquiv_id :
    (GammaGroundEssentialVFMap.id A).genericEquiv hκ hs hS hv hn = Equiv.refl (GammaGroundGeneric A) := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem genericEquiv_symm (f : GammaGroundEssentialVFMap A B) :
    f.symm.genericEquiv hκ hs hS hv hn = (f.genericEquiv hκ hs hS hv hn).symm := by
  apply Equiv.ext
  intro a
  rfl

theorem genericEquiv_eq_iff (f g : GammaGroundEssentialVFMap A B) :
    f.genericEquiv hκ hs hS hv hn = g.genericEquiv hκ hs hS hv hn ↔
      ∃ E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r),
        Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ) ∧
        ∀ x ∈ E.carrier, ∃ (p : f.source) (q : g.source),
          p.val = x ∧ q.val = x ∧ (f.map p).val = (g.map q).val := by
  constructor
  · intro he
    let D := {x | ∃ y, (∃ p : f.source, p.val = x ∧ (f.map p).val = y) ∧
      (∃ q : g.source, q.val = x ∧ (g.map q).val = y)}
    have hD : GammaGroundDefinable hc ground (rawMixedSpace (M := M) n r) D := by
      apply ((f.map.graph_definable.inter g.map.graph_definable).image
        (universalProductFst _ _ ground.real)).congr
      intro x
      constructor
      · rintro ⟨z, ⟨hp, hq⟩, hx⟩
        exact ⟨z.2, hx ▸ hp, hx ▸ hq⟩
      · rintro ⟨y, hp, hq⟩
        exact ⟨(x, y), ⟨hp, hq⟩, rfl⟩
    let E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r) := ⟨D, hD⟩
    refine ⟨E, gammaGround_small_complement_of_generic A E hκ hs hS hv hn ?_, ?_⟩
    · intro a
      let p : f.source := ⟨a.val.val,
        gammaGround_mem_of_small_complement f.source hκ hs hS hv hn f.source_small a⟩
      let q : g.source := ⟨a.val.val,
        gammaGround_mem_of_small_complement g.source hκ hs hS hv hn g.source_small a⟩
      have heq : (f.map p).val = (g.map q).val :=
        congrArg (fun e : GammaGroundGeneric A ≃ GammaGroundGeneric B => (e a).val.val) he
      exact ⟨(f.map p).val, ⟨p, rfl, rfl⟩, ⟨q, rfl, heq.symm⟩⟩
    · rintro x ⟨y, ⟨p, hp, hf⟩, ⟨q, hq, hg⟩⟩
      exact ⟨p, q, hp, hq, hf.trans hg.symm⟩
  · rintro ⟨E, hE, he⟩
    apply Equiv.ext
    intro a
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨p, q, hp, hq, h⟩ := he a.val.val
      (gammaGround_mem_of_small_complement E hκ hs hS hv hn hE a)
    exact (congrArg (fun p : f.source => (f.map p).val) (Subtype.ext hp.symm)).trans
      (h.trans (congrArg (fun q : g.source => (g.map q).val) (Subtype.ext hq)))

end DiamondIntegral.Section3.GammaGroundEssentialVFMap
