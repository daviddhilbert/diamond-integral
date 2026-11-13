import «section 3».GammaGroundRVFamilyMaps

/-! A finite family of definable maps descends along the explicit RV
tagging bijection. The target may be an imaginary with many real codes. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {n : ℕ}
variable {Q : Space LRV M} (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)) (B : GammaGroundDefSet hc ground Q)

theorem gammaGroundRVFamilyDesc_graph_definable (f : ∀ i, GammaGroundMap (A.piece i) B) :
    GammaGroundRelationDefinable hc ground (rawRVSpace (A.tags + n)) Q
      (fun x y => ∃ a : A.Carrier, (A.rvEncode a).val = x ∧ (f a.1 a.2).val = y) := by
  have hd := GammaGroundRelationDefinable.exists_finite (fun i =>
    ((gammaGroundRVFamilyTagMap i (A.piece i)).relation_definable.symm).comp
      (f i).relation_definable)
  exact hd.congr (by
    intro x y
    constructor
    · rintro ⟨i, u, ⟨a, rfl, hx⟩, ⟨b, hb, hy⟩⟩
      have hb' : b = a := Subtype.ext hb
      subst b
      exact ⟨⟨i, a⟩, hx, hy⟩
    · rintro ⟨⟨i, a⟩, hx, hy⟩
      exact ⟨i, a.val, ⟨a, rfl, hx⟩, a, rfl, hy⟩)

def gammaGroundRVFamilyDesc (f : ∀ i, GammaGroundMap (A.piece i) B) : GammaGroundMap A.rvRealization B where
  toFun a := let c := A.rvEquiv.symm a; f c.1 c.2
  graph_definable := by
    change GammaGroundRelationDefinable hc ground (rawRVSpace (A.tags + n)) Q
      (fun x y => ∃ a : A.rvRealization, a.val = x ∧
        (f (A.rvEquiv.symm a).1 (A.rvEquiv.symm a).2).val = y)
    exact (gammaGroundRVFamilyDesc_graph_definable A B f).congr (by
      intro x y
      constructor
      · rintro ⟨a, hx, hy⟩
        refine ⟨A.rvEncode a, hx, ?_⟩
        change (f (A.rvEquiv.symm (A.rvEquiv a)).1 (A.rvEquiv.symm (A.rvEquiv a)).2).val = y
        rw [Equiv.symm_apply_apply]
        exact hy
      · rintro ⟨a, hx, hy⟩
        refine ⟨A.rvEquiv.symm a, ?_, hy⟩
        change (A.rvEquiv (A.rvEquiv.symm a)).val = x
        rw [Equiv.apply_symm_apply]
        exact hx)

@[simp] theorem gammaGroundRVFamilyDesc_encode (f : ∀ i, GammaGroundMap (A.piece i) B) (a : A.Carrier) :
    gammaGroundRVFamilyDesc A B f (A.rvEncode a) = f a.1 a.2 := by
  change f (A.rvEquiv.symm (A.rvEquiv a)).1 (A.rvEquiv.symm (A.rvEquiv a)).2 = _
  rw [Equiv.symm_apply_apply]

end DiamondIntegral.Section3
