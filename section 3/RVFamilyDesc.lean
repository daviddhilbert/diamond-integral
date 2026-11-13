import «section 3».RVFamilyMaps

/-! A finite family of definable maps descends along the explicit RV
tagging bijection. The target may be an imaginary with many real codes. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {Q : Space LRV M} (A : FiniteFamily (rawRVSpace (M := M) n) S) (B : DefSet Q S)

theorem rvFamilyDesc_graph_definable (f : ∀ i, Map (A.piece i) B) :
    (rawRVSpace (A.tags + n)).RelationDefinable Q S
      (fun x y => ∃ a : A.Carrier, (A.rvEncode a).val = x ∧ (f a.1 a.2).val = y) := by
  have hd := relationDefinable_exists_finite (fun i =>
    ((rvFamilyTagMap i (A.piece i)).graph_definable.swap (rawRVSpace n) (rawRVSpace (A.tags + n))).comp
      (rawRVSpace (A.tags + n)) (rawRVSpace n) Q (f i).graph_definable)
  exact hd.congr _ _ (by
    intro x y
    constructor
    · rintro ⟨i, u, ⟨a, rfl, hx⟩, ⟨b, hb, hy⟩⟩
      have hb' : b = a := Subtype.ext hb
      subst b
      exact ⟨⟨i, a⟩, hx, hy⟩
    · rintro ⟨⟨i, a⟩, hx, hy⟩
      exact ⟨i, a.val, ⟨a, rfl, hx⟩, a, rfl, hy⟩)

def rvFamilyDesc (f : ∀ i, Map (A.piece i) B) : Map A.rvRealization B where
  toFun a := let c := A.rvEquiv.symm a; f c.1 c.2
  graph_definable := (rvFamilyDesc_graph_definable A B f).congr _ _ (by
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

@[simp] theorem rvFamilyDesc_encode (f : ∀ i, Map (A.piece i) B) (a : A.Carrier) :
    rvFamilyDesc A B f (A.rvEncode a) = f a.1 a.2 := by
  change f (A.rvEquiv.symm (A.rvEquiv a)).1 (A.rvEquiv.symm (A.rvEquiv a)).2 = _
  rw [Equiv.symm_apply_apply]

end DiamondIntegral.Section3
