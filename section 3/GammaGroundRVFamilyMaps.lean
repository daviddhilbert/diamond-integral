import «section 3».GammaGroundRVFamilyRealization
import «section 3».GammaGroundMapRelations

/-! Definable maps on finite tagged families give genuine definable maps
on their RV realizations. This includes bijections, with no new parameters. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {n m : ℕ}
variable {A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)}
variable {B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) m)}

theorem GammaGroundFamilyDefinable.rvRealization {f : A.Carrier → B.Carrier} (hf : GammaGroundFamilyDefinable A B f) :
    GammaGroundRelationDefinable hc ground (rawRVSpace (A.tags + n)) (rawRVSpace (B.tags + m))
      (fun x y => ∃ a : A.Carrier, (A.rvEncode a).val = x ∧ (B.rvEncode (f a)).val = y) := by
  let PA := rawRVSpace (M := M) (A.tags + n)
  let PB := rawRVSpace (M := M) (B.tags + m)
  let P := rawRVSpace (M := M) n
  let Q := rawRVSpace (M := M) m
  have hd := GammaGroundRelationDefinable.exists_finite (fun i =>
    GammaGroundRelationDefinable.exists_finite (fun j =>
      (((gammaGroundRVFamilyTagMap i (A.piece i)).relation_definable.symm).comp (hf i j)).comp
        (gammaGroundRVFamilyTagMap j (B.piece j)).relation_definable))
  exact hd.congr (by
    intro x y
    constructor
    · rintro ⟨i, j, v, ⟨u, ⟨a, rfl, hx⟩, ⟨a', b, ha, rfl, he⟩⟩, ⟨b', hb, hy⟩⟩
      have ha' : a' = a := Subtype.ext ha
      have hb' : b' = b := Subtype.ext hb
      subst a'
      subst b'
      refine ⟨⟨i, a⟩, hx, ?_⟩
      rw [he]
      exact hy
    · rintro ⟨a, hx, hy⟩
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b, he⟩ : ∃ j b, f ⟨i, a⟩ = ⟨j, b⟩ := ⟨_, _, rfl⟩
      refine ⟨i, j, b.val, ⟨a.val, ⟨a, rfl, hx⟩, a, b, rfl, rfl, he⟩, b, rfl, ?_⟩
      rw [he] at hy
      exact hy)

def gammaGroundRVFamilyMap (f : A.Carrier → B.Carrier) (hf : GammaGroundFamilyDefinable A B f) :
    GammaGroundMap A.rvRealization B.rvRealization where
  toFun a := B.rvEncode (f (A.rvEquiv.symm a))
  graph_definable := by
    change GammaGroundRelationDefinable hc ground (rawRVSpace (A.tags + n)) (rawRVSpace (B.tags + m))
      (fun x y => ∃ a : A.rvRealization, a.val = x ∧ (B.rvEncode (f (A.rvEquiv.symm a))).val = y)
    exact (hf.rvRealization).congr (by
      intro x y
      constructor
      · rintro ⟨a, hx, hy⟩
        refine ⟨A.rvEncode a, hx, ?_⟩
        change (B.rvEncode (f (A.rvEquiv.symm (A.rvEncode a)))).val = y
        rw [show A.rvEncode a = A.rvEquiv a from rfl, Equiv.symm_apply_apply]
        exact hy
      · rintro ⟨a, hx, hy⟩
        refine ⟨A.rvEquiv.symm a, ?_, hy⟩
        change (A.rvEquiv (A.rvEquiv.symm a)).val = x
        rw [Equiv.apply_symm_apply]
        exact hx)

@[simp] theorem gammaGroundRVFamilyMap_encode (f : A.Carrier → B.Carrier) (hf : GammaGroundFamilyDefinable A B f)
    (a : A.Carrier) : gammaGroundRVFamilyMap f hf (A.rvEncode a) = B.rvEncode (f a) := by
  change B.rvEncode (f (A.rvEquiv.symm (A.rvEquiv a))) = _
  rw [Equiv.symm_apply_apply]

def GammaGroundFamilyBijection.rvRealization (f : GammaGroundFamilyBijection A B) :
    GammaGroundBijection A.rvRealization B.rvRealization where
  map := gammaGroundRVFamilyMap f.equiv f.definable
  bijective := B.rvEquiv.bijective.comp (f.equiv.bijective.comp A.rvEquiv.symm.bijective)

end DiamondIntegral.Section3
