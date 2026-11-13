import «section 3».GammaGroundRelations
import «section 3».GammaGroundMapRestrictions

/-! Finite disjoint unions retain their tags. Definability of a map means
definability of every branch of its complete graph. Composition quantifies
over the finitely many intermediate tags, without choosing real codes. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q R : Space LRV M}

structure GammaGroundFiniteFamily (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (P : Space LRV M) where
  tags : ℕ
  piece : Fin tags → GammaGroundDefSet hc ground P

def GammaGroundFiniteFamily.Carrier (A : GammaGroundFiniteFamily hc ground P) := Σ i, A.piece i

def gammaGroundFamilyGraph (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q)
    (f : A.Carrier → B.Carrier) (i : Fin A.tags) (j : Fin B.tags)
    (x : P.Carrier) (y : Q.Carrier) : Prop :=
  ∃ a : A.piece i, ∃ b : B.piece j, a.val = x ∧ b.val = y ∧ f ⟨i, a⟩ = ⟨j, b⟩

def GammaGroundFamilyDefinable (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q)
    (f : A.Carrier → B.Carrier) : Prop :=
  ∀ i j, GammaGroundRelationDefinable hc ground P Q (gammaGroundFamilyGraph A B f i j)

theorem GammaGroundFamilyDefinable.id (A : GammaGroundFiniteFamily hc ground P) : GammaGroundFamilyDefinable A A id := by
  classical
  intro i j
  by_cases he : i = j
  · subst j
    have hd : GammaGroundRelationDefinable hc ground P P
        (fun x y => ∃ a : A.piece i, a.val = x ∧ a.val = y) := (GammaGroundMap.id (A.piece i)).graph_definable
    exact GammaGroundRelationDefinable.congr hd (by
      intro x y
      simp only [GammaGroundMap.id, gammaGroundFamilyGraph, id_eq]
      constructor
      · rintro ⟨a, rfl, rfl⟩
        exact ⟨a, a, rfl, rfl, rfl⟩
      · rintro ⟨a, b, rfl, rfl, hab⟩
        have hab' : a = b := by
          change (⟨i, a⟩ : Σ i, A.piece i) = ⟨i, b⟩ at hab
          simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
        exact ⟨a, rfl, congrArg Subtype.val hab'⟩)
  · have hd : GammaGroundRelationDefinable hc ground P P (fun _ _ => False) := by
      exact (GammaGroundDefSet.empty hc ground (P.prod P)).definable
    exact GammaGroundRelationDefinable.congr hd (by
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a, b, _, _, hab⟩
        exact he (congrArg Sigma.fst hab))

theorem GammaGroundFamilyDefinable.comp {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q}
    {D : GammaGroundFiniteFamily hc ground R} {f : A.Carrier → B.Carrier} {g : B.Carrier → D.Carrier}
    (hg : GammaGroundFamilyDefinable B D g) (hf : GammaGroundFamilyDefinable A B f) :
    GammaGroundFamilyDefinable A D (g ∘ f) := by
  intro i k
  have hd := GammaGroundRelationDefinable.exists_finite (fun j => (hf i j).comp (hg j k))
  exact GammaGroundRelationDefinable.congr hd (by
    intro x z
    constructor
    · rintro ⟨j, y, ⟨a, b, rfl, rfl, hab⟩, ⟨b', c, hb, rfl, hbc⟩⟩
      have hb' : b' = b := Subtype.ext hb
      subst b'
      exact ⟨a, c, rfl, rfl, by change g (f _) = _; rw [hab]; exact hbc⟩
    · rintro ⟨a, c, rfl, rfl, hac⟩
      obtain ⟨j, b, hfb⟩ : ∃ j b, f ⟨i, a⟩ = ⟨j, b⟩ := ⟨_, _, rfl⟩
      refine ⟨j, b.val, ⟨a, b, rfl, rfl, hfb⟩, b, c, rfl, rfl, ?_⟩
      exact (congrArg g hfb).symm.trans hac)

structure GammaGroundFamilyBijection (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q) where
  equiv : A.Carrier ≃ B.Carrier
  definable : GammaGroundFamilyDefinable A B equiv

namespace GammaGroundFamilyBijection
variable {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q} {D : GammaGroundFiniteFamily hc ground R}

@[ext] theorem ext {f g : GammaGroundFamilyBijection A B} (h : f.equiv = g.equiv) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : GammaGroundFiniteFamily hc ground P) : GammaGroundFamilyBijection A A :=
  ⟨Equiv.refl _, GammaGroundFamilyDefinable.id A⟩

def comp (g : GammaGroundFamilyBijection B D) (f : GammaGroundFamilyBijection A B) : GammaGroundFamilyBijection A D :=
  ⟨f.equiv.trans g.equiv, g.definable.comp f.definable⟩

def symm (f : GammaGroundFamilyBijection A B) : GammaGroundFamilyBijection B A where
  equiv := f.equiv.symm
  definable i j := (f.definable j i).symm |>.congr (by
    intro y x
    constructor
    · rintro ⟨a, b, rfl, rfl, he⟩
      exact ⟨b, a, rfl, rfl, f.equiv.symm_apply_eq.mpr he.symm⟩
    · rintro ⟨b, a, rfl, rfl, he⟩
      exact ⟨a, b, rfl, rfl, f.equiv.apply_eq_iff_eq_symm_apply.mpr he.symm⟩)

end GammaGroundFamilyBijection
end DiamondIntegral.Section3
