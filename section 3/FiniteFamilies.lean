import «section 3».DefinableBijections
import Section4.Products

/-! Finite disjoint unions retain their tags. Definability of a map means
definability of every branch of its complete graph. Composition quantifies
over the finitely many intermediate tags, without choosing real codes. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M}
variable {P Q R : Space L M}

structure FiniteFamily (P : Space L M) (S : Set M) where
  tags : ℕ
  piece : Fin tags → DefSet P S

def FiniteFamily.Carrier (A : FiniteFamily P S) := Σ i, A.piece i

def familyGraph (A : FiniteFamily P S) (B : FiniteFamily Q S)
    (f : A.Carrier → B.Carrier) (i : Fin A.tags) (j : Fin B.tags)
    (x : P.Carrier) (y : Q.Carrier) : Prop :=
  ∃ a : A.piece i, ∃ b : B.piece j, a.val = x ∧ b.val = y ∧ f ⟨i, a⟩ = ⟨j, b⟩

def FamilyDefinable (A : FiniteFamily P S) (B : FiniteFamily Q S)
    (f : A.Carrier → B.Carrier) : Prop :=
  ∀ i j, P.RelationDefinable Q S (familyGraph A B f i j)

theorem relationDefinable_exists_finite {ι : Type} [Finite ι]
    {T : ι → P.Carrier → Q.Carrier → Prop}
    (h : ∀ i, P.RelationDefinable Q S (T i)) :
    P.RelationDefinable Q S (fun x y => ∃ i, T i x y) := by
  have hd := Set.definable_iUnion_of_finite h
  change S.Definable L _
  convert hd using 1
  ext z
  simp only [Space.relation, Set.mem_setOf_eq, Set.mem_iUnion]
  aesop

theorem FamilyDefinable.id (A : FiniteFamily P S) : FamilyDefinable A A id := by
  classical
  intro i j
  by_cases he : i = j
  · subst j
    exact (Map.id (A.piece i)).graph_definable.congr P P (by
      intro x y
      simp only [Map.graph, Map.id, familyGraph, id_eq]
      constructor
      · rintro ⟨a, rfl, rfl⟩
        exact ⟨a, a, rfl, rfl, rfl⟩
      · rintro ⟨a, b, rfl, rfl, hab⟩
        have hab' : a = b := by
          change (⟨i, a⟩ : Σ i, A.piece i) = ⟨i, b⟩ at hab
          simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
        exact ⟨a, rfl, congrArg Subtype.val hab'⟩)
  · have hd : P.RelationDefinable P S (fun _ _ => False) := by
      change S.Definable L _
      simpa [Space.relation] using
        (Set.definable_empty : S.Definable L (∅ : Set (P.Index ⊕ P.Index → M)))
    exact hd.congr P P (by
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a, b, _, _, hab⟩
        exact he (congrArg Sigma.fst hab))

theorem FamilyDefinable.comp {A : FiniteFamily P S} {B : FiniteFamily Q S}
    {D : FiniteFamily R S} {f : A.Carrier → B.Carrier} {g : B.Carrier → D.Carrier}
    (hg : FamilyDefinable B D g) (hf : FamilyDefinable A B f) :
    FamilyDefinable A D (g ∘ f) := by
  intro i k
  have hd := relationDefinable_exists_finite (fun j => (hf i j).comp P Q R (hg j k))
  exact hd.congr P R (by
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

structure FamilyBijection (A : FiniteFamily P S) (B : FiniteFamily Q S) where
  equiv : A.Carrier ≃ B.Carrier
  definable : FamilyDefinable A B equiv

namespace FamilyBijection
variable {A : FiniteFamily P S} {B : FiniteFamily Q S} {D : FiniteFamily R S}

@[ext] theorem ext {f g : FamilyBijection A B} (h : f.equiv = g.equiv) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : FiniteFamily P S) : FamilyBijection A A :=
  ⟨Equiv.refl _, FamilyDefinable.id A⟩

def comp (g : FamilyBijection B D) (f : FamilyBijection A B) : FamilyBijection A D :=
  ⟨f.equiv.trans g.equiv, g.definable.comp f.definable⟩

def symm (f : FamilyBijection A B) : FamilyBijection B A where
  equiv := f.equiv.symm
  definable i j := (f.definable j i).swap P Q |>.congr Q P (by
    intro y x
    constructor
    · rintro ⟨a, b, rfl, rfl, he⟩
      exact ⟨b, a, rfl, rfl, f.equiv.symm_apply_eq.mpr he.symm⟩
    · rintro ⟨b, a, rfl, rfl, he⟩
      exact ⟨a, b, rfl, rfl, f.equiv.apply_eq_iff_eq_symm_apply.mpr he.symm⟩)

end FamilyBijection
end DiamondIntegral.Section3
