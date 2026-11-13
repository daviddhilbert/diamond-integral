import «section 3».FiniteFamilies
import «section 3».CarrierBijections

/-! Definable finite-family maps with a prescribed tag map, including
actual tag permutations and disjoint unions. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P Q : Space L M}

def FiniteFamily.coprod (A B : FiniteFamily P S) : FiniteFamily P S :=
  ⟨A.tags + B.tags, Fin.addCases A.piece B.piece⟩

def familyTaggedMap (A : FiniteFamily P S) (B : FiniteFamily Q S)
    (h : Fin A.tags → Fin B.tags) (f : ∀ i, Map (A.piece i) (B.piece (h i))) : A.Carrier → B.Carrier :=
  fun a => ⟨h a.1, f a.1 a.2⟩

theorem familyTaggedMap_definable (A : FiniteFamily P S) (B : FiniteFamily Q S)
    (h : Fin A.tags → Fin B.tags) (f : ∀ i, Map (A.piece i) (B.piece (h i))) :
    FamilyDefinable A B (familyTaggedMap A B h f) := by
  classical
  intro i j
  by_cases he : h i = j
  · subst j
    exact (f i).graph_definable.congr P Q (by
      intro x y
      constructor
      · rintro ⟨a, rfl, hy⟩
        exact ⟨a, f i a, rfl, hy, rfl⟩
      · rintro ⟨a, b, rfl, rfl, hab⟩
        have hfb : f i a = b := eq_of_heq (Sigma.mk.inj_iff.mp hab).2
        exact ⟨a, rfl, congrArg Subtype.val hfb⟩)
  · have hd : P.RelationDefinable Q S (fun _ _ => False) := by
      change S.Definable L _
      simpa [Space.relation] using
        (Set.definable_empty : S.Definable L (∅ : Set (P.Index ⊕ Q.Index → M)))
    exact hd.congr P Q (by
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a, b, _, _, hab⟩
        exact he (congrArg Sigma.fst hab))

def familyBijectionOfTagEquiv (A : FiniteFamily P S) (B : FiniteFamily Q S)
    (e : Fin A.tags ≃ Fin B.tags) (f : ∀ i, DefinableBijection (A.piece i) (B.piece (e i))) :
    FamilyBijection A B where
  equiv := (Equiv.sigmaCongrRight (fun i => Equiv.ofBijective (f i).map (f i).bijective)).trans
    (Equiv.sigmaCongrLeft (β := fun j => B.piece j) e)
  definable := familyTaggedMap_definable A B e (fun i => (f i).map)

@[simp] theorem familyBijectionOfTagEquiv_apply (A : FiniteFamily P S) (B : FiniteFamily Q S)
    (e : Fin A.tags ≃ Fin B.tags) (f : ∀ i, DefinableBijection (A.piece i) (B.piece (e i))) (a : A.Carrier) :
    (familyBijectionOfTagEquiv A B e f).equiv a = ⟨e a.1, (f a.1).map a.2⟩ := rfl

end DiamondIntegral.Section3
