import «section 3».FamilyTagMaps
import «section 3».CodePresentations

/-! Definability descends along full imaginary-code presentations. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P Q : Space L M}

theorem familyDecode_definable (A : FiniteFamily P S) : FamilyDefinable A.codeLift A A.decode :=
  familyTaggedMap_definable A.codeLift A (fun i => i) (fun i => codeDecode (A.piece i))

theorem FamilyDefinable.descend {A : FiniteFamily P S} {B : FiniteFamily Q S}
    {F : A.codeLift.Carrier → B.codeLift.Carrier} (hF : FamilyDefinable A.codeLift B.codeLift F)
    (f : A.Carrier → B.Carrier) (hf : ∀ c, B.decode (F c) = f (A.decode c)) : FamilyDefinable A B f := by
  intro i j
  have hg := (familyDecode_definable B).comp hF
  have hv : (codeSpace P).RelationDefinable Q S
      (fun c y => familyGraph A B f i j (P.decode c) y) :=
    (hg i j).congr (codeSpace P) Q (by
      intro c y
      constructor
      · rintro ⟨a, b, ha, hb, he⟩
        refine ⟨codeDecode (A.piece i) a, b, congrArg P.decode ha, hb, ?_⟩
        exact (hf ⟨i, a⟩).symm.trans he
      · rintro ⟨a, b, ha, hb, he⟩
        let ac : codePreimage (A.piece i) := ⟨c, by
          change P.decode c ∈ (A.piece i).carrier
          exact ha ▸ a.property⟩
        have hac : codeDecode (A.piece i) ac = a := Subtype.ext ha.symm
        refine ⟨ac, b, rfl, hb, ?_⟩
        exact (hf ⟨i, ac⟩).trans ((congrArg f (congrArg (Sigma.mk i) hac)).trans he))
  exact hv


def familyCodeRepresentative (A : FiniteFamily P S) (a : A.Carrier) : A.codeLift.Carrier :=
  Classical.choose (A.decode_surjective a)

@[simp] theorem familyCodeRepresentative_spec (A : FiniteFamily P S) (a : A.Carrier) :
    A.decode (familyCodeRepresentative A a) = a := Classical.choose_spec (A.decode_surjective a)

def familyDescendedMap {A : FiniteFamily P S} {B : FiniteFamily Q S}
    (F : FamilyBijection A.codeLift B.codeLift) (a : A.Carrier) : B.Carrier :=
  B.decode (F.equiv (familyCodeRepresentative A a))

theorem familyDescendedMap_decode {A : FiniteFamily P S} {B : FiniteFamily Q S}
    (F : FamilyBijection A.codeLift B.codeLift)
    (hF : ∀ c d, A.decode c = A.decode d → B.decode (F.equiv c) = B.decode (F.equiv d))
    (c : A.codeLift.Carrier) : familyDescendedMap F (A.decode c) = B.decode (F.equiv c) :=
  hF _ _ (familyCodeRepresentative_spec A (A.decode c))

def FamilyBijection.descend {A : FiniteFamily P S} {B : FiniteFamily Q S}
    (F : FamilyBijection A.codeLift B.codeLift)
    (hF : ∀ c d, A.decode c = A.decode d ↔ B.decode (F.equiv c) = B.decode (F.equiv d)) :
    FamilyBijection A B where
  equiv := Equiv.ofBijective (familyDescendedMap F) (by
    constructor
    · intro a b he
      have ht := (hF (familyCodeRepresentative A a) (familyCodeRepresentative A b)).mpr he
      simpa only [familyCodeRepresentative_spec] using ht
    · intro b
      obtain ⟨c, rfl⟩ := B.decode_surjective b
      refine ⟨A.decode (F.equiv.symm c), ?_⟩
      rw [familyDescendedMap_decode F (fun c d h => (hF c d).mp h), Equiv.apply_symm_apply])
  definable := F.definable.descend (familyDescendedMap F)
    (fun c => (familyDescendedMap_decode F (fun c d h => (hF c d).mp h) c).symm)

end DiamondIntegral.Section3
