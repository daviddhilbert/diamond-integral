import «section 3».GammaGroundFamilyTagMaps
import «section 3».GammaGroundCodePresentations
import «section 3».GammaGroundRawDescent
/-! Definability descends along full imaginary-code presentations. -/
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
variable {P Q : Space LRV M}

theorem gammaGroundFamilyDecode_definable (A : GammaGroundFiniteFamily hc ground P) : GammaGroundFamilyDefinable A.codeLift A A.decode :=
  gammaGroundFamilyTaggedMap_definable A.codeLift A (fun i => i) (fun i => gammaGroundCodeDecode (A.piece i))

theorem GammaGroundFamilyDefinable.descend {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q}
    {F : A.codeLift.Carrier → B.codeLift.Carrier} (hF : GammaGroundFamilyDefinable A.codeLift B.codeLift F)
    (f : A.Carrier → B.Carrier) (hf : ∀ c, B.decode (F c) = f (A.decode c)) : GammaGroundFamilyDefinable A B f := by
  intro i j
  have hg := (gammaGroundFamilyDecode_definable B).comp hF
  have hv : GammaGroundRelationDefinable hc ground (codeSpace P) Q
      (fun c y => gammaGroundFamilyGraph A B f i j (P.decode c) y) :=
    (hg i j).congr (by
      intro c y
      constructor
      · rintro ⟨a, b, ha, hb, he⟩
        refine ⟨gammaGroundCodeDecode (A.piece i) a, b, congrArg P.decode ha, hb, ?_⟩
        exact (hf ⟨i, a⟩).symm.trans he
      · rintro ⟨a, b, ha, hb, he⟩
        let ac : gammaGroundCodePreimage (A.piece i) := ⟨c, by
          change P.decode c ∈ (A.piece i).carrier
          exact ha ▸ a.property⟩
        have hac : gammaGroundCodeDecode (A.piece i) ac = a := Subtype.ext ha.symm
        refine ⟨ac, b, rfl, hb, ?_⟩
        exact (hf ⟨i, ac⟩).trans ((congrArg f (congrArg (Sigma.mk i) hac)).trans he))
  exact GammaGroundDefinable.of_real_codes hv.on_real_codes


def gammaGroundFamilyCodeRepresentative (A : GammaGroundFiniteFamily hc ground P) (a : A.Carrier) : A.codeLift.Carrier :=
  Classical.choose (A.decode_surjective a)

@[simp] theorem gammaGroundFamilyCodeRepresentative_spec (A : GammaGroundFiniteFamily hc ground P) (a : A.Carrier) :
    A.decode (gammaGroundFamilyCodeRepresentative A a) = a := Classical.choose_spec (A.decode_surjective a)

def gammaGroundFamilyDescendedMap {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q}
    (F : GammaGroundFamilyBijection A.codeLift B.codeLift) (a : A.Carrier) : B.Carrier :=
  B.decode (F.equiv (gammaGroundFamilyCodeRepresentative A a))

theorem gammaGroundFamilyDescendedMap_decode {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q}
    (F : GammaGroundFamilyBijection A.codeLift B.codeLift)
    (hF : ∀ c d, A.decode c = A.decode d → B.decode (F.equiv c) = B.decode (F.equiv d))
    (c : A.codeLift.Carrier) : gammaGroundFamilyDescendedMap F (A.decode c) = B.decode (F.equiv c) :=
  hF _ _ (gammaGroundFamilyCodeRepresentative_spec A (A.decode c))

def GammaGroundFamilyBijection.descend {A : GammaGroundFiniteFamily hc ground P} {B : GammaGroundFiniteFamily hc ground Q}
    (F : GammaGroundFamilyBijection A.codeLift B.codeLift)
    (hF : ∀ c d, A.decode c = A.decode d ↔ B.decode (F.equiv c) = B.decode (F.equiv d)) :
    GammaGroundFamilyBijection A B where
  equiv := Equiv.ofBijective (gammaGroundFamilyDescendedMap F) (by
    constructor
    · intro a b he
      have ht := (hF (gammaGroundFamilyCodeRepresentative A a) (gammaGroundFamilyCodeRepresentative A b)).mpr he
      simpa only [gammaGroundFamilyCodeRepresentative_spec] using ht
    · intro b
      obtain ⟨c, rfl⟩ := B.decode_surjective b
      refine ⟨A.decode (F.equiv.symm c), ?_⟩
      rw [gammaGroundFamilyDescendedMap_decode F (fun c d h => (hF c d).mp h), Equiv.apply_symm_apply])
  definable := F.definable.descend (gammaGroundFamilyDescendedMap F)
    (fun c => (gammaGroundFamilyDescendedMap_decode F (fun c d h => (hF c d).mp h) c).symm)

end DiamondIntegral.Section3
