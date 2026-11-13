import «section 3».RVFamilyMaps

/-! A genuine bijection of explicit tagged RV realizations gives a
definable bijection of the original finite families, with its full graph. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}
variable {A : FiniteFamily (rawRVSpace (M := M) k) S} {B : FiniteFamily (rawRVSpace (M := M) l) S}

def familyRealizationPullEquiv (F : DefinableBijection A.rvRealization B.rvRealization) : A.Carrier ≃ B.Carrier :=
  A.rvEquiv.trans ((Equiv.ofBijective F.map F.bijective).trans B.rvEquiv.symm)

theorem familyRealizationPullEquiv_apply_iff (F : DefinableBijection A.rvRealization B.rvRealization)
    (a : A.Carrier) (b : B.Carrier) :
    familyRealizationPullEquiv F a = b ↔ F.map (A.rvEncode a) = B.rvEncode b :=
  B.rvEquiv.symm_apply_eq

theorem familyRealizationPullEquiv_definable (F : DefinableBijection A.rvRealization B.rvRealization) :
    FamilyDefinable A B (familyRealizationPullEquiv F) := by
  intro i j
  let P := rawRVSpace (M := M) k
  let Q := rawRVSpace (M := M) l
  let PA := rawRVSpace (M := M) (A.tags + k)
  let PB := rawRVSpace (M := M) (B.tags + l)
  have hd := (((rvFamilyTagMap i (A.piece i)).graph_definable.comp P PA PB F.map.graph_definable).comp
    P PB Q ((rvFamilyTagMap j (B.piece j)).graph_definable.swap Q PB))
  exact hd.congr P Q (by
    intro t u
    constructor
    · rintro ⟨y, ⟨x, ⟨a, hat, hax⟩, ⟨p, hpx, hpy⟩⟩, ⟨b, hbu, hby⟩⟩
      have hp : p = A.rvEncode ⟨i, a⟩ := Subtype.ext (hpx.trans hax.symm)
      subst p
      have he : F.map (A.rvEncode ⟨i, a⟩) = B.rvEncode ⟨j, b⟩ := Subtype.ext (hpy.trans hby.symm)
      exact ⟨a, b, hat, hbu, (familyRealizationPullEquiv_apply_iff F _ _).mpr he⟩
    · rintro ⟨a, b, hat, hbu, he⟩
      have he' := (familyRealizationPullEquiv_apply_iff F _ _).mp he
      exact ⟨(B.rvEncode ⟨j, b⟩).val,
        ⟨(A.rvEncode ⟨i, a⟩).val, ⟨a, hat, rfl⟩,
          A.rvEncode ⟨i, a⟩, rfl, congrArg Subtype.val he'⟩,
        b, hbu, rfl⟩)

def FamilyBijection.ofRVRealization (F : DefinableBijection A.rvRealization B.rvRealization) : FamilyBijection A B :=
  ⟨familyRealizationPullEquiv F, familyRealizationPullEquiv_definable F⟩

@[simp] theorem FamilyBijection.ofRVRealization_encode (F : DefinableBijection A.rvRealization B.rvRealization)
    (a : A.Carrier) : B.rvEncode ((FamilyBijection.ofRVRealization F).equiv a) = F.map (A.rvEncode a) :=
  (familyRealizationPullEquiv_apply_iff F a _).mp rfl |>.symm

end DiamondIntegral.Section3
