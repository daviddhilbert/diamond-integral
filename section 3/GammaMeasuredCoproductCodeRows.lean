import «section 3».GammaMeasuredRVSyntax

/-! Each tagged coproduct density row is exactly the complete original
Gamma code row of that summand. No RV-function assertion is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaMeasuredRVSchema.coprod_rowDensity_left
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (G : GammaMeasuredRVSchema hc B p b (k+1) sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (x : Fin a → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
    (F.coprodFormula G).rowDensity z (@rvLeftTag M N hN a b x) c ↔ F.rowDensity z x c := by
  rw [show (F.coprodFormula G).rowDensity z (@rvLeftTag M N hN a b x) c ↔ _ from
    F.toRVTemplate.coprod_rowDensity G.toRVTemplate z hz _ (gammaVolumeCodeRV c)]
  constructor
  · rintro (⟨x',hd,he⟩|⟨y,hd,he⟩)
    · have hx : x' = x := @rvLeftTag_injective M N hN a b _ _ he
      exact hx ▸ hd
    · exact False.elim (@rvTag_disjoint M N hN a b x y he.symm)
  · intro hd
    exact Or.inl ⟨x,hd,rfl⟩

theorem GammaMeasuredRVSchema.coprod_rowDensity_right
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (G : GammaMeasuredRVSchema hc B p b (k+1) sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (x : Fin b → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
    (F.coprodFormula G).rowDensity z (@rvRightTag M N hN b a x) c ↔ G.rowDensity z x c := by
  rw [show (F.coprodFormula G).rowDensity z (@rvRightTag M N hN b a x) c ↔ _ from
    F.toRVTemplate.coprod_rowDensity G.toRVTemplate z hz _ (gammaVolumeCodeRV c)]
  constructor
  · rintro (⟨y,hd,he⟩|⟨x',hd,he⟩)
    · exact False.elim (@rvTag_disjoint M N hN a b y x he)
    · have hx : x' = x := @rvRightTag_injective M N hN b a _ _ he
      exact hx ▸ hd
  · intro hd
    exact Or.inr ⟨x,hd,rfl⟩

end DiamondIntegral.Section3
