import «section 3».GoodGammaRows
import «section 3».ResidueTupleGammaClosure
import «section 3».GammaAlgebraicFinite
import «section 3».IntegrationGammaParameters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ} {sn : Fin n → SortTag}

def goodGammaImage (G : GoodBaseGammaRelation B n sn) (A : Set (Fin n → M)) :
    Set (Values.Gamma (M := M)) := {δ | ∃ a ∈ A, δ ∈ gammaRow G.carrier a}

theorem goodGammaImage_definable (G : GoodBaseGammaRelation B n sn)
    (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A) :
    GammaDefinableOverBase B (goodGammaImage G A) := by
  let π : Fin (n+1) → Fin 1 ⊕ Fin n := Fin.lastCases (Sum.inl 0) Sum.inr
  have he (z : Fin 1 ⊕ Fin n → M) : (Fin.init (z ∘ π),(z ∘ π) (Fin.last n)) =
      (z ∘ Sum.inr,z (Sum.inl 0)) := by
    apply Prod.ext
    · funext i
      simp only [Fin.init,Function.comp_apply,π,Fin.lastCases_castSucc]
    · simp only [Function.comp_apply,π,Fin.lastCases_last]
  have hg : FullBaseAtomicity.OverBase (integrationGammaBase B)
      {z : Fin 1 ⊕ Fin n → M | (z ∘ Sum.inr,z (Sum.inl 0)) ∈ G.carrier} := by
    have hh := FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable G.definable) π
    convert hh using 1
    ext z
    change ((z ∘ Sum.inr,z (Sum.inl 0)) ∈ G.carrier) ↔
      ((Fin.init (z ∘ π),(z ∘ π) (Fin.last n)) ∈ G.carrier)
    rw [he]
  have hp := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hg
    (FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hA) (Sum.inr : Fin n → Fin 1 ⊕ Fin n)))
  have hfull : FullGammaSyntax.Scalar (integrationGammaBase B) (goodGammaImage G A) := by
    change FullBaseAtomicity.OverBase (integrationGammaBase B)
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (goodGammaImage G A)}
    convert hp using 1
    ext z
    change (z 0 ∈ Values.gammaPullback (goodGammaImage G A)) ↔ _
    rw [GammaSyntax.mem_gammaPullback_iff]
    change (NonzeroRV (z 0) ∧ ∃ a ∈ A, codeValue (z 0) ∈ gammaRow G.carrier a) ↔
      ∃ a : Fin n → M, (a,z 0) ∈ G.carrier ∧ a ∈ A
    constructor
    · rintro ⟨hn,a,ha,hγ⟩
      exact ⟨a,(goodGammaRow_mem_code_iff G a (z 0) hn).mp hγ,ha⟩
    · rintro ⟨a,hg,ha⟩
      have hn := G.proper a (z 0) hg
      exact ⟨hn,a,ha,(goodGammaRow_mem_code_iff G a (z 0) hn).mpr hg⟩
  apply (integrationGammaDefinable_iff ?_).mpr hfull
  intro z hz i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact hz.choose

/-- Any finite Gamma correspondence on a residue tuple domain has finite
Gamma projection over the original small real/Gamma ground. -/
theorem goodGammaImage_finite_residue_tuple {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    {n : ℕ} (G : GoodBaseGammaRelation B n (fun _ => .rv))
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hsub : ∀ a ∈ A, ∀ i, a i ∈ D i) : (goodGammaImage G A).Finite := by
  apply gamma_finite_of_definable_subset_algebraic hκ hs B hsmall hγsmall _ (goodGammaImage_definable G A hA)
  rintro δ ⟨a,ha,hδ⟩
  apply (gamma_algebraic_iff_definable_base B δ).mpr
  exact residue_tuple_gamma_algebraic_elimination hκ hs h00 B hsmall D hD hvalues a (hsub a ha) δ
    (goodGammaRow_member_algebraic G a δ hδ)
end DiamondIntegral.Section3
