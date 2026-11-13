import «section 3».FullRawLogic
import «section 3».IntegrationGammaParameters
import «section 3».FullGammaTuplePoint
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



/-- Full code preimage of a mixed RV-tuple/Gamma-tuple family. -/
def mixedGammaTupleDefinable (B : Base (M := M)) {n m : ℕ}
    (R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop) : Prop :=
  FullRawDefinable (integrationGammaBase B) (fun z : Fin n ⊕ Fin m → M =>
    GammaSyntax.Proper (z ∘ Sum.inr) ∧ R (z ∘ Sum.inl) (GammaSyntax.decode (z ∘ Sum.inr)))

theorem mixedGammaTupleDefinable.column {B : Base (M := M)} {n m : ℕ}
    {R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop}
    (hR : mixedGammaTupleDefinable B R) (a : Fin n → M) :
    FullGammaSyntax.Definable (integrationGammaBase ⟨B.real ∪ Set.range a,B.gamma⟩) (R a) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range a,B.gamma⟩
  let T : Set M := C.real
  let F (z : Fin m → M) : Fin n ⊕ Fin m → M := Sum.elim a z
  have hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin m) (Fin n ⊕ Fin m) T F := by
    letI := CanonicalStructure.normalize (M := M)
    intro i
    cases i with
    | inl j => exact LRV.definableFun_const (Fin m) (show a j ∈ T from Or.inr (Set.mem_range_self j))
    | inr j => exact Set.DefinableFun.proj LRV
  have hh := FullBaseAtomicity.OverBase.preimage_map
    (FullBaseAtomicity.OverBase.mono hR (B' := integrationGammaBase C) Set.subset_union_left Set.Subset.rfl) hF
  exact hh

/-- A Gamma tuple individually definable over the original base can be
specialized without naming any of its RV representatives. -/
theorem mixedGammaTupleDefinable.fibre {B : Base (M := M)} {n m : ℕ}
    {R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop}
    (hR : mixedGammaTupleDefinable B R) (γ : Fin m → Values.Gamma (M := M))
    (hγ : ∀ i, FullGammaSyntax.Scalar (integrationGammaBase B) {γ i}) :
    FullRawDefinable (integrationGammaBase B) (fun a => R a γ) := by
  have hnames := FullGammaSyntax.Definable.forall_finite (fun i => FullGammaSyntax.unary_at (hγ i) i)
  have hnc : FullRawDefinable (integrationGammaBase B)
      (fun z : Fin n ⊕ Fin m → M => GammaSyntax.Proper (z ∘ Sum.inr) ∧
        ∀ i, GammaSyntax.decode (z ∘ Sum.inr) i = γ i) :=
    FullRawDefinable.reindex hnames (Sum.inr : Fin m → Fin n ⊕ Fin m)
  have hh := (hR.and hnc).exists_block
  apply FullBaseAtomicity.OverBase.congr hh
  intro a
  change (∃ c : Fin m → M,
    (GammaSyntax.Proper c ∧ R a (GammaSyntax.decode c)) ∧
    GammaSyntax.Proper c ∧ ∀ i, GammaSyntax.decode c i = γ i) ↔ R a γ
  constructor
  · rintro ⟨c,⟨hc,hr⟩,_,he⟩
    exact (funext he) ▸ hr
  · intro hr
    let c := representatives γ
    have hp : GammaSyntax.Proper (rawTuple c) := rawTuple_proper c
    have he : GammaSyntax.decode (rawTuple c) = γ := by
      funext i
      exact (codeValue_raw _).trans (congrFun (representatives_values γ) i)
    exact ⟨rawTuple c,⟨hp,he.symm ▸ hr⟩,hp,fun i => congrFun he i⟩
end DiamondIntegral.Section3
