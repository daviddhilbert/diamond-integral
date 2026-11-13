import «section 3».IntegrationDiscCodes
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Exposing a suffix of Gamma arguments as full invariant real codes,
while retaining the original named prefix. This supports the finite-disc
parameter comparison without choosing named radius representatives. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {k l n : ℕ} {S : Set M} {sn : Fin n → SortTag}

def integrationGammaTailRelation (R : GammaParameters.Relation S (k+l) n sn)
    (θ : Fin k → ParameterPresentation.Name (M := M)) : Set (Fin l ⊕ Fin n → M) :=
  {x | GammaParameters.Proper (x ∘ Sum.inl) ∧ x ∘ Sum.inr ∈
    integrationGammaRelation R (Fin.append θ (fun j => Sum.inr (codeValue (x (.inl j)))))}

def integrationGammaTailRecode
    (z : (Fin k × Fin 5) ⊕ (Fin l ⊕ Fin n) → M) : (Fin (k+l) × Fin 5) ⊕ Fin n → M :=
  Sum.elim (fun p => Fin.addCases (fun i => z (.inl (i,p.2)))
    (fun i => AdjoinGamma.embedCode ![z (.inr (.inl i))] p.2) p.1)
    (fun j => z (.inr (.inr j)))

theorem integrationGammaEmbed_proper_iff (x : M) :
    AdjoinGamma.embedCode ![x] ∈ ParameterPresentation.codeDomain ↔ NonzeroRV x := by
  have hn : iVFOne (M := M) ≠ iVFZero :=
    fun he => (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
  change ((iVFOne = iVFZero ∧ _) ∨ (iVFOne ≠ iVFZero ∧ NonzeroRV x)) ↔ _
  constructor
  · rintro (h | h)
    · exact (hn h.1).elim
    · exact h.2
  · intro hx
    exact Or.inr ⟨hn,hx⟩

theorem integrationGammaTailRecode_definable (S : Set M) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      ((Fin k × Fin 5) ⊕ (Fin l ⊕ Fin n)) ((Fin (k+l) × Fin 5) ⊕ Fin n) S
      (integrationGammaTailRecode (M := M)) := by
  have he := AdjoinGamma.embedCode_definable (M := M) S
  letI := CanonicalStructure.normalize (M := M)
  intro j
  cases j with
  | inr j => exact Set.DefinableFun.proj LRV
  | inl p =>
    rcases p with ⟨i,c⟩
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [integrationGammaTailRecode,Sum.elim_inl,Fin.addCases_left]
      exact Set.DefinableFun.proj LRV
    · simp only [integrationGammaTailRecode,Sum.elim_inl,Fin.addCases_right]
      exact (he c).comp
        (g := fun z : (Fin k × Fin 5) ⊕ (Fin l ⊕ Fin n) → M => fun _ : Fin 1 => z (.inr (.inl b)))
        (fun _ => Set.DefinableFun.proj LRV (i := Sum.inr (Sum.inl b)))

theorem integrationGammaTail_pullback (R : GammaParameters.Relation S (k+l) n sn)
    (z : (Fin k × Fin 5) ⊕ (Fin l ⊕ Fin n) → M) :
    z ∈ ImaginaryParameters.vectorPullback
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin k))
      (integrationGammaTailRelation R) ↔
    integrationGammaTailRecode z ∈ ImaginaryParameters.vectorPullback
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (k+l)))
      (integrationGammaRelation R) := by
  have hcode : (∀ i : Fin (k+l), (fun j => integrationGammaTailRecode z (.inl (i,j))) ∈
      ParameterPresentation.codeDomain) ↔
    (∀ i : Fin k, (fun j => z (.inl (i,j))) ∈ ParameterPresentation.codeDomain) ∧
      GammaParameters.Proper (fun j => z (.inr (.inl j))) := by
    constructor
    · intro h
      refine ⟨fun i => ?_,fun i => ?_⟩
      · simpa only [integrationGammaTailRecode,Sum.elim_inl,Fin.addCases_left] using h (Fin.castAdd l i)
      · apply (integrationGammaEmbed_proper_iff _).mp
        simpa only [integrationGammaTailRecode,Sum.elim_inl,Fin.addCases_right] using h (Fin.natAdd k i)
    · rintro ⟨hp,ht⟩ i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · simpa only [integrationGammaTailRecode,Sum.elim_inl,Fin.addCases_left] using hp a
      · simpa only [integrationGammaTailRecode,Sum.elim_inl,Fin.addCases_right] using
          (integrationGammaEmbed_proper_iff _).mpr (ht b)
  have hdecode (h : ∀ i : Fin (k+l), (fun j => integrationGammaTailRecode z (.inl (i,j))) ∈
      ParameterPresentation.codeDomain) :
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (k+l))).decode
        ⟨integrationGammaTailRecode z ∘ Sum.inl,h⟩ =
      Fin.append ((ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin k)).decode
        ⟨z ∘ Sum.inl,(hcode.mp h).1⟩) (fun j => Sum.inr (codeValue (z (.inr (.inl j))))) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [ImaginaryParameters.tuplePresentation,integrationGammaTailRecode,
        Function.comp_apply,Sum.elim_inl,Fin.addCases_left,Fin.append_left]
    · simpa only [ImaginaryParameters.tuplePresentation,integrationGammaTailRecode,
        Function.comp_apply,Sum.elim_inl,Fin.addCases_right,Fin.append_right,
        ParameterPresentation.presentation,Matrix.cons_val_zero] using
        (AdjoinGamma.embedCode_compatible ![z (.inr (.inl b))] ((hcode.mp h).2 b)).choose_spec
  constructor
  · rintro ⟨hp,ht,hr⟩
    have h := hcode.mpr ⟨hp,ht⟩
    refine ⟨h,?_⟩
    change _ ∈ integrationGammaRelation R _
    rw [hdecode h]
    exact hr
  · rintro ⟨h,hr⟩
    refine ⟨(hcode.mp h).1,(hcode.mp h).2,?_⟩
    rw [hdecode h] at hr
    exact hr

theorem integrationGammaTailWith (R : GammaParameters.Relation S (k+l) n sn)
    (γ : Fin k → Values.Gamma (M := M)) :
    @ImaginaryParameters.WithTuple LRV M (CanonicalStructure.normalize (M := M))
      (ParameterPresentation.Name (M := M)) (Fin 5) (@ParameterPresentation.presentation M sM hM)
      S (Fin k) (Fin l ⊕ Fin n) (fun i => Sum.inr (γ i))
      (integrationGammaTailRelation R (fun i => Sum.inr (γ i))) := by
  have hr := integrationGammaRelation_definable R
  have hm := integrationGammaTailRecode_definable (M := M) (k := k) (l := l) (n := n) S
  have he := integrationGammaTail_pullback R
  let Q := integrationGammaTailRelation R
  letI := CanonicalStructure.normalize (M := M)
  refine ⟨Q,?_,rfl⟩
  convert hr.preimage_map hm using 1
  ext z
  exact he z
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationGammaTailOverBase (B : GammaParameters.Base (M := M)) {k l n : ℕ}
    {sn : Fin n → SortTag} (R : GammaParameters.Relation B.real (k+l) n sn)
    (γ : Fin k → Values.Gamma (M := M)) (hγ : ∀ i, γ i ∈ B.gamma) :
    FullBaseAtomicity.OverBase (integrationGammaBase B)
      (integrationGammaTailRelation R (fun i => Sum.inr (γ i))) := by
  let F : Finset (ParameterPresentation.Name (M := M)) := Finset.univ.image (fun i => Sum.inr (γ i))
  have hF (i : Fin k) : Sum.inr (γ i) ∈ F := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  refine ⟨F,?_,?_⟩
  · rintro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨γ j,hγ j,rfl⟩
  · have hw := integrationGammaTailWith R γ
    have hp := ParameterPresentation.codeDomain_definable B.real
    letI := CanonicalStructure.normalize (M := M)
    exact hw.reindex hp (fun i => (⟨Sum.inr (γ i),hF i⟩ : F)) rfl

theorem integrationGammaTail_row {S : Set M} {k l n : ℕ} {sn : Fin n → SortTag}
    (R : GammaParameters.Relation S (k+l) n sn) (γ : Fin k → Values.Gamma (M := M))
    (t : Fin l → GammaParameters.Code (M := M)) (b : Fin n → M) :
    Sum.elim (GammaParameters.rawTuple t) b ∈
      integrationGammaTailRelation R (fun i => Sum.inr (γ i)) ↔
    b ∈ R.fibre (Fin.append γ (GammaParameters.values t)) := by
  have he : Fin.append (fun i => Sum.inr (γ i))
      (fun j => Sum.inr (codeValue (GammaParameters.rawTuple t j))) =
      (fun i => (Sum.inr (Fin.append γ (GammaParameters.values t) i) : ParameterPresentation.Name (M := M))) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      exact congrArg Sum.inr (codeValue_raw (t a))
  change (GammaParameters.Proper (GammaParameters.rawTuple t) ∧
    ∃ η, Fin.append (fun i => Sum.inr (γ i))
      (fun j => Sum.inr (codeValue (GammaParameters.rawTuple t j))) = (fun i => Sum.inr (η i)) ∧
      b ∈ R.fibre η) ↔ _
  rw [he, and_iff_right (GammaParameters.rawTuple_proper t)]
  constructor
  · rintro ⟨η,hη,hb⟩
    have heq : Fin.append γ (GammaParameters.values t) = η :=
      funext (fun i => Sum.inr.inj (congrFun hη i))
    exact heq.symm ▸ hb
  · intro hb
    exact ⟨_,rfl,hb⟩
end DiamondIntegral.Section3
