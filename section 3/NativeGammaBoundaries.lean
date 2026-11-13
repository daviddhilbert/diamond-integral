import «section 3».CodedGammaBoundary
import «section 3».ResidueGammaProjection
import IntegrationSection3ACVF.FullGammaPoint
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


theorem nativeGammaColumn_definable (B : Base (M := M)) {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))})
    (a : Fin n → M) :
    GammaDefinableOverBase ⟨B.real ∪ Set.range a,B.gamma⟩ {γ | R a γ} := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range a,B.gamma⟩
  let T : Set M := C.real
  let F (z : Fin 1 → M) : Fin (n+1) → M := Fin.snoc a (z 0)
  have hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin 1) (Fin (n+1)) T F := by
    letI := CanonicalStructure.normalize (M := M)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [F,Fin.snoc_last]
      exact Set.DefinableFun.proj LRV
    · simp only [F,Fin.snoc_castSucc]
      exact LRV.definableFun_const (Fin 1) (show a j ∈ T from Or.inr (Set.mem_range_self j))
  have hd := (hR.mono (C := C) Set.subset_union_left Set.Subset.rfl).preimage_real_map
    (fun _ : Fin 1 => .rv) F hF
  change DefinableOverBase C (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback {γ | R a γ}}
  convert hd using 1
  ext z
  change (z 0 ∈ Values.gammaPullback {γ | R a γ}) ↔
    ((NonzeroRV (F z (Fin.last n)) ∧ R (Fin.init (F z)) (codeValue (F z (Fin.last n)))) ∧
    z ∈ sortedUniverse (fun _ => .rv))
  simp only [F,Fin.init_snoc,Fin.snoc_last,GammaSyntax.mem_gammaPullback_iff,Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h,fun i => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact h.1.1⟩,fun h => h.1⟩

def nativeGammaBoundaryCarrier {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop) : Set ((Fin n → M) × M) :=
  {p | (∀ i, iRV (p.1 i)) ∧ codedGammaBoundary
    (fun a t => NonzeroRV t ∧ R a (codeValue t)) p.1 p.2}

theorem nativeGammaBoundaryCarrier_mem {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop) (a : Fin n → M) (t : M) :
    (a,t) ∈ nativeGammaBoundaryCarrier R ↔
      (∀ i, iRV (a i)) ∧ NonzeroRV t ∧ codeValue t ∈ orderBoundary {γ | R a γ} := by
  exact and_congr Iff.rfl (codedGammaBoundary_iff _ R (fun a t ht => and_iff_right ht) a t)

theorem nativeGammaBoundaryCarrier_definable (B : Base (M := M)) {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))}) :
    DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | (Fin.init z,z (Fin.last n)) ∈ nativeGammaBoundaryCarrier R} := by
  let π : Fin (n+1) → Fin n ⊕ Fin 1 := Fin.lastCases (.inr 0) Sum.inl
  have hp : FullRawDefinable (integrationGammaBase B)
      (fun z : Fin n ⊕ Fin 1 → M => NonzeroRV (z (.inr 0)) ∧
        R (z ∘ Sum.inl) (codeValue (z (.inr 0)))) := by
    have hh := FullRawDefinable.reindex (integrationGammaDefinable hR) π
    convert hh using 1
    ext z
    have he : Fin.init (z ∘ π) = z ∘ Sum.inl := by
      funext i
      simp only [Fin.init,Function.comp_apply,π,Fin.lastCases_castSucc]
    change (NonzeroRV (z (.inr 0)) ∧ R (z ∘ Sum.inl) (codeValue (z (.inr 0)))) ↔ _
    simp only [Function.comp_apply,π,Fin.lastCases_last] at he ⊢
    rw [← he]
  have hb := codedGammaBoundary_definable (integrationGammaBase B)
    (fun a t => NonzeroRV t ∧ R a (codeValue t)) hp
  have hs := FullRawDefinable.forall_finite (fun i : Fin n =>
    fullRaw_rv (integrationGammaBase B) (Sum.inl i : Fin n ⊕ Fin 1))
  have hh := (hs.and hb).reindex
    (Sum.elim Fin.castSucc (fun _ : Fin 1 => Fin.last n))
  apply (integrationGammaDefinable_iff ?_).mpr
  · convert hh using 1
    ext z
    rfl
  · intro z hz i
    have hx := (nativeGammaBoundaryCarrier_mem R _ _).mp hz
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last,sortEval,iRV] using hx.2.1.1
    · simpa only [Fin.lastCases_castSucc,Fin.init,sortEval,iRV] using hx.1 j

theorem nativeGammaBoundaryRow_eq {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop) (a : Fin n → M) :
    gammaRow (nativeGammaBoundaryCarrier R) a =
      if ∀ i, iRV (a i) then orderBoundary {γ | R a γ} else ∅ := by
  ext γ
  change (a,raw (representative γ)) ∈ nativeGammaBoundaryCarrier R ↔ _
  rw [nativeGammaBoundaryCarrier_mem]
  have hn : NonzeroRV (raw (representative γ)) := ⟨raw_rv _,raw_ne_zero _⟩
  have he : codeValue (raw (representative γ)) = γ :=
    (codeValue_raw _).trans (representative_value γ)
  rw [he]
  by_cases ha : ∀ i, iRV (a i) <;> simp [ha,hn]

def nativeGammaBoundaryRelation (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))}) :
    GoodBaseGammaRelation B n (fun _ => .rv) where
  carrier := nativeGammaBoundaryCarrier R
  definable := nativeGammaBoundaryCarrier_definable B R hR
  proper a t ht := ((nativeGammaBoundaryCarrier_mem R a t).mp ht).2.1
  invariant a t u he := by
    simp only [nativeGammaBoundaryCarrier_mem,codeValue_raw,he,
      show NonzeroRV (raw t) from ⟨raw_rv _,raw_ne_zero _⟩,
      show NonzeroRV (raw u) from ⟨raw_rv _,raw_ne_zero _⟩]
  finite a := by
    rw [nativeGammaBoundaryRow_eq]
    split_ifs
    · apply orderBoundary_finite_of_controller
      have hc := integrationGammaDefinable (nativeGammaColumn_definable B R hR a)
      obtain ⟨F,hF,_,_⟩ := FullGammaPoint.exists_definable_minimal_controller h00 _ hc
      exact ⟨F,hF⟩
    · exact Set.finite_empty
end DiamondIntegral.Section3
