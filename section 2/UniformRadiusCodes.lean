import «section 2».GammaBallRelations
import «section 2».CorrespondenceSets
import «section 2».GammaFiniteFamilies

/-! Full uniform formulas for fibre-ball certificates and their unary
projections, with every proper code of each Gamma radius retained. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

private def radiusBadIndex (n : ℕ) : Fin 1 ⊕ Fin n → (Fin 1 ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr

private def radiusMemberIndex (n : ℕ) : Fin 1 ⊕ Fin n → ((Fin 1 ⊕ Fin 1) ⊕ Fin n) ⊕ Fin n :=
  Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) Sum.inr

private def radiusBallIndex (n : ℕ) : (Fin n ⊕ Fin n) ⊕ Fin 1 → ((Fin 1 ⊕ Fin 1) ⊕ Fin n) ⊕ Fin n :=
  Sum.elim (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr) (Sum.inl ∘ Sum.inl ∘ Sum.inl)

def radiusGoodFibre (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M)) (γ : Gamma M) (a : Fin 1 → VF M) :
    Set (Fin n → VF M) := {x ∈ C a | ∀ y ∈ vfBall x γ, (a,y) ∈ A}

def goodRadiusCodes (I : Set (Fin 1 → VF M))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M)) :
    Set ((Fin 1 ⊕ Fin 1) ⊕ Fin n → M) :=
  {z | GammaParameters.NonzeroRV (z (.inl (.inl 0))) ∧
    z ∘ radiusBadIndex n ∈ vfCorrespondenceGraph I C ∧
      ∀ y : Fin n → M, Sum.elim z y ∘ radiusBallIndex n ∈ rawGammaBallRelation n →
        Sum.elim z y ∘ radiusMemberIndex n ∈ vfCorrespondenceGraph I (fun a => {y | (a,y) ∈ A})}

theorem goodRadiusCodes_definable {S : Set M}
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M))
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {y | (a,y) ∈ A})))
    (hC : S.Definable LRV (vfCorrespondenceGraph I C)) :
    S.Definable LRV (goodRadiusCodes I A C) := by
  have hbad := (((rawGammaBallRelation_definable S n).preimage_comp (radiusBallIndex n)).inter
    (hA.preimage_comp (radiusMemberIndex n)).compl).exists_of_finite
  have hNZ := (GammaParameters.nonzero_rv_definable S).preimage_comp
    (fun _ : Fin 1 => (Sum.inl (.inl 0) : (Fin 1 ⊕ Fin 1) ⊕ Fin n))
  convert hNZ.inter ((hC.preimage_comp (radiusBadIndex n)).inter hbad.compl) using 1
  ext z
  change (_ ∧ _ ∧ ∀ y, _ → _) ↔ _ ∧ _ ∧ ¬ ∃ y, _ ∧ ¬ _
  constructor
  · rintro ⟨ht,hc,hall⟩
    exact ⟨ht,hc,by rintro ⟨y,hy,hno⟩; exact hno (hall y hy)⟩
  · rintro ⟨ht,hc,hno⟩
    refine ⟨ht,hc,fun y hy => ?_⟩
    by_contra hn
    exact hno ⟨y,hy,hn⟩

theorem goodRadiusCodes_at
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M))
    (t : M) (ht : GammaParameters.NonzeroRV t) (a : Fin 1 → VF M) (x : Fin n → VF M) :
    Sum.elim (Sum.elim (fun _ : Fin 1 => t) (vfValues a)) (vfValues x) ∈ goodRadiusCodes I A C ↔
      a ∈ I ∧ x ∈ radiusGoodFibre A C (GammaParameters.codeValue t) a := by
  simp only [goodRadiusCodes,Set.mem_setOf_eq]
  have hidx : Sum.elim (Sum.elim (fun _ : Fin 1 => t) (vfValues a)) (vfValues x) ∘ radiusBadIndex n =
      Sum.elim (vfValues a) (vfValues x) := by
    funext j
    cases j <;> rfl
  rw [hidx]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [and_iff_right ht,vfCorrespondenceGraph_at]
  have hmember (y : Fin n → M) :
      Sum.elim (Sum.elim (Sum.elim (fun _ : Fin 1 => t) (vfValues a)) (vfValues x)) y ∘
        radiusMemberIndex n = Sum.elim (vfValues a) y := by
    funext j
    cases j <;> rfl
  simp_rw [hmember]
  constructor
  · rintro ⟨⟨ha,hx⟩,hall⟩
    refine ⟨ha,hx,fun y hy => ?_⟩
    have hball := (rawGammaBallRelation_iff x y t ht).mpr hy
    exact ((vfCorrespondenceGraph_at I (fun a => {y | (a,y) ∈ A}) a y).mp
      (hall (vfValues y) hball)).2
  · rintro ⟨ha,hx,hall⟩
    refine ⟨⟨ha,hx⟩,fun y hy => ?_⟩
    have hys : ∀ i, iVF (y i) := hy.2.2.1
    let b : Fin n → VF M := fun i => ⟨y i,hys i⟩
    have hball : b ∈ vfBall x (GammaParameters.codeValue t) :=
      (rawGammaBallRelation_iff x b t ht).mp hy
    exact (vfCorrespondenceGraph_at I (fun a => {y | (a,y) ∈ A}) a b).mpr ⟨ha,hall b hball⟩

theorem radiusGoodFibre_graph_definable_univ
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M)) {S : Set M}
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {y | (a,y) ∈ A})))
    (hC : S.Definable LRV (vfCorrespondenceGraph I C)) (γ : Gamma M) :
    (Set.univ : Set M).Definable LRV (vfCorrespondenceGraph I (radiusGoodFibre A C γ)) := by
  obtain ⟨t,ht,het⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
  let f (z : Fin 1 ⊕ Fin n → M) : (Fin 1 ⊕ Fin 1) ⊕ Fin n → M :=
    Sum.elim (Sum.elim (fun _ => t) (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hf : (Set.univ : Set M).DefinableMap LRV f := by
    rintro ((i | i) | i)
    · exact LRV.definableFun_const _ (Set.mem_univ t)
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have h := ((goodRadiusCodes_definable I A C hA hC).mono (Set.subset_univ _)).preimage_map hf
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,x,hx,rfl⟩
    exact (goodRadiusCodes_at I A C t ht a x).mpr ⟨ha,het.symm ▸ hx⟩
  · intro hz
    have hidx : f z ∘ radiusBadIndex n = z := by
      funext j
      cases j <;> rfl
    have hCz := hz.2.1
    rw [hidx] at hCz
    obtain ⟨a,ha,x,hx,rfl⟩ := hCz
    have hgood := (goodRadiusCodes_at I A C t ht a x).mp hz
    exact ⟨a,ha,x,het ▸ hgood.2,rfl⟩

end DiamondIntegral.Section2
