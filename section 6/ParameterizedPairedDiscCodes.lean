import «section 6».MixedScalarGraphCodes

/-! Complete first-order paired-disc predicates with arbitrary retained
real parameters. Source and target points are both quantified through
the full graph; no image equality is replaced by just an anchor pair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem parameterScalarGraphAt_definable (G : Set (Fin n ⊕ Fin 2 → M)) (hG : S.Definable LRV G)
    {I : Type} (π : Fin n → I) (a b : I) :
    S.Definable LRV {z : I → M | Sum.elim (z ∘ π) ![z a,z b] ∈ G} := by
  have h := hG.preimage_comp (Sum.elim π (![a,b] : Fin 2 → I))
  convert h using 1
  ext z
  have he : Sum.elim (z ∘ π) ![z a,z b]=z ∘ Sum.elim π (![a,b] : Fin 2 → I) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl
  change Sum.elim (z ∘ π) ![z a,z b] ∈ G ↔ z ∘ Sum.elim π (![a,b] : Fin 2 → I) ∈ G
  rw [he]

def parameterizedPairedDiscCodes (G : Set (Fin n ⊕ Fin 2 → M)) : Set (Fin n ⊕ Fin 4 → M) :=
  {z | Sum.elim (z ∘ Sum.inl) ![z (.inr 0),z (.inr 1)] ∈ G ∧
    z (.inr 0) ∈ rawOpenBall (z (.inr 0)) (z (.inr 2)) ∧
    z (.inr 1) ∈ rawOpenBall (z (.inr 1)) (z (.inr 3)) ∧
    (∀ x : Fin 1 → M,x 0 ∈ rawOpenBall (z (.inr 0)) (z (.inr 2)) →
      ∃ y : Fin 1 → M,Sum.elim (z ∘ Sum.inl) ![x 0,y 0] ∈ G) ∧
    ∀ y : Fin 1 → M,y 0 ∈ rawOpenBall (z (.inr 1)) (z (.inr 3)) ↔
      ∃ x : Fin 1 → M,x 0 ∈ rawOpenBall (z (.inr 0)) (z (.inr 2)) ∧
        Sum.elim (z ∘ Sum.inl) ![x 0,y 0] ∈ G}

theorem parameterizedPairedDiscCodes_definable (G : Set (Fin n ⊕ Fin 2 → M)) (hG : S.Definable LRV G) :
    S.Definable LRV (parameterizedPairedDiscCodes G) := by
  let I := Fin n ⊕ Fin 4
  let J := I ⊕ Fin 1
  let K := J ⊕ Fin 1
  let π : Fin n → K := fun i => .inl (.inl (.inl i))
  have hGraphXY := parameterScalarGraphAt_definable G hG π (Sum.inl (Sum.inr 0)) (Sum.inr 0)
  have hDomain := hGraphXY.exists_of_finite
  have hSource : S.Definable LRV {z : J → M | z (.inr 0) ∈
      rawOpenBall (z (.inl (.inr 0))) (z (.inl (.inr 2)))} :=
    variable_rawOpenBall_definable (I := J) S (.inl (.inr 0)) (.inl (.inr 2)) (.inr 0)
  have hSourceBad := (hSource.inter hDomain.compl).exists_of_finite
  have hGraphYX := parameterScalarGraphAt_definable G hG π (Sum.inr 0) (Sum.inl (Sum.inr 0))
  have hSourceBig : S.Definable LRV {z : K → M | z (.inr 0) ∈
      rawOpenBall (z (.inl (.inl (.inr 0)))) (z (.inl (.inl (.inr 2))))} :=
    variable_rawOpenBall_definable (I := K) S (.inl (.inl (.inr 0))) (.inl (.inl (.inr 2))) (.inr 0)
  have hImage := (hSourceBig.inter hGraphYX).exists_of_finite
  have hTarget : S.Definable LRV {z : J → M | z (.inr 0) ∈
      rawOpenBall (z (.inl (.inr 1))) (z (.inl (.inr 3)))} :=
    variable_rawOpenBall_definable (I := J) S (.inl (.inr 1)) (.inl (.inr 3)) (.inr 0)
  have hMismatch := (hTarget.inter hImage.compl).union (hImage.inter hTarget.compl)
  have hAll := hMismatch.exists_of_finite.compl
  have hAnchor := parameterScalarGraphAt_definable G hG (Sum.inl : Fin n → I) (.inr 0) (.inr 1)
  have hSelfSource := variable_rawOpenBall_definable S (Sum.inr 0 : I) (.inr 2) (.inr 0)
  have hSelfTarget := variable_rawOpenBall_definable S (Sum.inr 1 : I) (.inr 3) (.inr 1)
  convert hAnchor.inter (hSelfSource.inter (hSelfTarget.inter (hSourceBad.compl.inter hAll))) using 1
  ext z
  change (_ ∧ _ ∧ _ ∧ (∀ x,_ → ∃ y,_) ∧ ∀ y,_ ↔ ∃ x,_ ∧ _) ↔
    _ ∧ _ ∧ _ ∧ (¬ ∃ x,_ ∧ ¬ ∃ y,_) ∧ ¬ ∃ y,(_ ∧ ¬ ∃ x,_) ∨ ((∃ x,_) ∧ ¬ _)
  constructor
  · rintro ⟨hA,hS,hT,hDom,hImage⟩
    refine ⟨hA,hS,hT,?_,?_⟩
    · rintro ⟨x,hx,hn⟩
      exact hn (hDom x hx)
    · rintro ⟨y,(⟨hy,hn⟩ | ⟨hy,hn⟩)⟩
      · exact hn ((hImage y).mp hy)
      · exact hn ((hImage y).mpr hy)
  · rintro ⟨hA,hS,hT,hDom,hImage⟩
    refine ⟨hA,hS,hT,?_,?_⟩
    · intro x hx
      by_contra hn
      exact hDom ⟨x,hx,hn⟩
    · intro y
      constructor
      · intro hy
        by_contra hn
        exact hImage ⟨y,Or.inl ⟨hy,hn⟩⟩
      · intro hy
        by_contra hn
        exact hImage ⟨y,Or.inr ⟨hy,hn⟩⟩

end DiamondIntegral.Section6
