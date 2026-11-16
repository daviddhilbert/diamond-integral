import «section 6».PairedCenteredDiscs

/-! The complete original-base formula for actual paired disc images.
Both proper radius representatives and the whole source-domain and
target-image equalities are retained in the four-VF-parameter graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {I : Type}

theorem variable_rawOpenBall_definable (S : Set M) (a r x : I) :
    S.Definable LRV {z : I → M | z x ∈ rawOpenBall (z a) (z r)} := by
  convert (OpenBallCodes.membership_raw_definable S).preimage_comp (![a,r,x] : Fin 3 → I) using 1
  ext z
  have he : Fin.init (z ∘ (![a,r,x] : Fin 3 → I)) = ![z a,z r] := by
    funext i
    fin_cases i <;> rfl
  change z x ∈ OpenBallCodes.rawBall ![z a,z r] ↔
    (z ∘ (![a,r,x] : Fin 3 → I)) (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init (z ∘ (![a,r,x] : Fin 3 → I)))
  rw [he]
  rfl

def pairedDiscImageCodes (A : Set (VF M)) (f : VF M → VF M) : Set (Fin 4 → M) :=
  {z | ![z 0,z 1] ∈ scalarPartialGraph A f ∧
    z 0 ∈ rawOpenBall (z 0) (z 2) ∧ z 1 ∈ rawOpenBall (z 1) (z 3) ∧
    (∀ x : Fin 1 → M, x 0 ∈ rawOpenBall (z 0) (z 2) → x 0 ∈ Subtype.val '' A) ∧
    ∀ y : Fin 1 → M, y 0 ∈ rawOpenBall (z 1) (z 3) ↔
      ∃ x : Fin 1 → M, x 0 ∈ rawOpenBall (z 0) (z 2) ∧ ![x 0,y 0] ∈ scalarPartialGraph A f}

theorem pairedDiscImageCodes_definable (A : Set (VF M)) (f : VF M → VF M)
    (hGraph : S.Definable LRV (scalarPartialGraph A f)) :
    S.Definable LRV (pairedDiscImageCodes A f) := by
  let J := Fin 4 ⊕ Fin 1
  let K := J ⊕ Fin 1
  have hSource : S.Definable LRV {z : J → M |
      z (.inr 0) ∈ rawOpenBall (z (.inl 0)) (z (.inl 2))} :=
    variable_rawOpenBall_definable (I := J) S (.inl 0) (.inl 2) (.inr 0)
  have hDomain := (scalarPartialGraph_domain_definable S A f hGraph).preimage_comp
    (fun _ : Fin 1 => (Sum.inr 0 : J))
  have hSourceBad := (hSource.inter hDomain.compl).exists_of_finite
  have hSourceBig : S.Definable LRV {z : K → M |
      z (.inr 0) ∈ rawOpenBall (z (.inl (.inl 0))) (z (.inl (.inl 2)))} :=
    variable_rawOpenBall_definable (I := K) S (.inl (.inl 0)) (.inl (.inl 2)) (.inr 0)
  have hAt := hGraph.preimage_comp (![Sum.inr 0,Sum.inl (Sum.inr 0)] : Fin 2 → K)
  have hImage := (hSourceBig.inter hAt).exists_of_finite
  have hTarget : S.Definable LRV {z : J → M |
      z (.inr 0) ∈ rawOpenBall (z (.inl 1)) (z (.inl 3))} :=
    variable_rawOpenBall_definable (I := J) S (.inl 1) (.inl 3) (.inr 0)
  have hMismatch := (hTarget.inter hImage.compl).union (hImage.inter hTarget.compl)
  have hAll := hMismatch.exists_of_finite.compl
  have hAnchor := hGraph.preimage_comp (![0,1] : Fin 2 → Fin 4)
  have hSelfSource := variable_rawOpenBall_definable S (0 : Fin 4) 2 0
  have hSelfTarget := variable_rawOpenBall_definable S (1 : Fin 4) 3 1
  convert hAnchor.inter (hSelfSource.inter (hSelfTarget.inter (hSourceBad.compl.inter hAll))) using 1
  ext z
  change (_ ∧ _ ∧ _ ∧ (∀ x, _ → _) ∧ ∀ y, _ ↔ ∃ x, _) ↔
    _ ∧ _ ∧ _ ∧ (¬ ∃ x, _ ∧ ¬ _) ∧ ¬ ∃ y, (_ ∧ ¬ ∃ x, _) ∨ ((∃ x, _) ∧ ¬ _)
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
