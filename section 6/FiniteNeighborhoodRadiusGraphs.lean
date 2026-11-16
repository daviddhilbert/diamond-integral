import «section 6».SeparatedPairedCores

/-! The full original-base formula for one radius fitting a prescribed
neighborhood at every point of a finite center family. All centers are
quantified through their complete defining set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

def finiteNeighborhoodRadiusCodes (C : Set (Fin n → VF M))
    (R : Set (Fin n ⊕ Fin 1 → M)) (j : Fin n) : Set (Fin 1 → M) :=
  {z | z ∈ vfValues '' puncturedRadiusBall (1 : Gamma M) ∧
    ∀ q : Fin n → M, ∀ x : Fin 1 → M, q ∈ vfValues '' C →
      x 0 ∈ rawOpenBall (q j) (z 0) → Sum.elim q x ∈ R}

theorem finiteNeighborhoodRadiusCodes_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : Set (Fin n → VF M)) (hC : S.Definable LRV (vfValues '' C))
    (R : Set (Fin n ⊕ Fin 1 → M)) (hR : S.Definable LRV R) (j : Fin n) :
    S.Definable LRV (finiteNeighborhoodRadiusCodes C R j) := by
  let J := Fin 1 ⊕ Fin n
  let K := J ⊕ Fin 1
  let cidx : Fin n → K := fun i => .inl (.inr i)
  let ridx : Fin n ⊕ Fin 1 → K := Sum.elim cidx Sum.inr
  have hCenter := hC.preimage_comp cidx
  have hBall := variable_rawOpenBall_definable (I := K) S (.inl (.inr j)) (.inl (.inl 0)) (.inr 0)
  have hBad := ((hCenter.inter hBall).inter (hR.preimage_comp ridx).compl).exists_of_finite.exists_of_finite
  have hBase := puncturedRadiusBall_definable (M := M) (S := S) (1 : Gamma M) (gamma_one_named hc)
  convert hBase.inter hBad.compl using 1
  ext z
  have hRidx (q : Fin n → M) (x : Fin 1 → M) : Sum.elim (Sum.elim z q) x ∘ ridx = Sum.elim q x := by
    funext i
    cases i <;> rfl
  have hCidx (q : Fin n → M) (x : Fin 1 → M) : Sum.elim (Sum.elim z q) x ∘ cidx = q := rfl
  change (_ ∧ ∀ q x, _ → _ → _) ↔ _ ∧ ¬ ∃ q x, (_ ∧ _) ∧ ¬ _
  constructor
  · rintro ⟨hz,hall⟩
    refine ⟨hz,?_⟩
    rintro ⟨q,x,⟨hq,hx⟩,hn⟩
    change Sum.elim (Sum.elim z q) x ∘ ridx ∉ R at hn
    rw [hRidx] at hn
    exact hn (hall q x hq hx)
  · rintro ⟨hz,hall⟩
    refine ⟨hz,fun q x hq hx => ?_⟩
    by_contra hn
    apply hall
    refine ⟨q,x,⟨hq,hx⟩,?_⟩
    change Sum.elim (Sum.elim z q) x ∘ ridx ∉ R
    rw [hRidx]
    exact hn

theorem finiteNeighborhoodRadiusCodes_at
    (C : Set (Fin n → VF M)) (R : Set (Fin n ⊕ Fin 1 → M)) (j : Fin n)
    (c : VF M) (hc0 : c ≠ 0) :
    (fun _ : Fin 1 => c.val) ∈ finiteNeighborhoodRadiusCodes C R j ↔
      (1 : GammaInfinity M) < vfValue c ∧ ∀ q ∈ C, ∀ x ∈ centeredGammaDisc (q j) (finiteValue c hc0),
        Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R := by
  constructor
  · rintro ⟨⟨a,ha,he⟩,hall⟩
    have hac : a 0 = c := Subtype.ext (congrFun he 0)
    have hpos : (1 : GammaInfinity M) < vfValue (a 0) := ha.2
    refine ⟨hac ▸ hpos,?_⟩
    intro q hq x hx
    exact hall (vfValues q) (fun _ => x.val) ⟨q,hq,rfl⟩
      ((rawOpenBall_iff_centeredGammaDisc (q j) c x hc0).mpr hx)
  · rintro ⟨hcpos,hall⟩
    refine ⟨⟨fun _ => c,⟨hc0,hcpos⟩,rfl⟩,?_⟩
    rintro q x ⟨a,ha,he⟩ hx
    have hxSort : iVF (x 0) := hx.2.1
    let y : VF M := ⟨x 0,hxSort⟩
    have hRaw : y.val ∈ rawOpenBall (a j).val c.val := by
      have hCenter : (a j).val = q j := congrFun he j
      rw [hCenter]
      exact hx
    have h := hall a ha y ((rawOpenBall_iff_centeredGammaDisc (a j) c y hc0).mp hRaw)
    have hX : (fun _ : Fin 1 => y.val) = x := by funext i; fin_cases i; rfl
    rwa [he,hX] at h

end DiamondIntegral.Section6
