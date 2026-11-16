import «section 6».BoundedPairedDiscFamilies

/-! Canonical paired cores from a finite nonempty family of valid
radius pairs. Intersect all candidate discs. A largest source radius
realizes that intersection and its actual target image, so no candidate
or individual radius representative is named. Full core graphs stay over S. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def candidateDiscCore (F : (Fin 2 → VF M) → Set (Fin 2 → VF M))
    (q : Fin 2 → VF M) (i : Fin 2) : Set (VF M) :=
  {x | ∀ r ∈ F q, x.val ∈ rawOpenBall (q i).val (r i).val}

def candidateDiscCoreGraph (C : Set (Fin 2 → VF M))
    (F : (Fin 2 → VF M) → Set (Fin 2 → VF M)) (i : Fin 2) : Set (Fin 2 ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ vfValues '' C ∧ ∀ r : Fin 2 → M,
    Sum.elim (z ∘ Sum.inl) r ∈ vfCorrespondenceGraph C F →
      z (.inr 0) ∈ rawOpenBall (z (.inl i)) (r i)}

theorem candidateDiscCoreGraph_definable (C : Set (Fin 2 → VF M))
    (hC : S.Definable LRV (vfValues '' C))
    (F : (Fin 2 → VF M) → Set (Fin 2 → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph C F)) (i : Fin 2) :
    S.Definable LRV (candidateDiscCoreGraph C F i) := by
  let J := Fin 2 ⊕ Fin 1
  let idx : Fin 2 ⊕ Fin 2 → J ⊕ Fin 2 := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hBall := variable_rawOpenBall_definable (I := J ⊕ Fin 2) S (.inl (.inl i)) (.inr i) (.inl (.inr 0))
  have hBad := ((hF.preimage_comp idx).inter hBall.compl).exists_of_finite
  convert (hC.preimage_comp (Sum.inl : Fin 2 → J)).inter hBad.compl using 1
  ext z
  have hIdx (r : Fin 2 → M) : Sum.elim z r ∘ idx = Sum.elim (z ∘ Sum.inl) r := by
    funext j
    cases j <;> rfl
  change (_ ∧ ∀ r, _ → _) ↔ _ ∧ ¬ ∃ r, _ ∧ ¬ _
  constructor
  · rintro ⟨hz,hall⟩
    refine ⟨hz,?_⟩
    rintro ⟨r,hr,hn⟩
    change Sum.elim z r ∘ idx ∈ vfCorrespondenceGraph C F at hr
    rw [hIdx] at hr
    exact hn (hall r hr)
  · rintro ⟨hz,hall⟩
    refine ⟨hz,fun r hr => ?_⟩
    by_contra hn
    apply hall
    refine ⟨r,?_,hn⟩
    change Sum.elim z r ∘ idx ∈ vfCorrespondenceGraph C F
    rw [hIdx]
    exact hr

theorem candidateDiscCoreGraph_at (C : Set (Fin 2 → VF M))
    (F : (Fin 2 → VF M) → Set (Fin 2 → VF M)) (i : Fin 2)
    (q : Fin 2 → VF M) (hq : q ∈ C) (x : VF M) :
    Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ candidateDiscCoreGraph C F i ↔
      x ∈ candidateDiscCore F q i := by
  constructor
  · rintro ⟨hSource,hall⟩
    intro r hr
    exact hall (vfValues r) ⟨q,hq,r,hr,rfl⟩
  · intro hx
    refine ⟨⟨q,hq,rfl⟩,?_⟩
    intro r hGraph
    obtain ⟨p,hp,s,hs,he⟩ := hGraph
    have hpq : p = q := vfValues_injective (funext fun j => congrFun he (.inl j))
    subst p
    have hsVal : (s i).val = r i := congrFun he (.inr i)
    have h := hx s hs
    change x.val ∈ rawOpenBall (q i).val (r i)
    rw [← hsVal]
    exact h

theorem candidateDiscCores_paired (F : (Fin 2 → VF M) → Set (Fin 2 → VF M))
    (q : Fin 2 → VF M) (hFin : (F q).Finite) (hNe : (F q).Nonempty)
    (f : VF M → VF M)
    (hPair : ∀ r ∈ F q, ∃ hr : r 0 ≠ 0, ∃ hs : r 1 ≠ 0,
      f '' centeredGammaDisc (q 0) (finiteValue (r 0) hr) = centeredGammaDisc (q 1) (finiteValue (r 1) hs)) :
    ∃ r ∈ F q, ∃ hr : r 0 ≠ 0, ∃ hs : r 1 ≠ 0,
      candidateDiscCore F q 0 = centeredGammaDisc (q 0) (finiteValue (r 0) hr) ∧
      candidateDiscCore F q 1 = centeredGammaDisc (q 1) (finiteValue (r 1) hs) ∧
      f '' candidateDiscCore F q 0 = candidateDiscCore F q 1 := by
  let γ (r : Fin 2 → VF M) : Gamma M := if hr : r 0 ≠ 0 then finiteValue (r 0) hr else 1
  have hNeFin : hFin.toFinset.Nonempty := by
    obtain ⟨r,hr⟩ := hNe
    exact ⟨r,hFin.mem_toFinset.mpr hr⟩
  obtain ⟨r,hr,hMax⟩ := hFin.toFinset.exists_max_image γ hNeFin
  have hrF : r ∈ F q := hFin.mem_toFinset.mp hr
  obtain ⟨hr0,hr1,hImage⟩ := hPair r hrF
  have hSource : candidateDiscCore F q 0 = centeredGammaDisc (q 0) (finiteValue (r 0) hr0) := by
    ext x
    constructor
    · intro hx
      exact (rawOpenBall_iff_centeredGammaDisc _ _ _ hr0).mp (hx r hrF)
    · intro hx t ht
      obtain ⟨ht0,ht1,hImageT⟩ := hPair t ht
      have hle : finiteValue (t 0) ht0 ≤ finiteValue (r 0) hr0 := by
        simpa only [γ,dif_pos ht0,dif_pos hr0] using hMax t (hFin.mem_toFinset.mpr ht)
      exact (rawOpenBall_iff_centeredGammaDisc _ _ _ ht0).mpr
        (centeredGammaDisc_anti (q 0) hle hx)
  have hTarget : candidateDiscCore F q 1 = centeredGammaDisc (q 1) (finiteValue (r 1) hr1) := by
    ext y
    constructor
    · intro hy
      exact (rawOpenBall_iff_centeredGammaDisc _ _ _ hr1).mp (hy r hrF)
    · intro hy
      obtain ⟨x,hx,hxy⟩ := hImage.symm ▸ hy
      have hxCore : x ∈ candidateDiscCore F q 0 := hSource.symm ▸ hx
      intro t ht
      obtain ⟨ht0,ht1,hImageT⟩ := hPair t ht
      have hxT := (rawOpenBall_iff_centeredGammaDisc _ _ _ ht0).mp (hxCore t ht)
      have hyT : y ∈ centeredGammaDisc (q 1) (finiteValue (t 1) ht1) :=
        hImageT ▸ ⟨x,hxT,hxy⟩
      exact (rawOpenBall_iff_centeredGammaDisc _ _ _ ht1).mpr hyT
  exact ⟨r,hrF,hr0,hr1,hSource,hTarget,by rw [hSource,hTarget]; exact hImage⟩

end DiamondIntegral.Section6
