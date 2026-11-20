import «section 7».Lemma720Uniform

/-! Lemma 7.20, step 14a: the graph of the final positioning map is definable.

`closestRaw Q x z` says, with raw balls, that `z` is the strictly closest point of `Q` to
`x` (`closestRaw_iff`). The graph of `epsHat` on `B` is described by the raw condition
`EHR` (`EHR_iff`), which is definable over the base (`EHR_definable`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
open IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}

namespace Final

/-- `z` is the strictly closest point of `Q` to `x`, in raw form. -/
def closestRaw (Q : Finset (VF M)) (x z : M) : Prop :=
  ∀ z' : M, z' ∈ Subtype.val '' (Q : Set (VF M)) → z' ≠ z →
    ∃ b : M, NonzeroRV b ∧ ball b x z ∧ ¬ ball b x z'

theorem vfValue_zero_eq_infinity : vfValue (0 : VF M) = SpecialTransformations.Section3.Values.infinity := by
  change Values.vfValueHom (0 : VF M) = _
  rw [map_zero, ← Values.infinity_eq_zero]

theorem closestRaw_iff (Q : Finset (VF M)) (x z : VF M) :
    closestRaw Q x.val z.val ↔ ∀ z' ∈ Q, z' ≠ z → vfValue (x - z') < vfValue (x - z) := by
  constructor
  · intro h z' hz' hne
    obtain ⟨b, hb, h1, h2⟩ := h z'.val ⟨z', hz', rfl⟩ (fun he => hne (Subtype.ext he))
    rw [ball_iff_value b hb] at h1 h2
    exact lt_of_le_of_lt (not_lt.mp h2) h1
  · intro h zr hzr hne
    obtain ⟨z', hz', hz'e⟩ : ∃ z' : VF M, z' ∈ Q ∧ z'.val = zr := hzr
    subst hz'e
    have hne' : z' ≠ z := fun he => hne (by rw [he])
    have hlt := h z' hz' hne'
    have hx0 : x - z' ≠ 0 := by
      intro h0
      rw [h0, vfValue_zero_eq_infinity] at hlt
      exact absurd (lt_of_lt_of_le hlt (SpecialTransformations.Section3.Values.le_infinity _)) (lt_irrefl _)
    obtain ⟨b, hb, hbv⟩ := EndpointLogic.codeValue_surjective (gval (x - z') hx0)
    refine ⟨b, hb, ?_, ?_⟩
    · rw [ball_iff_value b hb, hbv, gval_val]
      exact hlt
    · rw [ball_iff_value b hb, hbv, gval_val]
      exact lt_irrefl _

theorem closestRaw_definable (hc : CanonicalStructure.IsCanonical (M := M)) {Q : Finset (VF M)}
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M)))) :
    S.Definable LRV {v : Fin 2 → M | closestRaw Q (v 0) (v 1)} := by
  let B' := fullBase S
  have hQ' : FullBaseAtomicity.OverBase B' {z : Fin 1 → M | z 0 ∈ Subtype.val '' (Q : Set (VF M))} :=
    overBase_of_definable hc hQ
  have hNZ := FullBaseAtomicity.OverBase.of_real (B := B')
    (nonzero_codes_normalized_definable (M := M) B'.real)
  have hEq : FullBaseAtomicity.OverBase B' {z : Fin 2 → M | z 0 = z 1} :=
    overBase_of_definable hc ((Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV))
  have hBall := ball_definable B'
  let ι₁ := Fin 2 ⊕ Fin 1
  let ι₂ := ι₁ ⊕ Fin 1
  have hNZb := FullBaseAtomicity.OverBase.preimage_comp hNZ (fun _ : Fin 1 => (Sum.inr 0 : ι₂))
  have hB1 := FullBaseAtomicity.OverBase.preimage_comp hBall
    (![Sum.inr 0, Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1)] : Fin 3 → ι₂)
  have hB2 := FullBaseAtomicity.OverBase.preimage_comp hBall
    (![Sum.inr 0, Sum.inl (Sum.inl 0), Sum.inl (Sum.inr 0)] : Fin 3 → ι₂)
  have hEx := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter hNZb (FullBaseAtomicity.OverBase.inter hB1
      (FullBaseAtomicity.OverBase.compl hB2)))
  have hQz := FullBaseAtomicity.OverBase.preimage_comp hQ' (fun _ : Fin 1 => (Sum.inr 0 : ι₁))
  have hEqz := FullBaseAtomicity.OverBase.preimage_comp hEq (![Sum.inr 0, Sum.inl 1] : Fin 2 → ι₁)
  have hAll := FullBaseAtomicity.OverBase.forall_block
    (FullBaseLogic.implication B' hQz
      (FullBaseLogic.implication B' (FullBaseAtomicity.OverBase.compl hEqz) hEx))
  apply definable_of_overBase hc
  apply FullBaseAtomicity.OverBase.congr hAll
  intro v
  constructor
  · intro h z' hz' hne
    obtain ⟨b, hb⟩ := h ![z'] hz' hne
    exact ⟨b 0, hb⟩
  · intro h z' hz' hne
    obtain ⟨b, hb⟩ := h (z' 0) hz' hne
    exact ⟨![b], hb⟩

section EH
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M))

/-- A point of a good ball around `z` has `z` as its strictly closest point of `Q`. -/
theorem closest_of_K (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {w : Fin a → RVInfinity M} {z x : VF M}
    (hx : x ∈ Protect.K B.carrier (εfun B ε) lead Q w z) :
    ∀ z' ∈ Q, z' ≠ z → vfValue (x - z') < vfValue (x - z) := by
  obtain ⟨β, hβ, hg⟩ := hx
  intro z' hz' hne
  have hsep : ¬ β.val < vfValue (z' - z) := hg.2 z' hz' hne
  rw [not_lt] at hsep
  have hlt : vfValue (z - z') < vfValue (x - z) := by
    rw [vfValue_sub_comm hv]
    exact lt_of_le_of_lt hsep hβ
  have he : x - z' = (z - z') + (x - z) := by ring
  rw [he, vfValue_add_eq_of_lt hv hlt]
  exact hlt

/-- The raw graph of the final positioning map. -/
def EHR (z : (Fin 1 ⊕ Fin a) ⊕ Fin 1 → M) : Prop :=
  z ∘ Sum.inl ∈ mixedValues '' B.carrier ∧
    ((UR B ε lead Q (z ∘ Sum.inl) ∧ ∃ zq : M, zq ∈ Subtype.val '' (Q : Set (VF M)) ∧
        closestRaw Q (z (.inl (.inl 0))) zq ∧ zq ∈ rawDom B (z ∘ Sum.inl ∘ Sum.inr) ∧
        z (.inr 0) = rawFun B ε (z ∘ Sum.inl ∘ Sum.inr) zq) ∨
      (¬ UR B ε lead Q (z ∘ Sum.inl) ∧ z (.inl (.inl 0)) ∈ rawDom B (z ∘ Sum.inl ∘ Sum.inr) ∧
        z (.inr 0) = rawFun B ε (z ∘ Sum.inl ∘ Sum.inr) (z (.inl (.inl 0)))))

theorem mkPoint_self (q : Mixed M 1 a) : mkPoint (q.1 0) q.2 = q := by
  refine Prod.ext ?_ rfl
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rfl

theorem EHR_iff (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M) (q : Mixed M 1 a) (e : M) :
    EHR B ε lead Q (Sum.elim (mixedValues q) ![e]) ↔ q ∈ B.carrier ∧ e = (epsHat B ε lead Q q).val := by
  change (mixedValues q ∈ mixedValues '' B.carrier ∧
    ((UR B ε lead Q (mixedValues q) ∧ ∃ zq : M, zq ∈ Subtype.val '' (Q : Set (VF M)) ∧
        closestRaw Q (q.1 0).val zq ∧ zq ∈ rawDom B (rvValues q.2) ∧ e = rawFun B ε (rvValues q.2) zq) ∨
      (¬ UR B ε lead Q (mixedValues q) ∧ (q.1 0).val ∈ rawDom B (rvValues q.2) ∧
        e = rawFun B ε (rvValues q.2) (q.1 0).val))) ↔ _
  rw [mixedValues_injective.mem_set_image, ← mem_U_iff_UR B ε lead Q hlead]
  constructor
  · rintro ⟨hqB, (⟨hU, zr, hzr, hcl, hzd, he⟩ | ⟨hU, -, he⟩)⟩
    · obtain ⟨zv, hzv, rfl⟩ : ∃ zv : VF M, zv ∈ Q ∧ zv.val = zr := hzr
      obtain ⟨-, z₀, hz₀, hxK⟩ := hU
      have hcl₀ := closest_of_K B ε lead Q hv hxK
      have hcl' := (closestRaw_iff Q (q.1 0) zv).mp hcl
      have hzz : zv = z₀ := by
        by_contra hne
        exact lt_asymm (hcl' z₀ hz₀ (Ne.symm hne)) (hcl₀ zv hzv hne)
      subst hzz
      refine ⟨hqB, ?_⟩
      rw [epsHat, if_pos ⟨hqB, zv, hzv, hxK⟩, zOf_eq hv hzv hxK]
      rw [he, rawFun_mkPoint B ε q.2 zv ((rawDom_iff B q.2 zv).mp hzd)]
    · refine ⟨hqB, ?_⟩
      rw [epsHat, if_neg hU, he]
      have := rawFun_mkPoint B ε q.2 (q.1 0) (by rw [mkPoint_self]; exact hqB)
      rw [this, mkPoint_self]
  · rintro ⟨hqB, he⟩
    refine ⟨hqB, ?_⟩
    by_cases hU : q ∈ Protect.U B.carrier (εfun B ε) lead Q
    · left
      obtain ⟨-, z₀, hz₀, hxK⟩ := hU
      have hzB : mkPoint z₀ q.2 ∈ B.carrier := by
        obtain ⟨β, -, hg⟩ := hxK
        refine (hg.1 z₀ ?_).1
        rw [sub_self]
        exact SpecialTransformations.Section9.gamma_lt_value_zero β
      refine ⟨⟨hqB, z₀, hz₀, hxK⟩, z₀.val, ⟨z₀, hz₀, rfl⟩,
        (closestRaw_iff Q (q.1 0) z₀).mpr (closest_of_K B ε lead Q hv hxK),
        (rawDom_iff B q.2 z₀).mpr hzB, ?_⟩
      rw [he, epsHat, if_pos ⟨hqB, z₀, hz₀, hxK⟩, zOf_eq hv hz₀ hxK,
        rawFun_mkPoint B ε q.2 z₀ hzB]
    · right
      refine ⟨hU, (rawDom_iff B q.2 (q.1 0)).mpr (by rw [mkPoint_self]; exact hqB), ?_⟩
      rw [he, epsHat, if_neg hU, rawFun_mkPoint B ε q.2 (q.1 0) (by rw [mkPoint_self]; exact hqB),
        mkPoint_self]

theorem EHR_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M)))) :
    S.Definable LRV {z | EHR B ε lead Q z} := by
  let B' := fullBase S
  let ι₀ := (Fin 1 ⊕ Fin a) ⊕ Fin 1
  let ι := ι₀ ⊕ Fin 1
  have hBc : FullBaseAtomicity.OverBase B' (mixedValues '' B.carrier) := by
    apply overBase_of_definable hc
    rw [← preimage_eq_image]
    exact B.definable
  have hUR : FullBaseAtomicity.OverBase B' {c | UR B ε lead Q c} :=
    overBase_of_definable hc (UR_definable B ε lead Q hc hQ)
  have hQ' : FullBaseAtomicity.OverBase B' {z : Fin 1 → M | z 0 ∈ Subtype.val '' (Q : Set (VF M))} :=
    overBase_of_definable hc hQ
  have hCl : FullBaseAtomicity.OverBase B' {v : Fin 2 → M | closestRaw Q (v 0) (v 1)} :=
    overBase_of_definable hc (closestRaw_definable hc hQ)
  have hG := rawFun_graph B hc ε
  -- atoms on ι₀
  have hBc₀ := FullBaseAtomicity.OverBase.preimage_comp hBc (Sum.inl : Fin 1 ⊕ Fin a → ι₀)
  have hUR₀ := FullBaseAtomicity.OverBase.preimage_comp hUR (Sum.inl : Fin 1 ⊕ Fin a → ι₀)
  have hGx := FullBaseAtomicity.OverBase.preimage_comp hG
    (Sum.elim (Sum.elim (fun i => Sum.inl (Sum.inr i)) (fun _ => Sum.inl (Sum.inl 0))) (fun _ => Sum.inr 0) :
      (Fin a ⊕ Fin 1) ⊕ Fin 1 → ι₀)
  -- atoms on ι (with the witness `zq`)
  have hUR₁ := FullBaseAtomicity.OverBase.preimage_comp hUR
    ((fun i => Sum.inl (Sum.inl i)) : Fin 1 ⊕ Fin a → ι)
  have hQz := FullBaseAtomicity.OverBase.preimage_comp hQ' (fun _ : Fin 1 => (Sum.inr 0 : ι))
  have hClz := FullBaseAtomicity.OverBase.preimage_comp hCl
    (![Sum.inl (Sum.inl (Sum.inl 0)), Sum.inr 0] : Fin 2 → ι)
  have hGz := FullBaseAtomicity.OverBase.preimage_comp hG
    (Sum.elim (Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inr i))) (fun _ => Sum.inr 0)) (fun _ => Sum.inl (Sum.inr 0)) :
      (Fin a ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hEx := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter hUR₁ (FullBaseAtomicity.OverBase.inter hQz
      (FullBaseAtomicity.OverBase.inter hClz hGz)))
  have hAll := FullBaseAtomicity.OverBase.inter hBc₀ (FullBaseAtomicity.OverBase.union hEx
    (FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.compl hUR₀) hGx))
  apply definable_of_overBase hc
  apply FullBaseAtomicity.OverBase.congr hAll
  intro z
  constructor
  · rintro ⟨hB, (⟨w, hU, hQw, hCw, hGw⟩ | ⟨hU, hGx'⟩)⟩
    · exact ⟨hB, Or.inl ⟨hU, w 0, hQw, hCw, hGw⟩⟩
    · exact ⟨hB, Or.inr ⟨hU, hGx'⟩⟩
  · rintro ⟨hB, (⟨hU, zq, hQw, hCw, hGw⟩ | ⟨hU, hGx'⟩)⟩
    · exact ⟨hB, Or.inl ⟨![zq], hU, hQw, hCw, hGw⟩⟩
    · exact ⟨hB, Or.inr ⟨hU, hGx'⟩⟩

end EH

end Final

end DiamondIntegral.Section7.Lemma720
