import «section 7».Lemma720Protect

/-! Lemma 7.20, step 10: the protected neighbourhood of the obstacles is definable.

Radii are coded by nonzero RV elements and balls by the upstream raw `ball` relation.
The set `Protect.U` is described by a first-order condition on raw codes (`UR`), and
`U_definable` shows it is definable over the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
open IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}

theorem ball_iff_value (r : M) (hr : NonzeroRV r) (x c : VF M) :
    ball r x.val c.val ↔ (codeValue r).val < vfValue (x - c) :=
  (ball_iff r hr x c).trans (mem_gammaBall_iff c x (codeValue r))

theorem codeValue_rv_val (t : RVInfinity M) (ht : t ≠ rvZero M) :
    (codeValue t.val).val = Values.vrv t := by
  have hr : NonzeroRV t.val := ⟨t.property, fun h => ht (Subtype.ext h)⟩
  simp only [codeValue, dite_eq_left hr]
  rfl

section UDef
variable (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M))

/-- The raw condition describing `Protect.U` on codes. -/
def UR (c : Fin 1 ⊕ Fin a → M) : Prop :=
  c ∈ mixedValues '' B.carrier ∧
    ∃ z b : M, z ∈ Subtype.val '' (Q : Set (VF M)) ∧ NonzeroRV b ∧ ball b (c (.inl 0)) z ∧
      (∀ x' : M, ball b x' z → x' ∈ rawDom B (c ∘ Sum.inr) ∧
        ∀ y₁ y₂ : M, (x' ∈ rawDom B (c ∘ Sum.inr) ∧ y₁ = rawFun B ε (c ∘ Sum.inr) x') →
          (z ∈ rawDom B (c ∘ Sum.inr) ∧ y₂ = rawFun B ε (c ∘ Sum.inr) z) → ball (c (.inr lead)) y₁ y₂) ∧
      (∀ z' : M, z' ∈ Subtype.val '' (Q : Set (VF M)) → z' ≠ z → ¬ ball b z' z)

theorem UR_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M)))) :
    S.Definable LRV {c | UR B ε lead Q c} := by
  let B' := fullBase S
  -- atoms
  have hBc : FullBaseAtomicity.OverBase B' (mixedValues '' B.carrier) := by
    apply overBase_of_definable hc
    rw [← preimage_eq_image]
    exact B.definable
  have hQ' : FullBaseAtomicity.OverBase B' {z : Fin 1 → M | z 0 ∈ Subtype.val '' (Q : Set (VF M))} :=
    overBase_of_definable hc hQ
  have hNZ := FullBaseAtomicity.OverBase.of_real (B := B')
    (nonzero_codes_normalized_definable (M := M) B'.real)
  have hG := rawFun_graph B hc ε
  have hDom := FiniteScalarFamilies.domain_definable B' (rawDom B) (rawFun B ε) hG
  have hBall := ball_definable B'
  have hEq : FullBaseAtomicity.OverBase B' {z : Fin 2 → M | z 0 = z 1} :=
    overBase_of_definable hc ((Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV))
  -- index types
  let ι₀ := Fin 1 ⊕ Fin a
  let ι₁ := ι₀ ⊕ Fin 2          -- z = .inr 0, b = .inr 1
  let ι₂ := ι₁ ⊕ Fin 1          -- x'
  let ι₃ := ι₂ ⊕ Fin 2          -- y₁, y₂
  -- the inner universal clause on (c, z, b, x', y₁, y₂)
  have hG1 := FullBaseAtomicity.OverBase.preimage_comp hG
    (Sum.elim (Sum.elim (fun i => (Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))) : Fin a → ι₃)
      (fun _ => Sum.inl (Sum.inr 0))) (fun _ => Sum.inr 0) : (Fin a ⊕ Fin 1) ⊕ Fin 1 → ι₃)
  have hG2 := FullBaseAtomicity.OverBase.preimage_comp hG
    (Sum.elim (Sum.elim (fun i => (Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))) : Fin a → ι₃)
      (fun _ => Sum.inl (Sum.inl (Sum.inr 0)))) (fun _ => Sum.inr 1) : (Fin a ⊕ Fin 1) ⊕ Fin 1 → ι₃)
  have hBy := FullBaseAtomicity.OverBase.preimage_comp hBall
    (![Sum.inl (Sum.inl (Sum.inl (Sum.inr lead))), Sum.inr 0, Sum.inr 1] : Fin 3 → ι₃)
  have hInner := FullBaseAtomicity.OverBase.forall_block
    (FullBaseLogic.implication B' hG1 (FullBaseLogic.implication B' hG2 hBy))
  have hDx := FullBaseAtomicity.OverBase.preimage_comp hDom
    (Sum.elim (fun i => (Sum.inl (Sum.inl (Sum.inr i)))) (fun _ => Sum.inr 0) : Fin a ⊕ Fin 1 → ι₂)
  have hBx := FullBaseAtomicity.OverBase.preimage_comp hBall
    (![Sum.inl (Sum.inr 1), Sum.inr 0, Sum.inl (Sum.inr 0)] : Fin 3 → ι₂)
  have hAll1 := FullBaseAtomicity.OverBase.forall_block
    (FullBaseLogic.implication B' hBx (FullBaseAtomicity.OverBase.inter hDx hInner))
  -- the separation clause on (c, z, b, z')
  have hQz' := FullBaseAtomicity.OverBase.preimage_comp hQ' (fun _ : Fin 1 => (Sum.inr 0 : ι₂))
  have hEqz := FullBaseAtomicity.OverBase.preimage_comp hEq
    (![Sum.inr 0, Sum.inl (Sum.inr 0)] : Fin 2 → ι₂)
  have hBz := FullBaseAtomicity.OverBase.preimage_comp hBall
    (![Sum.inl (Sum.inr 1), Sum.inr 0, Sum.inl (Sum.inr 0)] : Fin 3 → ι₂)
  have hAll2 := FullBaseAtomicity.OverBase.forall_block
    (FullBaseLogic.implication B' hQz' (FullBaseLogic.implication B'
      (FullBaseAtomicity.OverBase.compl hEqz) (FullBaseAtomicity.OverBase.compl hBz)))
  -- the existential clause on (c, z, b)
  have hQz := FullBaseAtomicity.OverBase.preimage_comp hQ' (fun _ : Fin 1 => (Sum.inr 0 : ι₁))
  have hNZb := FullBaseAtomicity.OverBase.preimage_comp hNZ (fun _ : Fin 1 => (Sum.inr 1 : ι₁))
  have hBc' := FullBaseAtomicity.OverBase.preimage_comp hBall
    (![Sum.inr 1, Sum.inl (Sum.inl 0), Sum.inr 0] : Fin 3 → ι₁)
  have hEx := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter hQz (FullBaseAtomicity.OverBase.inter hNZb
      (FullBaseAtomicity.OverBase.inter hBc' (FullBaseAtomicity.OverBase.inter hAll1 hAll2))))
  apply definable_of_overBase hc
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hBc hEx)
  intro c
  constructor
  · rintro ⟨hcB, zb, hz, hb, hball, h1, h2⟩
    refine ⟨hcB, zb 0, zb 1, hz, hb, hball, fun x' hx' => ?_, fun z' hz' hne hb' => ?_⟩
    · obtain ⟨hd, hrest⟩ := h1 ![x'] hx'
      refine ⟨hd, fun y₁ y₂ hy₁ hy₂ => hrest ![y₁, y₂] hy₁ hy₂⟩
    · exact h2 ![z'] hz' hne hb'
  · rintro ⟨hcB, z, b, hz, hb, hball, h1, h2⟩
    refine ⟨hcB, ![z, b], hz, hb, hball, fun x' hx' => ?_, fun z' hz' hne hb' => ?_⟩
    · obtain ⟨hd, hrest⟩ := h1 (x' 0) hx'
      exact ⟨hd, fun yy hy₁ hy₂ => hrest (yy 0) (yy 1) hy₁ hy₂⟩
    · exact h2 (z' 0) hz' hne hb'

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem rawDom_iff (w : Fin a → RVInfinity M) (x : VF M) :
    x.val ∈ rawDom B (rvValues w) ↔ mkPoint x w ∈ B.carrier := by
  constructor
  · rintro ⟨q, hqx, hqw⟩
    have : q.val = mkPoint x w := by
      refine Prod.ext ?_ (rvValues_injective hqw)
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact Subtype.ext hqx
    rw [← this]
    exact q.property
  · intro h
    exact ⟨⟨mkPoint x w, h⟩, rfl, rfl⟩

theorem rawFun_mkPoint (w : Fin a → RVInfinity M) (x : VF M) (h : mkPoint x w ∈ B.carrier) :
    rawFun B ε (rvValues w) x.val = (εfun B ε (mkPoint x w)).val := by
  have := rawFun_point B ε ⟨mkPoint x w, h⟩
  change rawFun B ε (rvValues w) x.val = _ at this
  rw [this, εfun_of_mem B ε ⟨mkPoint x w, h⟩]

/-- **`U` is cut out by the raw condition.** -/
theorem mem_U_iff_UR (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M) (q : Mixed M 1 a) :
    q ∈ Protect.U B.carrier (εfun B ε) lead Q ↔ UR B ε lead Q (mixedValues q) := by
  have hball_self (b : M) (hb : NonzeroRV b) (z : VF M) : ball b z.val z.val := by
    rw [ball_iff_value b hb, sub_self]
    exact SpecialTransformations.Section9.gamma_lt_value_zero _
  constructor
  · rintro ⟨hqB, z, hzQ, β, hβ, hgood⟩
    have ht : NonzeroRV (q.2 lead).val := ⟨(q.2 lead).property, fun h => hlead q hqB (Subtype.ext h)⟩
    obtain ⟨b, hb, hbβ⟩ := EndpointLogic.codeValue_surjective β
    refine ⟨⟨q, hqB, rfl⟩, z.val, b, ⟨z, hzQ, rfl⟩, hb, ?_, fun x' hx' => ?_, fun z' hz' hne hb' => ?_⟩
    · change ball b (q.1 0).val z.val
      rw [ball_iff_value b hb, hbβ]
      exact hβ
    · let xv : VF M := ⟨x', hx'.1⟩
      have hx'β : β.val < vfValue (xv - z) := by
        have := (ball_iff_value b hb xv z).mp hx'
        rwa [hbβ] at this
      obtain ⟨hxB, hval⟩ := hgood.1 xv hx'β
      have hzB : mkPoint z q.2 ∈ B.carrier := (hgood.1 z (by
        rw [sub_self]; exact SpecialTransformations.Section9.gamma_lt_value_zero β)).1
      have hxd : x' ∈ rawDom B (mixedValues q ∘ Sum.inr) := (rawDom_iff B q.2 xv).mpr hxB
      refine ⟨hxd, fun y₁ y₂ hy₁ hy₂ => ?_⟩
      change ball (q.2 lead).val y₁ y₂
      have e1 : y₁ = (εfun B ε (mkPoint xv q.2)).val := hy₁.2.trans (rawFun_mkPoint B ε q.2 xv hxB)
      have e2 : y₂ = (εfun B ε (mkPoint z q.2)).val := hy₂.2.trans (rawFun_mkPoint B ε q.2 z hzB)
      rw [e1, e2, ball_iff_value _ ht, codeValue_rv_val _ (hlead q hqB)]
      exact hval
    · obtain ⟨z'v, hz'Q, rfl⟩ := hz'
      have hne' : z'v ≠ z := fun h => hne (by rw [h])
      apply hgood.2 z'v hz'Q hne'
      have := (ball_iff_value b hb z'v z).mp hb'
      rwa [hbβ] at this
  · rintro ⟨⟨q', hq'B, hq'q⟩, zr, b, ⟨z, hzQ, rfl⟩, hb, hball, h1, h2⟩
    have hqB : q ∈ B.carrier := by rw [← mixedValues_injective hq'q]; exact hq'B
    have ht : NonzeroRV (q.2 lead).val := ⟨(q.2 lead).property, fun h => hlead q hqB (Subtype.ext h)⟩
    have hzd := (h1 z.val (hball_self b hb z)).1
    have hzB : mkPoint z q.2 ∈ B.carrier := (rawDom_iff B q.2 z).mp hzd
    refine ⟨hqB, z, hzQ, codeValue b, (ball_iff_value b hb (q.1 0) z).mp hball, fun x' hx' => ?_, fun z' hz' hne hlt => ?_⟩
    · have hbx : ball b x'.val z.val := (ball_iff_value b hb x' z).mpr hx'
      obtain ⟨hxd, hrest⟩ := h1 x'.val hbx
      have hxB : mkPoint x' q.2 ∈ B.carrier := (rawDom_iff B q.2 x').mp hxd
      refine ⟨hxB, ?_⟩
      have hb' := hrest _ _ ⟨hxd, rfl⟩ ⟨hzd, rfl⟩
      change ball (q.2 lead).val (rawFun B ε (rvValues q.2) x'.val) (rawFun B ε (rvValues q.2) z.val) at hb'
      rw [rawFun_mkPoint B ε q.2 x' hxB, rawFun_mkPoint B ε q.2 z hzB, ball_iff_value _ ht,
        codeValue_rv_val _ (hlead q hqB)] at hb'
      exact hb'
    · apply h2 z'.val ⟨z', hz', rfl⟩ (fun h => hne (Subtype.ext h))
      exact (ball_iff_value b hb z' z).mpr hlt

/-- **`U` is definable over the base.** -/
theorem U_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
    (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M) :
    (rawMixedSpace (M := M) 1 a).Definable S (Protect.U B.carrier (εfun B ε) lead Q) :=
  mixed_definable_of_codes _ _ (UR_definable B ε lead Q hc hQ) (mem_U_iff_UR B ε lead Q hlead)

end UDef

end DiamondIntegral.Section7.Lemma720
