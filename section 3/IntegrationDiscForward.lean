import «section 3».IntegrationDiscRadii
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Native finite-disc definability implies full interpreted-base definability without naming representatives. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {k n : ℕ}

def integrationDiscProper (z : (Fin k ⊕ Fin k) ⊕ Fin n → M) : Prop :=
  ∀ i, iVF (z (.inl (.inl i))) ∧ iVF (z (.inl (.inr i))) ∧ z (.inl (.inr i)) ≠ iVFZero

theorem integrationVFCoordinate_definable (B : FullBaseAtomicity.Base (M := M))
    {α : Type} [Finite α] (j : α) :
    FullBaseAtomicity.OverBase B {z : α → M | iVF (z j)} := by
  have hu := ((definableOver_iff_normalized_raw B.real (fun _ : Fin 1 => .vf)
    {z | iVF (z 0)}).mp (definableAt_sort B.real .vf).1).1
  exact FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hu)
    (fun _ : Fin 1 => j)

theorem integrationZeroCoordinate_definable (B : FullBaseAtomicity.Base (M := M))
    {α : Type} [Finite α] (j : α) :
    FullBaseAtomicity.OverBase B {z : α → M | z j = iVFZero} := by
  have hz : DefinableClosureAt B.real .vf (0 : VFType (M := M)).val :=
    (vfDefinableClosureField B.real).zero_mem
  have hu := ((definableOver_iff_normalized_raw B.real (fun _ : Fin 1 => .vf)
    {z | z 0 = (0 : VFType (M := M)).val}).mp hz.1).1
  exact FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hu)
    (fun _ : Fin 1 => j)

theorem integrationDiscProper_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {z : (Fin k ⊕ Fin k) ⊕ Fin n → M | integrationDiscProper z} := by
  apply FullBaseAtomicity.OverBase.forall_finite
  intro i
  exact FullBaseAtomicity.OverBase.inter (integrationVFCoordinate_definable B (α := (Fin k ⊕ Fin k) ⊕ Fin n) (.inl (.inl i)))
    (FullBaseAtomicity.OverBase.inter (integrationVFCoordinate_definable B (α := (Fin k ⊕ Fin k) ⊕ Fin n) (.inl (.inr i)))
      (FullBaseAtomicity.OverBase.compl (integrationZeroCoordinate_definable B (α := (Fin k ⊕ Fin k) ⊕ Fin n) (.inl (.inr i)))))

def integrationDiscBody (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) :
    Set ((Fin k ⊕ Fin k) ⊕ Fin n → M) :=
  {z | integrationDiscProper z ∧
    integrationDiscRadiiMap z ∈ integrationGammaTailRelation R.relation (fun i => Sum.inr (R.support i)) ∧
    ∀ i, integrationDiscCode (closed i) ![z (.inl (.inl i)),z (.inl (.inr i))] ∈
      (@ParameterPresentation.presentation M sM hM).pullback
        {Sum.inl (Section2.finitePolydiscNames closed a δ i)}}

theorem integrationDiscBody_definable (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) :
    FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) (integrationDiscBody B R a δ) := by
  let C := integrationDiscBase B closed a δ
  have hr : FullBaseAtomicity.OverBase C
      (integrationGammaTailRelation R.relation (fun i => Sum.inr (R.support i))) :=
    FullBaseAtomicity.OverBase.mono
      (integrationGammaTailOverBase B R.relation R.support R.support_mem)
      Set.Subset.rfl (integrationDiscBase_mono B closed a δ)
  have hm := FullBaseAtomicity.OverBase.preimage_map hr (integrationDiscRadiiMap_definable B.real)
  have hn (i : Fin k) := FullBaseAtomicity.OverBase.preimage_comp
    (integrationNamedDiscCodes C (Section2.finitePolydiscNames closed a δ i)
      (integrationDiscBase_name B closed a δ i) (closed i))
    (![Sum.inl (Sum.inl i),Sum.inl (Sum.inr i)] : Fin 2 → (Fin k ⊕ Fin k) ⊕ Fin n)
  exact FullBaseAtomicity.OverBase.inter (integrationDiscProper_definable C)
    (FullBaseAtomicity.OverBase.inter hm (FullBaseAtomicity.OverBase.forall_finite hn))
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {k n : ℕ}

theorem integrationDiscProper_point (a r : Fin k → Section2.VF M) (hr : ∀ i, r i ≠ 0) (b : Fin n → M) :
    integrationDiscProper (integrationDiscPoint a r b) := by
  intro i
  exact ⟨(a i).property,(r i).property,fun he => hr i (Subtype.ext he)⟩

theorem integrationDiscBody_row (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a x r : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (hr : ∀ i, r i ≠ 0) (b : Fin n → M) :
    integrationDiscPoint x r b ∈ integrationDiscBody B R a δ ↔
      b ∈ R.fibre x (fun i => Section2.finiteValue (r i) (hr i)) ∧
      Section2.finitePolydiscNames closed x (fun i => Section2.finiteValue (r i) (hr i)) =
        Section2.finitePolydiscNames closed a δ := by
  constructor
  · rintro ⟨_,hg,hn⟩
    refine ⟨(integrationDiscTail_row B R x r hr b).mp hg,?_⟩
    funext i
    exact (integrationNamedDiscCodes_row (Section2.finitePolydiscNames closed a δ i)
      (closed i) (x i) (r i) (hr i)).mp (hn i)
  · rintro ⟨hg,hn⟩
    refine ⟨integrationDiscProper_point x r hr b,(integrationDiscTail_row B R x r hr b).mpr hg,?_⟩
    intro i
    exact (integrationNamedDiscCodes_row (Section2.finitePolydiscNames closed a δ i)
      (closed i) (x i) (r i) (hr i)).mpr (congrFun hn i)

def integrationDiscCut (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) : Set (Fin n → M) :=
  {b | ∃ q : Fin k ⊕ Fin k → M, Sum.elim q b ∈ integrationDiscBody B R a δ}

theorem integrationDiscCut_definable (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) :
    FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) (integrationDiscCut B R a δ) := by
  have hd := FullBaseAtomicity.OverBase.preimage_comp (integrationDiscBody_definable B R a δ)
    (Sum.swap : (Fin k ⊕ Fin k) ⊕ Fin n → Fin n ⊕ (Fin k ⊕ Fin k))
  have he := FullBaseAtomicity.OverBase.exists_block hd
  convert he using 1
  ext b
  have hs (q : Fin k ⊕ Fin k → M) : Sum.elim b q ∘ Sum.swap = Sum.elim q b := by
    funext j
    cases j <;> rfl
  change (∃ q, Sum.elim q b ∈ integrationDiscBody B R a δ) ↔
    ∃ q, Sum.elim b q ∘ Sum.swap ∈ integrationDiscBody B R a δ
  simp only [hs]

theorem integrationDiscCut_eq_fibre (B : GammaParameters.Base (M := M)) {sn : Fin n → SortTag}
    {closed : Fin k → Bool} (R : Section2.FiniteDiscTupleRelation B closed sn)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) :
    integrationDiscCut B R a δ = R.fibre a δ := by
  ext b
  constructor
  · rintro ⟨q,hq⟩
    let x : Fin k → Section2.VF M := fun i => ⟨q (.inl i),(hq.1 i).1⟩
    let r : Fin k → Section2.VF M := fun i => ⟨q (.inr i),(hq.1 i).2.1⟩
    have hr (i : Fin k) : r i ≠ 0 := fun he => (hq.1 i).2.2 (congrArg Subtype.val he)
    have hp : integrationDiscPoint x r b = Sum.elim q b := by
      funext j
      cases j with
      | inr j => rfl
      | inl j => cases j <;> rfl
    have hrow := integrationDiscBody_row B R a x r δ hr b
    rw [hp] at hrow
    obtain ⟨hg,hn⟩ := hrow.mp hq
    rw [R.fibre_eq_of_names x a _ δ hn] at hg
    exact hg
  · intro hb
    let r (i : Fin k) : Section2.VF M := Section2.radiusRepresentative (δ i).val
    have hr (i : Fin k) : r i ≠ 0 :=
      fun he => (δ i).property ((Section2.radiusRepresentative_zero_iff _).mp he)
    have hv : (fun i => Section2.finiteValue (r i) (hr i)) = δ := by
      funext i
      exact Subtype.ext (Section2.radiusRepresentative_value (δ i).val)
    have hm : integrationDiscPoint a r b ∈ integrationDiscBody B R a δ := by
      apply (integrationDiscBody_row B R a a r δ hr b).mpr
      rw [hv]
      exact ⟨hb,rfl⟩
    exact ⟨Sum.elim (fun i => (a i).val) (fun i => (r i).val),hm⟩

theorem integrationFiniteDiscDefinable_to_full (B : GammaParameters.Base (M := M))
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : Section2.DefinableOverFiniteDiscNames B closed a δ sn A) :
    FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) A := by
  obtain ⟨R,rfl⟩ := hA
  rw [← integrationDiscCut_eq_fibre B R a δ]
  exact integrationDiscCut_definable B R a δ
end DiamondIntegral.Section3
