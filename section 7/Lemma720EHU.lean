import «section 7».Lemma720Closest

/-! Lemma 7.20, step 14b: the positioning functions over the target points, in raw form.

`EHU v` says: the first block of `v` codes a point `u` of the target of the second stage,
`x` lies in the second-stage disc over `u`, and `e = εU u x`. It is definable over the
base (`EHU_definable`) and has the expected meaning (`EHU_iff`, `EHU_target`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Final
variable {B : DefSet (rawMixedSpace (M := M) 1 a) S} (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M)) (T₂ : StandardContractionStage (G := G) B)
  (hD₂ : SameLabelShearDisplacement T₂.lift (Fin.last 0))

/-- The raw graph of the second-stage offset. -/
def offsetRaw : Set ((Fin 0 ⊕ Fin T₂.arity) ⊕ Fin 1 → M) :=
  (rawMixedSpace (M := M) 0 T₂.arity).relation (rawVFSpace (M := M) 1) (Stage.offset T₂ hD₂).graph

theorem offsetRaw_definable : S.Definable LRV (offsetRaw T₂ hD₂) := (Stage.offset T₂ hD₂).graph_definable

theorem mem_offsetRaw_iff (z : (Fin 0 ⊕ Fin T₂.arity) ⊕ Fin 1 → M) :
    z ∈ offsetRaw T₂ hD₂ ↔ ∃ s : T₂.contracted,
      Sum.elim (mixedValues s.val) (vfValues (Stage.offset T₂ hD₂ s).val) = z := by
  constructor
  · rintro ⟨hx, hy, q, hq, hfq⟩
    have he₁ : mixedValues q.val = z ∘ Sum.inl := by rw [hq]; exact mixedValues_decode _
    have he₂ : vfValues (Stage.offset T₂ hD₂ q).val = z ∘ Sum.inr := by rw [hfq]; exact vfValues_decode _
    exact ⟨q, by funext i; cases i with
      | inl i => exact congrFun he₁ i
      | inr i => exact congrFun he₂ i⟩
  · rintro ⟨q, rfl⟩
    refine ⟨mixedValues_mem_domain q.val, ⟨(Stage.offset T₂ hD₂ q).val, rfl⟩, q, ?_, ?_⟩
    · exact (decode_mixedValues q.val).symm
    · exact (decode_vfValues (Stage.offset T₂ hD₂ q).val).symm

/-- The raw positioning relation over target points. -/
def EHU (v : (Fin T₂.arity ⊕ Fin 1) ⊕ Fin 1 → M) : Prop :=
  Sum.elim (Fin.elim0 : Fin 0 → M) (v ∘ Sum.inl ∘ Sum.inl) ∈ mixedValues '' T₂.contracted.carrier ∧
    (∃ c : M, Sum.elim (Sum.elim (Fin.elim0 : Fin 0 → M) (v ∘ Sum.inl ∘ Sum.inl)) (fun _ : Fin 1 => c) ∈
        offsetRaw T₂ hD₂ ∧ iVF (v (.inl (.inr 0))) ∧
        iRv (iVFAdd (v (.inl (.inr 0))) (iVFNeg c)) = v (.inl (.inl T₂.leading))) ∧
    EHR B ε lead Q (Sum.elim (Sum.elim (fun _ : Fin 1 => v (.inl (.inr 0)))
      (fun i => v (.inl (.inl (T₂.oldLabels i))))) (fun _ : Fin 1 => v (.inr 0)))

/-- Points of a second-stage disc give points of `B`. -/
theorem mkPoint_mem_of_Dof (s : T₂.contracted) {x : VF M} (hx : x ∈ Dof T₂ hD₂ s.val.2) :
    mkPoint x (wOf T₂ s.val.2) ∈ B.carrier := by
  have hs : ((Fin.elim0 : Fin 0 → VF M), s.val.2) ∈ T₂.contracted.carrier := by
    have : s.val = ((Fin.elim0 : Fin 0 → VF M), s.val.2) := Prod.ext (funext fun i => i.elim0) rfl
    rw [← this]
    exact s.property
  have hss : (⟨((Fin.elim0 : Fin 0 → VF M), s.val.2), hs⟩ : T₂.contracted) = s :=
    Subtype.ext (Prod.ext (funext fun i => i.elim0) rfl)
  have hx' : rv M (x - Stage.eps T₂ hD₂ s) = s.val.2 T₂.leading := by
    have := hx
    change rv M (x - cOf T₂ hD₂ s.val.2) = _ at this
    rw [cOf, dif_pos hs, hss] at this
    exact this
  obtain ⟨b, hb, hbx⟩ := Stage.exists_mem_fibre T₂ hD₂ s x hx'
  obtain ⟨-, hlab, -⟩ := (Stage.contraction_eq_iff T₂ hD₂ b s).mp hb
  have : b.val = mkPoint x (wOf T₂ s.val.2) := by
    refine Prod.ext ?_ (funext hlab)
    funext i
    obtain rfl : i = 0 := Fin.ext (by have := i.isLt; omega)
    exact hbx
  rw [← this]
  exact b.property

theorem target_mem (s : T₂.contracted) :
    ((Fin.elim0 : Fin 0 → VF M), s.val.2) ∈ T₂.contracted.carrier := by
  have : s.val = ((Fin.elim0 : Fin 0 → VF M), s.val.2) := Prod.ext (funext fun i => i.elim0) rfl
  rw [← this]
  exact s.property

theorem cOf_eq (s : T₂.contracted) : cOf T₂ hD₂ s.val.2 = Stage.eps T₂ hD₂ s := by
  rw [cOf, dif_pos (target_mem T₂ s)]
  have hss : (⟨((Fin.elim0 : Fin 0 → VF M), s.val.2), target_mem T₂ s⟩ : T₂.contracted) = s :=
    Subtype.ext (Prod.ext (funext fun i => i.elim0) rfl)
  rw [hss]

theorem target_codes (s : T₂.contracted) :
    Sum.elim (Fin.elim0 : Fin 0 → M) (rvValues s.val.2) = mixedValues s.val := by
  funext i
  rcases i with i | i
  · exact i.elim0
  · rfl

theorem EHU_iff (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M) (s : T₂.contracted) (x : VF M) (e : M) :
    EHU ε lead Q T₂ hD₂ (Sum.elim (Sum.elim (rvValues s.val.2) (fun _ : Fin 1 => x.val)) (fun _ : Fin 1 => e)) ↔
      x ∈ Dof T₂ hD₂ s.val.2 ∧ e = (εU ε lead Q T₂ s.val.2 x).val := by
  have hoff : ∀ c : M, Sum.elim (Sum.elim (Fin.elim0 : Fin 0 → M) (rvValues s.val.2)) (fun _ : Fin 1 => c) ∈
      offsetRaw T₂ hD₂ ↔ c = (Stage.eps T₂ hD₂ s).val := by
    intro c
    rw [mem_offsetRaw_iff]
    constructor
    · rintro ⟨s', hs'⟩
      have h1 : mixedValues s'.val = mixedValues s.val :=
        (congrArg (fun g => g ∘ Sum.inl) hs').trans (target_codes T₂ s)
      have hss : s' = s := Subtype.ext (mixedValues_injective h1)
      subst hss
      exact (congrFun hs' (.inr 0)).symm
    · rintro rfl
      refine ⟨s, ?_⟩
      funext i
      rcases i with i | i
      · rw [← target_codes]; rfl
      · have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
  have hEHR : Sum.elim (Sum.elim (fun _ : Fin 1 => x.val) (fun i => (rvValues s.val.2) (T₂.oldLabels i)))
      (fun _ : Fin 1 => e) = Sum.elim (mixedValues (mkPoint x (wOf T₂ s.val.2))) ![e] := by
    funext i
    rcases i with (i | i) | i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
    · rfl
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  change (Sum.elim (Fin.elim0 : Fin 0 → M) (rvValues s.val.2) ∈ mixedValues '' T₂.contracted.carrier ∧
    (∃ c : M, Sum.elim (Sum.elim (Fin.elim0 : Fin 0 → M) (rvValues s.val.2)) (fun _ : Fin 1 => c) ∈
        offsetRaw T₂ hD₂ ∧ iVF x.val ∧ iRv (iVFAdd x.val (iVFNeg c)) = (s.val.2 T₂.leading).val) ∧
    EHR B ε lead Q (Sum.elim (Sum.elim (fun _ : Fin 1 => x.val)
      (fun i => (rvValues s.val.2) (T₂.oldLabels i))) (fun _ : Fin 1 => e))) ↔ _
  rw [hEHR, EHR_iff B ε lead Q hv hlead]
  have hDof : x ∈ Dof T₂ hD₂ s.val.2 ↔ iRv (iVFAdd x.val (iVFNeg (Stage.eps T₂ hD₂ s).val)) =
      (s.val.2 T₂.leading).val := by
    change rv M (x - cOf T₂ hD₂ s.val.2) = _ ↔ _
    rw [cOf_eq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  constructor
  · rintro ⟨-, ⟨c, hc, -, hrv⟩, -, he⟩
    rw [hoff] at hc
    subst hc
    exact ⟨hDof.mpr hrv, he⟩
  · rintro ⟨hx, he⟩
    refine ⟨⟨s.val, s.property, (target_codes T₂ s).symm⟩, ⟨_, (hoff _).mpr rfl, x.property, hDof.mp hx⟩,
      mkPoint_mem_of_Dof T₂ hD₂ s hx, he⟩

theorem elim0_eq {α : Type} (f : Fin 0 → α) : f = Fin.elim0 := funext fun i => i.elim0

theorem EHU_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M)))) :
    S.Definable LRV {v | EHU ε lead Q T₂ hD₂ v} := by
  let V := (Fin T₂.arity ⊕ Fin 1) ⊕ Fin 1
  let W := V ⊕ Fin 1
  have hT : S.Definable LRV (mixedValues '' T₂.contracted.carrier) := by
    rw [← preimage_eq_image]; exact T₂.contracted.definable
  have hT' := hT.preimage_comp (Sum.elim (Fin.elim0 : Fin 0 → V) (fun j => Sum.inl (Sum.inl j)))
  have hO := (offsetRaw_definable T₂ hD₂).preimage_comp
    (Sum.elim (Sum.elim (Fin.elim0 : Fin 0 → W) (fun j => Sum.inl (Sum.inl (Sum.inl j)))) (fun _ => Sum.inr 0))
  have hX := (vf_sort_definable hc S).preimage_comp (fun _ : Fin 1 => (Sum.inl (Sum.inl (Sum.inr 0)) : W))
  have hfun : S.DefinableFun LRV (fun w : W → M =>
      iRv (iVFAdd (w (Sum.inl (Sum.inl (Sum.inr 0)))) (iVFNeg (w (Sum.inr 0))))) := by
    have hneg : S.DefinableFun LRV (fun w : W → M => iVFNeg (w (Sum.inr 0))) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
        (show S.DefinableMap LRV (fun w : W → M => ![w (Sum.inr 0)]) from by
          intro k; fin_cases k; exact Set.DefinableFun.proj LRV)
    have hadd : S.DefinableFun LRV (fun w : W → M =>
        iVFAdd (w (Sum.inl (Sum.inl (Sum.inr 0)))) (iVFNeg (w (Sum.inr 0)))) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
        (show S.DefinableMap LRV (fun w : W → M =>
          ![w (Sum.inl (Sum.inl (Sum.inr 0))), iVFNeg (w (Sum.inr 0))]) from by
          intro k; fin_cases k
          · exact Set.DefinableFun.proj LRV
          · exact hneg)
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun w : W → M =>
        ![iVFAdd (w (Sum.inl (Sum.inl (Sum.inr 0)))) (iVFNeg (w (Sum.inr 0)))]) from by
        intro k; fin_cases k; exact hadd)
  have hEq := hfun.ofPred_eq (Set.DefinableFun.proj LRV :
    S.DefinableFun LRV (fun w : W → M => w (Sum.inl (Sum.inl (Sum.inl T₂.leading)))))
  have hEx := definable_of_overBase hc (FullBaseAtomicity.OverBase.exists_block
    (overBase_of_definable hc (hO.inter (hX.inter hEq))))
  have hE := (EHR_definable B ε lead Q hc hQ).preimage_comp
    (Sum.elim (Sum.elim (fun _ : Fin 1 => (Sum.inl (Sum.inr 0) : V))
      (fun i => Sum.inl (Sum.inl (T₂.oldLabels i)))) (fun _ : Fin 1 => Sum.inr 0))
  convert hT'.inter (hEx.inter hE) using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h1, ⟨c, hc1, hc2, hc3⟩, h3⟩
    refine ⟨?_, ⟨![c], ?_, ?_, ?_⟩, ?_⟩
    · convert h1 using 1
      funext i; rcases i with i | i
      · exact i.elim0
      · rfl
    · convert hc1 using 1
      funext i; rcases i with (i | i) | i
      · exact i.elim0
      · rfl
      · rfl
    · exact hc2
    · exact hc3
    · convert h3 using 1
      funext i; rcases i with (i | i) | i <;> rfl
  · rintro ⟨h1, ⟨c, hc1, hc2, hc3⟩, h3⟩
    refine ⟨?_, ⟨c 0, ?_, hc2, hc3⟩, ?_⟩
    · convert h1 using 1
      funext i; rcases i with i | i
      · exact i.elim0
      · rfl
    · convert hc1 using 1
      funext i; rcases i with (i | i) | i
      · exact i.elim0
      · rfl
      · rfl
    · convert h3 using 1
      funext i; rcases i with (i | i) | i <;> rfl

theorem EHU_target {v : (Fin T₂.arity ⊕ Fin 1) ⊕ Fin 1 → M} (h : EHU ε lead Q T₂ hD₂ v) :
    ∃ s : T₂.contracted, ∃ x : VF M, v = Sum.elim (Sum.elim (rvValues s.val.2) (fun _ : Fin 1 => x.val))
      (fun _ : Fin 1 => v (.inr 0)) := by
  obtain ⟨⟨q, hq, hqv⟩, ⟨c, -, hx, -⟩, -⟩ := h
  refine ⟨⟨q, hq⟩, ⟨v (.inl (.inr 0)), hx⟩, ?_⟩
  funext i
  rcases i with (i | i) | i
  · exact (congrFun hqv (.inr i)).symm
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl

end Final

end DiamondIntegral.Section7.Lemma720
