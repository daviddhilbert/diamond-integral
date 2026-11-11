import «section 2».OpenDiscValue
import «section 2».DiscTupleParameters
import «section 2».DiscNameProducts
import Section8.GammaRadiusBase

/-! Every open polydisc is definable over its own actual DC tuple.
The full Gamma-code preimage is definable and invariant under both value
representatives and changes of disc presentations. No atomicity is used. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def openPolydiscCarrier (n : ℕ) : Set ((Fin (0+n) → M) × (Fin (n+n) → M)) :=
  {p | GammaParameters.Proper p.1 ∧
    p.2 ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin n => .vf)) ∧
    ∀ i, ¬ iLe (iRv (iVFAdd (p.2 (Fin.natAdd n i)) (iVFNeg (p.2 (Fin.castAdd n i)))))
      (p.1 (Fin.natAdd 0 i))}

theorem openPolydiscCarrier_definable (S : Set M) (n : ℕ) :
    S.Definable LRV {z : Fin (0+n) ⊕ Fin (n+n) → M |
      (z ∘ Sum.inl,z ∘ Sum.inr) ∈ openPolydiscCarrier n} := by
  let Z := Fin (0+n) ⊕ Fin (n+n)
  have hΓ := Set.definable_iInter_of_finite (fun j : Fin (0+n) =>
    (GammaParameters.nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => (Sum.inl j : Z)))
  have hVF := (GammaParameters.sortedUniverse_definable S
    (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin n => .vf))).raw_definable.preimage_comp
      (Sum.inr : Fin (n+n) → Z)
  let idx (i : Fin n) : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → Z :=
    Sum.elim (Sum.elim (fun _ => .inr (Fin.castAdd n i))
      (fun _ => .inr (Fin.natAdd n i))) (fun _ => .inl (Fin.natAdd 0 i))
  have hB := Set.definable_iInter_of_finite (fun i : Fin n =>
    (rawGammaBallRelation_definable S 1).preimage_comp (idx i))
  convert hΓ.inter (hVF.inter hB) using 1
  ext z
  change (GammaParameters.Proper (z ∘ Sum.inl) ∧ _ ∧ _) ↔ _
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hΓ,hs,hcmp⟩
    refine ⟨hΓ,hs,?_⟩
    intro i
    refine ⟨hΓ (Fin.natAdd 0 i),?_,?_,fun _ => hcmp i⟩
    · intro j
      simpa only [idx,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fin.append_left,sortEval,iVF] using hs (Fin.castAdd n i)
    · intro j
      simpa only [idx,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fin.append_right,sortEval,iVF] using hs (Fin.natAdd n i)
  · rintro ⟨hΓ,hs,hB⟩
    exact ⟨hΓ,hs,fun i => (hB i).2.2.2 0⟩

theorem openPolydiscCarrier_at {n : ℕ} (t : Fin (0+n) → GammaParameters.Code (M := M))
    (a x : Fin n → VF M) :
    (GammaParameters.rawTuple t,Fin.append (vfValues a) (vfValues x)) ∈ openPolydiscCarrier n ↔
      ∀ i, (GammaParameters.value (t (Fin.natAdd 0 i))).val < vfValue (x i-a i) := by
  have hs : Fin.append (vfValues a) (vfValues x) ∈ GammaParameters.sortedUniverse
      (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin n => .vf)) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,vfValues,sortEval,iVF] using (a i).property
    · simpa only [Fin.append_right,vfValues,sortEval,iVF] using (x i).property
  change (GammaParameters.Proper (GammaParameters.rawTuple t) ∧ _ ∧ _) ↔ _
  rw [and_iff_right (GammaParameters.rawTuple_proper t),and_iff_right hs]
  apply forall_congr'
  intro i
  have hd : (x i-a i).val = iVFAdd (x i).val (iVFNeg (a i).val) := by
    rw [sub_eq_add_neg]
    rfl
  simp only [Fin.append_left,Fin.append_right,vfValues,GammaParameters.rawTuple]
  rw [← hd]
  change (¬ iLe (rv M (x i-a i)).val (t (Fin.natAdd 0 i)).val.val) ↔ _
  rw [← Values.vrv_le_iff,not_le]
  rfl

def openPolydiscGammaRelation (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (n : ℕ) : GammaParameters.Relation S (0+n) (n+n)
      (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin n => .vf)) where
  carrier := openPolydiscCarrier n
  definable := by
    rw [normalize_eq_of_isCanonical hc]
    exact openPolydiscCarrier_definable S n
  proper := fun _ h => ⟨h.1,h.2.1⟩
  invariant := by
    intro t u he y
    by_cases hs : y ∈ GammaParameters.sortedUniverse
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin n => .vf))
    · let a : Fin n → VF M := fun i => ⟨y (Fin.castAdd n i),by
        simpa only [Fin.append_left,sortEval,iVF] using hs (Fin.castAdd n i)⟩
      let x : Fin n → VF M := fun i => ⟨y (Fin.natAdd n i),by
        simpa only [Fin.append_right,sortEval,iVF] using hs (Fin.natAdd n i)⟩
      have hy : Fin.append (vfValues a) (vfValues x) = y := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp only [Fin.append_left,vfValues,a]
        · simp only [Fin.append_right,vfValues,x]
      rw [← hy,openPolydiscCarrier_at,openPolydiscCarrier_at]
      apply forall_congr'
      intro i
      have heΓ : GammaParameters.value (t (Fin.natAdd 0 i)) =
          GammaParameters.value (u (Fin.natAdd 0 i)) := congrFun he (Fin.natAdd 0 i)
      rw [heΓ]
    · exact ⟨fun h => (hs h.2.1).elim,fun h => (hs h.2.1).elim⟩

theorem openPolydiscGammaRelation_fibre (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} (a : Fin n → VF M) (δ : Fin n → Gamma M) (x : Fin n → M) :
    Fin.append (vfValues a) x ∈ (openPolydiscGammaRelation hc S n).fibre (Fin.append Fin.elim0 δ) ↔
      x ∈ namedPolydisc (fun _ => false) a δ := by
  by_cases hx : ∀ i, iVF (x i)
  · let b : Fin n → VF M := fun i => ⟨x i,hx i⟩
    change (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append Fin.elim0 δ)),
      Fin.append (vfValues a) (vfValues b)) ∈ openPolydiscCarrier n ↔ _
    rw [openPolydiscCarrier_at]
    apply forall_congr'
    intro i
    have hδ : GammaParameters.value (GammaParameters.representatives
        (Fin.append (Fin.elim0 : Fin 0 → Gamma M) δ) (Fin.natAdd 0 i)) = δ i := by
      simpa only [GammaParameters.values,Fin.append_right] using congrFun
        (GammaParameters.representatives_values (Fin.append (Fin.elim0 : Fin 0 → Gamma M) δ))
        (Fin.natAdd 0 i)
    rw [hδ]
    exact (openDiscCode_mem_iff_value (a i) (b i) (δ i)).symm
  · constructor
    · intro h
      apply (hx ?_).elim
      intro i
      have hs := (openPolydiscGammaRelation hc S n).fibre_proper _ _ h (Fin.natAdd n i)
      simpa only [Fin.append_right,sortEval,iVF] using hs
    · intro h
      exact (hx (namedPolydisc_proper (fun _ => false) a δ h)).elim

theorem named_open_polydisc_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : ParameterBase M) {n : ℕ} (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    DefinableOverFiniteDiscNames B (fun _ => false) a δ (fun _ => .vf)
      (namedPolydisc (fun _ => false) a δ) := by
  let Q := openPolydiscGammaRelation hc B.real n
  let R : FiniteDiscTupleRelation B (fun _ : Fin n => false) (fun _ : Fin n => .vf) := {
    supportArity := 0
    support := Fin.elim0
    support_mem := fun i => i.elim0
    relation := Q
    invariant := by
      intro c c' γ γ' he x
      rw [openPolydiscGammaRelation_fibre,openPolydiscGammaRelation_fibre]
      change (∀ i, x i ∈ BallImaginaries.underlying (finitePolydiscNames (fun _ => false) c γ i)) ↔
        (∀ i, x i ∈ BallImaginaries.underlying (finitePolydiscNames (fun _ => false) c' γ' i))
      rw [he] }
  exact ⟨R,Set.ext (fun x => openPolydiscGammaRelation_fibre hc B.real a δ x)⟩

end DiamondIntegral.Section2
