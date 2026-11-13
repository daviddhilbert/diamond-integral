import «section 3».IntegrationDiscForward
import «section 3».IntegrationDiscWith
import «section 3».IntegrationDiscRecode
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Full interpreted-base definability agrees with native finite-disc definability on properly sorted outputs. Global Gamma-code invariance is proved before constructing the native relation. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {s k n : ℕ}

theorem integrationEmptyBase_definable_iff (S : Set M) {α : Type} [Finite α] (A : Set (α → M)) :
    FullBaseAtomicity.OverBase (⟨S,∅⟩ : FullBaseAtomicity.Base (M := M)) A ↔
      @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) α A := by
  let C : FullBaseAtomicity.Base (M := M) := ⟨S,∅⟩
  let p := @ParameterPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.empty_iff_real (p := p) (B := C) rfl

theorem integrationNormalizedRV_definable (S : Set M) {α : Type} [Finite α] (i : α) :
    @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) α S
      (fun z => @iRv M (CanonicalStructure.normalize (M := M)) (z i)) := by
  letI := CanonicalStructure.normalize (M := M)
  have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap) :=
    Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (L := LRV) Fn.rvMap)
  exact hf.comp (g := fun z : α → M => ![z i]) (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)

def integrationDiscRadiusRows (g : Fin (s+k) → M) (r : Fin k → M) : Prop :=
  ∀ i, iVF (r i) ∧ r i ≠ iVFZero ∧
    SameScalar (g (Fin.natAdd s i)) (@iRv M (CanonicalStructure.normalize (M := M)) (r i))

theorem integrationDiscRadiusRows_definable (S : Set M) :
    FullBaseAtomicity.OverBase (⟨S,∅⟩ : FullBaseAtomicity.Base (M := M))
      {z : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k → M |
        integrationDiscRadiusRows (z ∘ Sum.inl ∘ Sum.inl) (z ∘ Sum.inr)} := by
  let C : FullBaseAtomicity.Base (M := M) := ⟨S,∅⟩
  have hsame := ((definableOver_iff_normalized_raw S (fun _ : Fin 2 => .rv)
    {z | SameScalar (z 0) (z 1)}).mp (same_scalar_sorted_definable S)).1
  have hm (i : Fin k) :
      @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
        ((Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k) (Fin 2) S
        (fun z => ![z (.inl (.inl (Fin.natAdd s i))),
          @iRv M (CanonicalStructure.normalize (M := M)) (z (.inr i))]) := by
    have hr := integrationNormalizedRV_definable S (Sum.inr i : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k)
    letI := CanonicalStructure.normalize (M := M)
    intro j
    fin_cases j
    · exact Set.DefinableFun.proj LRV
    · exact hr
  have hs (i : Fin k) := FullBaseAtomicity.OverBase.preimage_map
    (FullBaseAtomicity.OverBase.of_real (B := C) hsame) (hm i)
  apply FullBaseAtomicity.OverBase.forall_finite
  intro i
  exact FullBaseAtomicity.OverBase.inter
    (integrationVFCoordinate_definable C (Sum.inr i : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k))
    (FullBaseAtomicity.OverBase.inter
      (FullBaseAtomicity.OverBase.compl (integrationZeroCoordinate_definable C
        (Sum.inr i : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k))) (hs i))

def integrationDiscInverseCarrier (closed : Fin k → Bool) (sn : Fin n → SortTag)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M)) :
    Set ((Fin (s+k) → M) × (Fin (k+n) → M)) :=
  {p | GammaParameters.Proper p.1 ∧ p.2 ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sn) ∧
    ∃ r : Fin k → M, integrationDiscRadiusRows p.1 r ∧
      integrationDiscRecode closed (Sum.elim (Sum.elim p.1 p.2) r) ∈
        ImaginaryParameters.vectorPullback
          (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))) R}

theorem integrationDiscInverseCarrier_definable (S : Set M) (closed : Fin k → Bool) (sn : Fin n → SortTag)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((Fin (s+k) × Fin 5) ⊕ Fin n)
      (ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))) R)) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin (s+k) ⊕ Fin (k+n))
      {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ integrationDiscInverseCarrier closed sn R} := by
  let C : FullBaseAtomicity.Base (M := M) := ⟨S,∅⟩
  have hr := FullBaseAtomicity.OverBase.preimage_map (FullBaseAtomicity.OverBase.of_real (B := C) hR)
    (integrationDiscRecode_definable S closed)
  have he := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter (integrationDiscRadiusRows_definable S) hr)
  have hp := FullBaseAtomicity.OverBase.preimage_comp
    (FullBaseAtomicity.OverBase.of_real (B := C) (GammaParameters.proper_normalized_definable S (n := s+k)))
    (Sum.inl : Fin (s+k) → Fin (s+k) ⊕ Fin (k+n))
  have hsort := ((definableOver_iff_normalized_raw S (Fin.append (fun _ : Fin k => .vf) sn)
    (GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sn))).mp
      (GammaParameters.sortedUniverse_definable S _)).1
  have hsp := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := C) hsort)
    (Sum.inr : Fin (k+n) → Fin (s+k) ⊕ Fin (k+n))
  apply (integrationEmptyBase_definable_iff S _).mp
  exact FullBaseAtomicity.OverBase.inter hp (FullBaseAtomicity.OverBase.inter hsp he)
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {s k n : ℕ}

theorem integrationNormalizedRV_on_vf (r : Section2.VF M) :
    @iRv M (CanonicalStructure.normalize (M := M)) r.val = @iRv M sM r.val :=
  @CanonicalStructure.normalize_fun M sM 1 Fn.rvMap ![r.val]
    (by intro i; fin_cases i; exact r.property)

theorem integrationSameScalar_codes (t u : GammaParameters.Code (M := M)) :
    SameScalar (GammaParameters.raw t) (GammaParameters.raw u) ↔ GammaParameters.value t = GammaParameters.value u := by
  constructor
  · intro h
    exact (codeValue_raw t).symm.trans (h.codeValue_eq.trans (codeValue_raw u))
  · intro h
    exact ((GammaParameters.same_codes_iff (fun _ : Fin 1 => t) (fun _ : Fin 1 => u)).mpr
      (funext (fun _ => h))) 0

theorem integrationSameScalar_radius (t : GammaParameters.Code (M := M)) (r : Section2.VF M) (hr : r ≠ 0) :
    SameScalar (GammaParameters.raw t) (@iRv M (CanonicalStructure.normalize (M := M)) r.val) ↔
      GammaParameters.value t = Section2.finiteValue r hr := by
  rw [integrationNormalizedRV_on_vf]
  let c : GammaParameters.Code (M := M) :=
    ⟨Section2.rv M r,fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he)⟩
  have hc : GammaParameters.value c = Section2.finiteValue r hr := Subtype.ext rfl
  exact (integrationSameScalar_codes t c).trans (by rw [hc])

theorem integrationAppendVF_sorted (sn : Fin n → SortTag) (a : Fin k → Section2.VF M) (b : Fin n → M) :
    Fin.append (SpecialTransformations.Section4.vfValues a) b ∈
      GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sn) ↔
    b ∈ GammaParameters.sortedUniverse sn := by
  constructor
  · intro h i
    simpa only [Fin.append_right] using h (Fin.natAdd k i)
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,SpecialTransformations.Section4.vfValues,sortEval,iVF] using (a j).property
    · simpa only [Fin.append_right] using h j

theorem integrationDiscInverseCarrier_row (closed : Fin k → Bool) (sn : Fin n → SortTag)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (t : Fin (s+k) → GammaParameters.Code (M := M)) (a : Fin k → Section2.VF M) (b : Fin n → M) :
    (GammaParameters.rawTuple t,Fin.append (SpecialTransformations.Section4.vfValues a) b) ∈
      integrationDiscInverseCarrier closed sn R ↔
    b ∈ GammaParameters.sortedUniverse sn ∧
      ∃ r : Fin k → Section2.VF M, ∃ hr : ∀ i, r i ≠ 0,
        (∀ i, GammaParameters.values t (Fin.natAdd s i) = Section2.finiteValue (r i) (hr i)) ∧
        b ∈ R (Fin.append (fun j => Sum.inr (GammaParameters.values t (Fin.castAdd k j)))
          (fun i => Sum.inl (Section2.finitePolydiscNames closed a
            (fun j => Section2.finiteValue (r j) (hr j)) i))) := by
  change (GammaParameters.Proper (GammaParameters.rawTuple t) ∧
    Fin.append (SpecialTransformations.Section4.vfValues a) b ∈
      GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sn) ∧ _) ↔ _
  rw [and_iff_right (GammaParameters.rawTuple_proper t),integrationAppendVF_sorted]
  constructor
  · rintro ⟨hs,rRaw,hRad,hR⟩
    let r : Fin k → Section2.VF M := fun i => ⟨rRaw i,(hRad i).1⟩
    have hr (i : Fin k) : r i ≠ 0 := fun he => (hRad i).2.1 (congrArg Subtype.val he)
    refine ⟨hs,r,hr,?_,?_⟩
    · intro i
      exact (integrationSameScalar_radius (t (Fin.natAdd s i)) (r i) (hr i)).mp (hRad i).2.2
    · exact (integrationDiscRecode_row closed R t a r hr b).mp hR
  · rintro ⟨hs,r,hr,hv,hR⟩
    refine ⟨hs,SpecialTransformations.Section4.vfValues r,?_,?_⟩
    · intro i
      exact ⟨(r i).property,fun he => hr i (Subtype.ext he),
        (integrationSameScalar_radius (t (Fin.natAdd s i)) (r i) (hr i)).mpr (hv i)⟩
    · exact (integrationDiscRecode_row closed R t a r hr b).mpr hR

theorem integrationDiscInverseCarrier_invariant (closed : Fin k → Bool) (sn : Fin n → SortTag)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (t u : Fin (s+k) → GammaParameters.Code (M := M)) (htu : GammaParameters.values t = GammaParameters.values u)
    (b : Fin (k+n) → M) :
    (GammaParameters.rawTuple t,b) ∈ integrationDiscInverseCarrier closed sn R ↔
      (GammaParameters.rawTuple u,b) ∈ integrationDiscInverseCarrier closed sn R := by
  by_cases hs : b ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sn)
  · let a : Fin k → Section2.VF M := fun i => ⟨b (Fin.castAdd n i),by
      simpa only [Fin.append_left,sortEval,iVF] using hs (Fin.castAdd n i)⟩
    let x := b ∘ Fin.natAdd k
    have he : Fin.append (SpecialTransformations.Section4.vfValues a) x = b := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left,SpecialTransformations.Section4.vfValues,a]
      · simp only [Fin.append_right,x,Function.comp_apply]
    rw [← he,integrationDiscInverseCarrier_row,integrationDiscInverseCarrier_row,htu]
  · constructor
    · intro h
      exact (hs h.2.1).elim
    · intro h
      exact (hs h.2.1).elim

def integrationDiscInverseRelation (S : Set M) (closed : Fin k → Bool) (sn : Fin n → SortTag)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((Fin (s+k) × Fin 5) ⊕ Fin n)
      (ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))) R)) :
    GammaParameters.Relation S (s+k) (k+n) (Fin.append (fun _ : Fin k => .vf) sn) where
  carrier := integrationDiscInverseCarrier closed sn R
  definable := integrationDiscInverseCarrier_definable S closed sn R hR
  proper p hp := ⟨hp.1,hp.2.1⟩
  invariant := integrationDiscInverseCarrier_invariant closed sn R
end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {s k n : ℕ}

theorem integrationDiscInverseRelation_row (S : Set M) (closed : Fin k → Bool) (sn : Fin n → SortTag)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((Fin (s+k) × Fin 5) ⊕ Fin n)
      (ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))) R))
    (γ : Fin s → Values.Gamma (M := M)) (a : Fin k → Section2.VF M)
    (δ : Fin k → Section2.Gamma M) (b : Fin n → M) :
    Fin.append (SpecialTransformations.Section4.vfValues a) b ∈
      (integrationDiscInverseRelation S closed sn R hR).fibre (Fin.append γ δ) ↔
    b ∈ GammaParameters.sortedUniverse sn ∧ b ∈ R (integrationDiscNamesTuple closed a δ γ) := by
  change (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append γ δ)),
    Fin.append (SpecialTransformations.Section4.vfValues a) b) ∈ integrationDiscInverseCarrier closed sn R ↔ _
  rw [integrationDiscInverseCarrier_row,GammaParameters.representatives_values]
  simp only [Fin.append_left,Fin.append_right]
  constructor
  · rintro ⟨hs,r,hr,hv,hb⟩
    have he : (fun i => Section2.finiteValue (r i) (hr i)) = δ := funext (fun i => (hv i).symm)
    refine ⟨hs,?_⟩
    change b ∈ R (Fin.append (fun j => Sum.inr (γ j))
      (fun i => Sum.inl (Section2.finitePolydiscNames closed a δ i)))
    rwa [he] at hb
  · rintro ⟨hs,hb⟩
    let r (i : Fin k) : Section2.VF M := Section2.radiusRepresentative (δ i).val
    have hr (i : Fin k) : r i ≠ 0 :=
      fun he => (δ i).property ((Section2.radiusRepresentative_zero_iff _).mp he)
    have hv : (fun i => Section2.finiteValue (r i) (hr i)) = δ := by
      funext i
      exact Subtype.ext (Section2.radiusRepresentative_value (δ i).val)
    refine ⟨hs,r,hr,?_,?_⟩
    · intro i
      exact congrFun hv.symm i
    · rw [hv]
      exact hb

def integrationDiscInverseTupleRelation (B : GammaParameters.Base (M := M))
    (closed : Fin k → Bool) (sn : Fin n → SortTag) (γ : Fin s → Values.Gamma (M := M))
    (hγ : ∀ i, γ i ∈ B.gamma)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (hR : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) ((Fin (s+k) × Fin 5) ⊕ Fin n)
      (ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))) R)) :
    Section2.FiniteDiscTupleRelation B closed sn where
  supportArity := s
  support := γ
  support_mem := hγ
  relation := integrationDiscInverseRelation B.real closed sn R hR
  invariant := by
    intro a a' δ δ' hn b
    rw [integrationDiscInverseRelation_row,integrationDiscInverseRelation_row]
    have he : integrationDiscNamesTuple closed a δ γ = integrationDiscNamesTuple closed a' δ' γ := by
      unfold integrationDiscNamesTuple
      rw [hn]
    rw [he]

theorem integrationFiniteDiscDefinable_of_full (B : GammaParameters.Base (M := M))
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hproper : ∀ b ∈ A, ∀ i, sortEval (sn i) (b i))
    (hA : FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) A) :
    Section2.DefinableOverFiniteDiscNames B closed a δ sn A := by
  obtain ⟨s,γ,hγ,R,hR,hRA⟩ := integrationDiscWith B closed a δ A hA
  refine ⟨integrationDiscInverseTupleRelation B closed sn γ hγ R hR,?_⟩
  ext b
  change Fin.append (SpecialTransformations.Section4.vfValues a) b ∈
    (integrationDiscInverseRelation B.real closed sn R hR).fibre (Fin.append γ δ) ↔ b ∈ A
  rw [integrationDiscInverseRelation_row,hRA]
  exact ⟨fun h => h.2,fun h => ⟨hproper b h,h⟩⟩

theorem integrationFiniteDiscDefinable_iff (B : GammaParameters.Base (M := M))
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hproper : ∀ b ∈ A, ∀ i, sortEval (sn i) (b i)) :
    Section2.DefinableOverFiniteDiscNames B closed a δ sn A ↔
      FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) A :=
  ⟨integrationFiniteDiscDefinable_to_full B closed a δ sn A,
    integrationFiniteDiscDefinable_of_full B closed a δ sn A hproper⟩
end DiamondIntegral.Section3
