import «section 6».AllDegreeUnaryFactorizations

/-! Lemma 6.29 (`bijection:partitioned:unary`), doubly bounded variants, in
every degree `k ≥ 0`. In positive degree these are `lemma_6_29_doublyBounded`
and `lemma_6_29_measured_doublyBounded`. In degree zero the one-step
factorization has only the two given objects as intermediate objects. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.AllDegreeUnaryFactorizations
open DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- Every intermediate object has finite volume fibres. -/
def RVUnaryFactorization.finiteVolume {U V : RVObject (M := M) S k} :
    RVUnaryFactorization S k U V → Prop
  | .identity U => U.volume.FiniteFibres
  | .step (U := U) _ _ tail => U.volume.FiniteFibres ∧ tail.finiteVolume

/-- Every intermediate object is doubly bounded. -/
def RVUnaryFactorization.doublyBounded {U V : RVObject (M := M) S k} :
    RVUnaryFactorization S k U V → Prop
  | .identity U => RVObjectDoublyBounded U
  | .step (U := U) _ _ tail => RVObjectDoublyBounded U ∧ tail.doublyBounded

/-- Every intermediate measured object is doubly bounded. -/
def MeasuredRVUnaryFactorization.doublyBounded {U V : MeasuredRVObject (M := M) S k} :
    MeasuredRVUnaryFactorization S k U V → Prop
  | .identity U => U.doublyBounded
  | .step (U := U) _ _ tail => U.doublyBounded ∧ tail.doublyBounded

theorem ofChain_finiteVolume {U V : RVObject (M := M) S k} (T : RVUnaryChain S k U V)
    (h : T.finiteVolume) : (ofChain T).finiteVolume := by
  induction T with
  | identity U => exact h
  | step i e unary tail ih => exact ⟨h.1, ih h.2⟩

theorem ofChain_doublyBounded {U V : RVObject (M := M) S k} (T : RVUnaryChain S k U V)
    (h : T.doublyBounded) : (ofChain T).doublyBounded := by
  induction T with
  | identity U => exact h
  | step i e unary tail ih => exact ⟨h.1, ih h.2⟩

theorem ofMeasuredChain_doublyBounded {U V : MeasuredRVObject (M := M) S k}
    (T : MeasuredRVUnaryChain S k U V) (h : T.doublyBounded) : (ofMeasuredChain T).doublyBounded := by
  induction T with
  | identity U => exact h
  | step i e unary tail ih => exact ⟨h.1, ih h.2⟩

/-- Lemma 6.29 for `μRV^db[k]` in every degree `k ≥ 0`. -/
theorem lemma_6_29_measured_doublyBounded_all_degrees (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ T : MeasuredRVUnaryFactorization S k U V,
      T.iso.iso.hom.map = e.iso.hom.map ∧ T.doublyBounded := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine ⟨.step e (Or.inl hk) (.identity V), ?_, hU, hV⟩
    apply Map.ext
    intro u
    rfl
  · obtain ⟨T, hT, hTB⟩ := lemma_6_29_measured_doublyBounded hc h00 hκ hs hsmall hk e hU hV
    exact ⟨ofMeasuredChain T, (congrArg (fun E : MeasuredRVIso U V => E.iso.hom.map)
      (ofMeasuredChain_iso T)).trans hT, ofMeasuredChain_doublyBounded T hTB⟩

/-- Lemma 6.29 for `RV^db[k]` in every degree `k ≥ 0`. -/
theorem lemma_6_29_doublyBounded_all_degrees (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : RVObject (M := M) S k} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero) (hV : ∀ v i, (V.value v i).val ≠ iRVZero)
    (hUB : RVObjectDoublyBounded U) (hVB : RVObjectDoublyBounded V) :
    ∃ T : RVUnaryFactorization S k U V,
      T.iso.hom.map = e.hom.map ∧ T.finiteVolume ∧ T.doublyBounded := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine ⟨.step e (Or.inl hk) (.identity V), ?_, ⟨hUF, hVF⟩, ⟨hUB, hVB⟩⟩
    apply Map.ext
    intro u
    rfl
  · obtain ⟨T, hT, hTF, hTB⟩ := lemma_6_29_doublyBounded hc h00 hκ hs hsmall hk e hUF hVF hU hV hUB hVB
    exact ⟨ofChain T, (congrArg (fun E : U ≅ V => E.hom.map) (ofChain_iso T)).trans hT,
      ofChain_finiteVolume T hTF, ofChain_doublyBounded T hTB⟩

/-- Lemma 6.29 for `RV[k]` in every degree `k ≥ 0`, keeping finite volume
fibres along the factorization (every intermediate object is in `RV[k]`). -/
theorem lemma_6_29_finiteVolume_all_degrees (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : RVObject (M := M) S k} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero) (hV : ∀ v i, (V.value v i).val ≠ iRVZero) :
    ∃ T : RVUnaryFactorization S k U V, T.iso.hom.map = e.hom.map ∧ T.finiteVolume := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine ⟨.step e (Or.inl hk) (.identity V), ?_, ⟨hUF, hVF⟩⟩
    apply Map.ext
    intro u
    rfl
  · obtain ⟨T, hT, hTF, _⟩ := lemma_6_29 hc h00 hκ hs hsmall hk e hUF hVF hU hV
    exact ⟨ofChain T, (congrArg (fun E : U ≅ V => E.hom.map) (ofChain_iso T)).trans hT,
      ofChain_finiteVolume T hTF⟩

end DiamondIntegral.Section6.AllDegreeUnaryFactorizations
