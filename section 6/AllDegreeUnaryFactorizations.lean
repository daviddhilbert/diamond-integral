import «section 6».RVIsomorphismFactorizations

/-! Lemma 6.29 (`bijection:partitioned:unary`) in every degree.

In degree zero there are no structural coordinates, so relative unarity is
vacuous and every morphism is itself relatively unary. The existing chain types
`RVUnaryChain` and `MeasuredRVUnaryChain` index each step by a coordinate in
`Fin k` and therefore express only identities when `k = 0`. The factorization
types below allow a step whose relative unarity is vacuous in degree zero;
positive-degree chains embed with the same composite, and in degree zero every
morphism is a one-step factorization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.AllDegreeUnaryFactorizations
open DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- A factorization of an `RV[k]`-isomorphism into relatively unary ones
(vacuously so in degree zero). -/
inductive RVUnaryFactorization (S : Set M) (k : ℕ) : RVObject (M := M) S k → RVObject (M := M) S k → Type where
  | identity (U : RVObject (M := M) S k) : RVUnaryFactorization S k U U
  | step {U V W : RVObject (M := M) S k} (e : U ≅ V)
      (unary : k = 0 ∨ ∃ i : Fin k, RVUnaryRelativeAt e.hom.map i)
      (tail : RVUnaryFactorization S k V W) : RVUnaryFactorization S k U W

/-- The composite isomorphism. -/
def RVUnaryFactorization.iso {U V : RVObject (M := M) S k} : RVUnaryFactorization S k U V → (U ≅ V)
  | .identity U => Iso.refl U
  | .step e _ tail => e ≪≫ tail.iso

/-- Positive-degree chains are factorizations with the same composite. -/
def ofChain {U V : RVObject (M := M) S k} : RVUnaryChain S k U V → RVUnaryFactorization S k U V
  | .identity U => .identity U
  | .step i e unary tail => .step e (Or.inr ⟨i, unary⟩) (ofChain tail)

omit [M ⊨ Axioms.ACVF] in
theorem ofChain_iso {U V : RVObject (M := M) S k} (T : RVUnaryChain S k U V) : (ofChain T).iso = T.iso := by
  induction T with
  | identity U => rfl
  | step i e unary tail ih =>
    change e ≪≫ (ofChain tail).iso = e ≪≫ tail.iso
    rw [ih]

/-- A factorization of an `μRV[k]`-isomorphism into relatively unary ones. -/
inductive MeasuredRVUnaryFactorization (S : Set M) (k : ℕ) :
    MeasuredRVObject (M := M) S k → MeasuredRVObject (M := M) S k → Type where
  | identity (U : MeasuredRVObject (M := M) S k) : MeasuredRVUnaryFactorization S k U U
  | step {U V W : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V)
      (unary : k = 0 ∨ ∃ i : Fin k, RVUnaryRelativeAt e.iso.hom.map i)
      (tail : MeasuredRVUnaryFactorization S k V W) : MeasuredRVUnaryFactorization S k U W

/-- The composite measured isomorphism. -/
def MeasuredRVUnaryFactorization.iso {U V : MeasuredRVObject (M := M) S k} :
    MeasuredRVUnaryFactorization S k U V → MeasuredRVIso U V
  | .identity U => .identity U
  | .step e _ tail => e.comp tail.iso

/-- Positive-degree measured chains are factorizations with the same composite. -/
def ofMeasuredChain {U V : MeasuredRVObject (M := M) S k} :
    MeasuredRVUnaryChain S k U V → MeasuredRVUnaryFactorization S k U V
  | .identity U => .identity U
  | .step i e unary tail => .step e (Or.inr ⟨i, unary⟩) (ofMeasuredChain tail)

theorem ofMeasuredChain_iso {U V : MeasuredRVObject (M := M) S k} (T : MeasuredRVUnaryChain S k U V) :
    (ofMeasuredChain T).iso = T.iso := by
  induction T with
  | identity U => rfl
  | step i e unary tail ih =>
    change e.comp (ofMeasuredChain tail).iso = e.comp tail.iso
    rw [ih]

/-- Lemma 6.29 for `μRV[k]` in every degree `k ≥ 0`. -/
theorem lemma_6_29_measured_all_degrees (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V) :
    ∃ T : MeasuredRVUnaryFactorization S k U V, T.iso.iso.hom.map = e.iso.hom.map := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine ⟨.step e (Or.inl hk) (.identity V), ?_⟩
    apply Map.ext
    intro u
    rfl
  · obtain ⟨T, hT, _⟩ := lemma_6_29_measured hc h00 hκ hs hsmall hk e
    exact ⟨ofMeasuredChain T, (congrArg (fun E : MeasuredRVIso U V => E.iso.hom.map)
      (ofMeasuredChain_iso T)).trans hT⟩

/-- Lemma 6.29 for `RV[k]` in every degree `k ≥ 0`. -/
theorem lemma_6_29_all_degrees (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : RVObject (M := M) S k} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero) (hV : ∀ v i, (V.value v i).val ≠ iRVZero) :
    ∃ T : RVUnaryFactorization S k U V, T.iso.hom.map = e.hom.map := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine ⟨.step e (Or.inl hk) (.identity V), ?_⟩
    apply Map.ext
    intro u
    rfl
  · obtain ⟨T, hT, _, _⟩ := lemma_6_29 hc h00 hκ hs hsmall hk e hUF hVF hU hV
    exact ⟨ofChain T, (congrArg (fun E : U ≅ V => E.hom.map) (ofChain_iso T)).trans hT⟩

end DiamondIntegral.Section6.AllDegreeUnaryFactorizations
