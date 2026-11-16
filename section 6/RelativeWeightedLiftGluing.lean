import «section 6».RelativeWeightedLiftDomains

/-! Global original-base gluing of relative weighted polynomial fibre
lifts. The selected graph on every RV pair has the exact inactive VF
diagonal and the weighted Jacobian block identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
namespace DiamondIntegral.Section6
variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n : ℕ}
local notation "VF" => VFType (M := M)
variable (w : Valuation (VFType (M := M)) Γ)
variable (hw : ∀ x y : VFType (M := M),VFValued.predV x y ↔ w x ≤ w y)

theorem exists_relative_lift_with_weighted_blocks
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B)
    (active : Fin n) (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (hFixed : ∀ z ∈ C,∀ j,j ≠ active → z (productRight n n j) = z (productLeft n n j))
    (h0 : ∀ z ∈ C, ∀ i, z i ≠ iRVZero)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    let E := vfDefinableClosureFieldBase B
    ∃ F : Set (Fin (n + n) → M), B.real.Definable LRV F ∧ C ⊆ rawLiftDomain F ∧
      ∀ t s : Fin n → _root_.RVCalc.RV w,
        productTuple (rawRV w hw t) (rawRV w hw s) ∈ C →
        ∃ H : Fin n → MvPolynomial (Fin (n + n)) E,
          ∀ a ∈ RVFibre w t, ∀ b ∈ RVFibre w s,
            let Z := fun i => (H i).map E.subtype
            let z := productTuple a b
            let A := (partialJacobianPolynomial (productLeft n n) Z).eval z * ∏ i, a i
            let D := (partialJacobianPolynomial (productRight n n) Z).eval z * ∏ i, b i
            (productTuple (rawVF a) (rawVF b) ∈ F ↔
              (∀ i,(Z i).eval z = 0) ∧ ∀ j,j ≠ active → b j = a j) ∧
            (productTuple (rawVF a) (rawVF b) ∈ F → D ≠ 0 ∧ w A = w D) := by
  classical
  let E := vfDefinableClosureFieldBase B
  have hE (c : E) : c.val.val ∈ B.real := (mem_generatedBase_vfField B hB c.val).mp c.property
  let Good (z : Fin (n + n) → M) (A : Set (Fin (n + n) → M)) : Prop :=
    ∃ H : Fin n → MvPolynomial (Fin (n + n)) E, A = relativePolynomialGraph H active ∧ z ∈ relativeWeightedLiftDomain H active
  have hloc (z : Fin (n + n) → M) (hz : z ∈ C) :
      ∃ A D : Set (Fin (n + n) → M), B.real.Definable LRV A ∧ B.real.Definable LRV D ∧
        z ∈ D ∧ D ⊆ rawLiftDomain A ∧ ∀ q ∈ D, Good q A := by
    let t (i : Fin n) : _root_.RVCalc.RV w := (CanonicalRV.equiv w hw).symm
      ⟨z (productLeft n n i), by simpa only [sortEval, iRV] using hC.proper z hz (productLeft n n i)⟩
    let s (i : Fin n) : _root_.RVCalc.RV w := (CanonicalRV.equiv w hw).symm
      ⟨z (productRight n n i), by simpa only [sortEval, iRV] using hC.proper z hz (productRight n n i)⟩
    have ht (i : Fin n) : rawRV w hw t i = z (productLeft n n i) := by simp [rawRV, t]
    have hs (i : Fin n) : rawRV w hw s i = z (productRight n n i) := by simp [rawRV, s]
    have he : productTuple (rawRV w hw t) (rawRV w hw s) = z := by
      apply productTuple_ext
      · intro i; simpa only [productTuple_left] using ht i
      · intro i; simpa only [productTuple_right] using hs i
    have hnone : (CanonicalRV.equiv w hw (none : _root_.RVCalc.RV w)).val = iRVZero := by
      rw [← _root_.RVCalc.rv_zero, CanonicalRV.equiv_rv]
      exact RVCalc.rv_zero_eq ‹M ⊨ Axioms.ACVF›
    have ht₀ (i : Fin n) : t i ≠ none := by
      intro h
      have hh := ht i
      rw [rawRV, h, hnone] at hh
      exact h0 z hz _ hh.symm
    have hs₀ (i : Fin n) : s i ≠ none := by
      intro h
      have hh := hs i
      rw [rawRV, h, hnone] at hh
      exact h0 z hz _ hh.symm
    have hFixedRV (j : Fin n) (hj : j ≠ active) : t j = s j := by
      apply (CanonicalRV.equiv w hw).injective
      apply Subtype.ext
      change rawRV w hw t j = rawRV w hw s j
      have h := hFixed z hz j hj
      rw [← ht j,← hs j] at h
      exact h.symm
    obtain ⟨H,α,hHG,hJL,hJR,hLift,hKeep⟩ :=
      exists_relative_correspondence_weighted_local_polynomials hκ hsat h00 B hsmall hB
        w hw C hC t s ht₀ hs₀ active hFixedRV (he.symm ▸ hz) (hright _) (hleft _)
    refine ⟨relativePolynomialGraph H active,relativeWeightedLiftDomain H active,
      relativePolynomialGraph_definable hE H active,relativeWeightedLiftDomain_definable hE H active,
      ?_,fun _ h => h.1,fun q hq => ⟨H,rfl,hq⟩⟩
    exact he ▸ mem_relativeWeightedLiftDomain_of_blocks w hw active t s ht₀ hs₀ H α
      ⟨hHG,hJL,hJR,hLift⟩ hKeep
  obtain ⟨k, c, hc⟩ := hC.specialize
  obtain ⟨F, hF, hlift, hGood⟩ := exists_gluedLift_on_good_domains hsat
    B.real (B.real ∪ Set.range (rawTuple c)) Set.subset_union_left
    (small_union_range hκ B.real hsmall (rawTuple c)) C hc.raw_definable
    (fun z hz i => by simpa only [sortEval, iRV] using hC.proper z hz i) Good hloc
  refine ⟨F, hF, hlift, fun t s hz => ?_⟩
  obtain ⟨_, ⟨H, rfl, hD⟩, hGraph⟩ := hGood _ hz
  refine ⟨H, fun a ha b hb => ?_⟩
  have ha' : rawVF a ∈ rawTupleFibre ((productTuple (rawRV w hw t) (rawRV w hw s)) ∘
      productLeft n n) := by
    simpa only [Function.comp_def, productTuple_left] using (rawVF_mem_rawTupleFibre_iff w hw t a).mpr ha
  have hb' : rawVF b ∈ rawTupleFibre ((productTuple (rawRV w hw t) (rawRV w hw s)) ∘
      productRight n n) := by
    simpa only [Function.comp_def, productTuple_right] using (rawVF_mem_rawTupleFibre_iff w hw s b).mpr hb
  have he := hGraph _ ha' _ hb'
  refine ⟨he.trans (relativePolynomialGraph_iff H active a b),fun hf => ?_⟩
  exact relativeWeightedLiftDomain_blocks w hw H active t s hD a ha b hb (he.mp hf)

end DiamondIntegral.Section6
