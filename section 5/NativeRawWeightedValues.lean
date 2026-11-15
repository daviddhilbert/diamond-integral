import «section 5».NativeRVSetArithmetic

/-! Finite integer-valued constructible integrals on raw RV bases in the actual native
RES ring, computed by their original-ground level sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem nativeRVSetValue_of_empty (A : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (he : A.carrier = ∅) : nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A = 0 := by
  have h := nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind A
    (Fin.elim0 : Fin 0 → GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (fun i => i.elim0) (fun x => by simp only [he,Set.mem_empty_iff_false,Fin.exists_fin_zero])
  simpa only [Finset.univ_eq_empty,Finset.sum_empty] using h

def nativeRawWeightLevel (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (c : (Fin p → CanonicalRV.RVSort M) → ℤ)
    (hlevels : ∀ m, GammaGroundDefinable hc B (rawRVSpace (M := M) p) {x | x ∈ X.carrier ∧ c x = m})
    (m : ℤ) : GammaGroundDefSet hc B (rawRVSpace (M := M) p) :=
  ⟨{x | x ∈ X.carrier ∧ c x = m},hlevels m⟩

def nativeRawWeightedValue (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (c : (Fin p → CanonicalRV.RVSort M) → ℤ)
    (hfinite : (Set.range (fun x : X => c x.val)).Finite)
    (hlevels : ∀ m, GammaGroundDefinable hc B (rawRVSpace (M := M) p) {x | x ∈ X.carrier ∧ c x = m}) :
    RESDimensionFreeReduction.Ring B :=
  ∑ m : ↥hfinite.toFinset, (m.val : RESDimensionFreeReduction.Ring B) *
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (nativeRawWeightLevel X c hlevels m.val)

theorem nativeRawWeightedValue_partition
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (c : (Fin p → CanonicalRV.RVSort M) → ℤ)
    (hfinite : (Set.range (fun x : X => c x.val)).Finite)
    (hlevels : ∀ m, GammaGroundDefinable hc B (rawRVSpace (M := M) p) {x | x ∈ X.carrier ∧ c x = m})
    {ι : Type} [Fintype ι] (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (a : ι → ℤ)
    (hsub : ∀ i, (A i).carrier ⊆ X.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier)
    (ha : ∀ i (x : A i), c x.val = a i) :
    nativeRawWeightedValue h00 linear hκ hs hr hγ hΓ kind X c hfinite hlevels =
      ∑ i, (a i : RESDimensionFreeReduction.Ring B) * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
  let K := ↥hfinite.toFinset
  let L (m : K) := nativeRawWeightLevel X c hlevels m.val
  let Z (m : K) (i : ι) := (A i).inter (L m)
  have hL (m : K) : nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (L m) =
      ∑ i, nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (Z m i) := by
    apply nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
    · intro i j hij
      exact (hd i j hij).mono Set.inter_subset_left Set.inter_subset_left
    · intro x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := (hcov x).mp hx.1
        exact ⟨i,hi,hx⟩
      · rintro ⟨i,_,hx⟩
        exact hx
  have hA (i : ι) : nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) =
      ∑ m : K, nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (Z m i) := by
    apply nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
    · intro m l hml
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hml (Subtype.ext (hx.2.2.symm.trans hy.2.2))
    · intro x
      constructor
      · intro hx
        have hm : c x ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr ⟨⟨x,hsub i hx⟩,rfl⟩
        exact ⟨⟨c x,hm⟩,hx,hsub i hx,rfl⟩
      · rintro ⟨m,hx,_⟩
        exact hx
  have hweight (m : K) (i : ι) :
      (m.val : RESDimensionFreeReduction.Ring B) * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (Z m i) =
      (a i : RESDimensionFreeReduction.Ring B) * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (Z m i) := by
    by_cases he : m.val = a i
    · rw [he]
    · have hempty : (Z m i).carrier = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact he (hx.2.2.symm.trans (ha i ⟨x,hx.1⟩))
      rw [nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind (Z m i) hempty,mul_zero,mul_zero]
  change (∑ m : K, (m.val : RESDimensionFreeReduction.Ring B) * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (L m)) = _
  simp_rw [hL,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [hweight]
  rw [← Finset.mul_sum,← hA]

end DiamondIntegral.Section5
