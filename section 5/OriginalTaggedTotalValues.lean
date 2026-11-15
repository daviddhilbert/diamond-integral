import «section 5».OriginalTaggedRowPresentations
import «section 5».OriginalRVPointwiseValues

/-! Total tagged families are additive in the actual native target.
The proof retains the parameter base and removes each literal tag by
an original-base finite catalog of actual bijective row graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem originalTaggedTotal_partition
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv)) :
    let L := nativeRVTaggedDomain D (originalEmptyDomain B p b (fun _ => .rv))
    let R := nativeRVTaggedDomain (originalEmptyDomain B p a (fun _ => .rv)) E
    Disjoint (originalRVTotalFamily X L).carrier (originalRVTotalFamily X R).carrier ∧
      ∀ u, u ∈ (originalRVTotalFamily X (nativeRVTaggedDomain D E)).carrier ↔
        u ∈ (originalRVTotalFamily X L).carrier ∨ u ∈ (originalRVTotalFamily X R).carrier := by
  dsimp only
  have hrows (z : Fin p → M) (w : Fin (1+(a+b)) → M) :
      (Fin.append z w ∈ (nativeRVTaggedDomain D (originalEmptyDomain B p b (fun _ => .rv))).val ↔
        ∃ x, Fin.append z x ∈ D.val ∧ w = rawRVLeftTag b x) ∧
      (Fin.append z w ∈ (nativeRVTaggedDomain (originalEmptyDomain B p a (fun _ => .rv)) E).val ↔
        ∃ y, Fin.append z y ∈ E.val ∧ w = rawRVRightTag a y) := by
    constructor
    · rw [nativeRVTaggedDomain_row]
      simp only [originalEmptyDomain,Set.mem_empty_iff_false,false_and,exists_false,or_false]
    · rw [nativeRVTaggedDomain_row]
      simp only [originalEmptyDomain,Set.mem_empty_iff_false,false_and,exists_false,false_or]
  have hsplit (u : Fin (p+(1+(a+b))) → CanonicalRV.RVSort M) :
      Fin.append (rvValues u ∘ Fin.castAdd (1+(a+b))) (rvValues u ∘ Fin.natAdd p) = rvValues u :=
    Fin.append_castAdd_natAdd
  constructor
  · apply Set.disjoint_left.mpr
    intro u hu hv
    obtain ⟨_,hu⟩ := (originalRVTotalFamily_mem X _ u).mp hu
    obtain ⟨_,hv⟩ := (originalRVTotalFamily_mem X _ u).mp hv
    have h := hrows (rvValues u ∘ Fin.castAdd (1+(a+b))) (rvValues u ∘ Fin.natAdd p)
    rw [hsplit u] at h
    obtain ⟨x,_,hx⟩ := h.1.mp hu
    obtain ⟨y,_,hy⟩ := h.2.mp hv
    have hxy : rawRVRightTag a y = rawRVLeftTag b x := hy.symm.trans hx
    have ht := congrFun hxy (Fin.castAdd (a+b) (0 : Fin 1))
    have ht' : (iRVOne : M) = iRVZero := by
      simpa only [rawRVLeftTag,rawRVRightTag,Fin.append_left] using ht
    exact RVCalc.rv_one_ne_zero hM ht'
  · intro u
    rw [originalRVTotalFamily_mem,originalRVTotalFamily_mem,originalRVTotalFamily_mem]
    have h := hrows (rvValues u ∘ Fin.castAdd (1+(a+b))) (rvValues u ∘ Fin.natAdd p)
    have hs := nativeRVTaggedDomain_row D E
      (rvValues u ∘ Fin.castAdd (1+(a+b))) (rvValues u ∘ Fin.natAdd p)
    rw [hsplit u] at h hs
    rw [h.1,h.2,hs]
    exact and_or_left

theorem original_tagged_total_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X (nativeRVTaggedDomain D E)) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) +
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X E) := by
  let L := nativeRVTaggedDomain D (originalEmptyDomain B p b (fun _ => .rv))
  let R := nativeRVTaggedDomain (originalEmptyDomain B p a (fun _ => .rv)) E
  have hp := originalTaggedTotal_partition X D E
  let A : Fin 2 → GammaGroundDefSet hc B (rawRVSpace (M := M) (p+(1+(a+b)))) :=
    ![originalRVTotalFamily X L,originalRVTotalFamily X R]
  have hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hp.1
    · exact hp.1.symm
    · exact (hij rfl).elim
  have hcov : ∀ u, u ∈ (originalRVTotalFamily X (nativeRVTaggedDomain D E)).carrier ↔
      ∃ i, u ∈ (A i).carrier := by
    intro u
    simpa only [Fin.exists_fin_two,A,Matrix.cons_val_zero,Matrix.cons_val_one] using hp.2 u
  have hv := nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind _ A hd hcov
  have hl := original_rv_total_value_of_pointwise_bijections h00 linear hκ hs hr hγ hΓ kind X L D
    (fun x => ⟨originalRVLeftTagRowBijection D b (rvValues x.val)⟩)
  have hr' := original_rv_total_value_of_pointwise_bijections h00 linear hκ hs hr hγ hΓ kind X R E
    (fun x => ⟨originalRVRightTagRowBijection E a (rvValues x.val)⟩)
  simpa only [Fin.sum_univ_two,A,Matrix.cons_val_zero,Matrix.cons_val_one,hl,hr'] using hv

end DiamondIntegral.Section5
