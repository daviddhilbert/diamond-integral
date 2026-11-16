import «section 6».FiniteCenterSeparation

/-! Paired-disc choice beyond prescribed original-base named source
and target thresholds. The target radius is obtained from the actual
image of the chosen source disc; the two radii are never independent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def boundedPairedRadiusFamily (A : Set (VF M)) (f : VF M → VF M) (c d : VF M)
    (q : Fin 2 → VF M) : Set (Fin 2 → VF M) :=
  {r | r ∈ pairedRadiusFamily A f q ∧
    iLe (iRv c.val) (iRv (r 0).val) ∧ iLe (iRv d.val) (iRv (r 1).val)}

theorem boundedPairedRadiusFamily_graph_definable
    (A : Set (VF M)) (f : VF M → VF M) (hGraph : S.Definable LRV (scalarPartialGraph A f))
    (C : Set (Fin 2 → VF M)) (hC : S.Definable LRV (vfValues '' C))
    (c d : VF M) (hc : S.Definable₁ LRV {c.val}) (hd : S.Definable₁ LRV {d.val}) :
    S.Definable LRV (vfCorrespondenceGraph C (boundedPairedRadiusFamily A f c d)) := by
  let J := Fin 2 ⊕ Fin 2
  have hPair := pairedRadiusFamily_graph_definable A f hGraph C hC
  have hCConst : S.DefinableFun LRV (fun _ : J → M => c.val) := definable_named_constant c.val hc
  have hDConst : S.DefinableFun LRV (fun _ : J → M => d.val) := definable_named_constant d.val hd
  have hCBound := rvCode_compare_definable (rv_scalarCode_definable hCConst)
    (rv_scalarCode_definable (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 0 : J))))
  have hDBound := rvCode_compare_definable (rv_scalarCode_definable hDConst)
    (rv_scalarCode_definable (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 1 : J))))
  convert hPair.inter (hCBound.inter hDBound) using 1
  ext z
  constructor
  · rintro ⟨q,hq,r,⟨hr,hcR,hdR⟩,he⟩
    refine ⟨⟨q,hq,r,hr,he⟩,?_,?_⟩
    · change iLe (iRv c.val) (iRv (z (.inr 0)))
      have h : (r 0).val = z (.inr 0) := congrFun he (.inr 0)
      rw [← h]
      exact hcR
    · change iLe (iRv d.val) (iRv (z (.inr 1)))
      have h : (r 1).val = z (.inr 1) := congrFun he (.inr 1)
      rw [← h]
      exact hdR
  · rintro ⟨⟨q,hq,r,hr,he⟩,hcR,hdR⟩
    refine ⟨q,hq,r,⟨hr,?_,?_⟩,he⟩
    · change iLe (iRv c.val) (iRv (z (.inr 0))) at hcR
      have h : (r 0).val = z (.inr 0) := congrFun he (.inr 0)
      rwa [← h] at hcR
    · change iLe (iRv d.val) (iRv (z (.inr 1))) at hdR
      have h : (r 1).val = z (.inr 1) := congrFun he (.inr 1)
      rwa [← h] at hdR

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_paired_discs_beyond_named_thresholds
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A B : Set (VF M)) (hA : IsOpen A) (f : VF M → VF M) (hbij : Set.BijOn f A B)
    (hGraph : S.Definable LRV (scalarPartialGraph A f)) (hCont : ContinuousOn f A)
    (hBound : ∃ η : Gamma M, ∀ y ∈ B, η.val ≤ vfValue y)
    (C : Set (Fin 2 → VF M)) (hC : S.Definable LRV (vfValues '' C)) (hCFin : C.Finite)
    (hCenters : ∀ q ∈ C, q 0 ∈ A ∧ f (q 0) = q 1)
    (c d : VF M) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hcDef : S.Definable₁ LRV {c.val}) (hdDef : S.Definable₁ LRV {d.val}) :
    ∃ F : (Fin 2 → VF M) → Set (Fin 2 → VF M),
      S.Definable LRV (vfCorrespondenceGraph C F) ∧ (⋃ q ∈ C, F q).Finite ∧
      (∀ q, (F q).Nonempty ↔ q ∈ C) ∧
      ∀ q ∈ C, ∀ r ∈ F q, ∃ hr : r 0 ≠ 0, ∃ hs : r 1 ≠ 0,
        vfValue c ≤ vfValue (r 0) ∧ vfValue d ≤ vfValue (r 1) ∧
        centeredGammaDisc (q 0) (finiteValue (r 0) hr) ⊆ A ∧
        f '' centeredGammaDisc (q 0) (finiteValue (r 0) hr) =
          centeredGammaDisc (q 1) (finiteValue (r 1) hs) := by
  have hNonempty (q) (hq : q ∈ C) : (boundedPairedRadiusFamily A f c d q).Nonempty := by
    obtain ⟨γ,hγ⟩ := paired_centered_discs_beyond_thresholds hc hκ.le hs hsmall hv
      A B hA f hbij hGraph hCont hBound (q 0) (hCenters q hq).1 (finiteValue c hc0) (finiteValue d hd0)
    obtain ⟨hα,δ,hβ,hSource,hTarget,hImage⟩ := hγ γ le_rfl
    obtain ⟨r,hr,hR⟩ := gamma_has_vf_representative γ
    obtain ⟨s,hs₀,hS⟩ := gamma_has_vf_representative δ
    have hR' : finiteValue r hr = γ := Subtype.ext hR
    have hS' : finiteValue s hs₀ = δ := Subtype.ext hS
    refine ⟨![r,s],?_,?_,?_⟩
    · apply (pairedDiscImageCodes_at A f (q 0) (q 1) r s hr hs₀).mpr
      rw [hR',hS',← (hCenters q hq).2]
      exact ⟨(hCenters q hq).1,rfl,hSource,hImage⟩
    · change iLe (rv M c).val (rv M r).val
      rw [← Values.vrv_le_iff]
      change finiteValue c hc0 ≤ finiteValue r hr
      rw [hR']
      exact hα
    · change iLe (rv M d).val (rv M s).val
      rw [← Values.vrv_le_iff]
      change finiteValue d hd0 ≤ finiteValue s hs₀
      rw [hS']
      exact hβ
  obtain ⟨F,hF,hFin,hSub,hNe⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV hnt hsmall
    C hC (boundedPairedRadiusFamily A f c d)
    (boundedPairedRadiusFamily_graph_definable A f hGraph C hC c d hcDef hdDef) hNonempty
  refine ⟨F,hF,hCFin.biUnion (fun q _ => hFin q),hNe,fun q hq r hrF => ?_⟩
  obtain ⟨hCode,hCL,hDL⟩ := hSub q hrF
  have hSelfA : (q 0).val ∈ rawOpenBall (q 0).val (r 0).val := hCode.2.1
  have hSelfB : (q 1).val ∈ rawOpenBall (q 1).val (r 1).val := hCode.2.2.1
  have hr : r 0 ≠ 0 := fun he => hSelfA.1.2 (congrArg Subtype.val he)
  have hs₀ : r 1 ≠ 0 := fun he => hSelfB.1.2 (congrArg Subtype.val he)
  have h := (pairedDiscImageCodes_at A f (q 0) (q 1) (r 0) (r 1) hr hs₀).mp hCode
  refine ⟨hr,hs₀,?_,?_,h.2.2⟩
  · change iLe (rv M c).val (rv M (r 0)).val at hCL
    rwa [← Values.vrv_le_iff] at hCL
  · change iLe (rv M d).val (rv M (r 1)).val at hDL
    rwa [← Values.vrv_le_iff] at hDL

end DiamondIntegral.Section6
