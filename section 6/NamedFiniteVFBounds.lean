import «section 6».FinitePairedDiscFamilies

/-! A named nonzero VF point strictly beyond every value in a finite
original-base definable nonzero family. Only the complete family is
named; the unordered-product positive-choice construction removes its
individual algebraic choices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def aboveFiniteVFValues (E : Set (VF M)) : Set (VF M) :=
  {c | c ≠ 0 ∧ (1 : GammaInfinity M) < vfValue c ∧ ∀ a ∈ E, vfValue a < vfValue c}

theorem aboveFiniteVFValues_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (E : Set (VF M)) (hE : S.Definable₁ LRV (Subtype.val '' E)) :
    S.Definable₁ LRV (Subtype.val '' aboveFiniteVFValues E) := by
  let J := Fin 1 ⊕ Fin 1
  have hBase := puncturedRadiusBall_definable (M := M) (S := S) (1 : Gamma M) (gamma_one_named hc)
  have hVals := hE.preimage_comp (Sum.inr : Fin 1 → J)
  have hCompare := rvCode_compare_definable
    (rv_scalarCode_definable (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inl 0 : J))))
    (rv_scalarCode_definable (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr 0 : J))))
  have hBad := (hVals.inter hCompare).exists_of_finite
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' aboveFiniteVFValues E}
  convert hBase.inter hBad.compl using 1
  ext z
  constructor
  · rintro ⟨c,hcP,hcz⟩
    refine ⟨⟨fun _ => c,⟨hcP.1,hcP.2.1⟩,by funext i; fin_cases i; exact hcz⟩,?_⟩
    rintro ⟨a,⟨x,hx,hxa⟩,hCmp⟩
    change x.val = a 0 at hxa
    change iLe (iRv (z 0)) (iRv (a 0)) at hCmp
    rw [← hcz,← hxa] at hCmp
    change iLe (rv M c).val (rv M x).val at hCmp
    rw [← Values.vrv_le_iff] at hCmp
    exact (not_le_of_gt (hcP.2.2 x hx)) hCmp
  · rintro ⟨⟨c,hcP,hcz⟩,hNo⟩
    have hc0 : c 0 ≠ 0 := hcP.1
    have hcpos : (1 : GammaInfinity M) < vfValue (c 0) := hcP.2
    refine ⟨c 0,⟨hc0,hcpos,?_⟩,congrFun hcz 0⟩
    intro a ha
    by_contra hn
    have hle : vfValue (c 0) ≤ vfValue a := le_of_not_gt hn
    apply hNo
    refine ⟨fun _ => a.val,⟨a,ha,rfl⟩,?_⟩
    change iLe (iRv (z 0)) (iRv a.val)
    rw [← congrFun hcz 0]
    change iLe (rv M (c 0)).val (rv M a).val
    rw [← Values.vrv_le_iff]
    exact hle

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_named_vf_above_finite_family
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (E : Set (VF M)) (hE : S.Definable₁ LRV (Subtype.val '' E)) (hFin : E.Finite)
    (hNZ : ∀ a ∈ E, a ≠ 0) :
    ∃ c : VF M, c ≠ 0 ∧ S.Definable₁ LRV {c.val} ∧
      (1 : GammaInfinity M) < vfValue c ∧ ∀ a ∈ E, vfValue a < vfValue c := by
  let values (a : VF M) : Gamma M := if ha : a ≠ 0 then finiteValue a ha else 1
  obtain ⟨γ,hγ⟩ := (hFin.image values).bddAbove
  obtain ⟨δ,hδ⟩ := exists_gt (max γ (1 : Gamma M))
  obtain ⟨b,hb,hbδ⟩ := gamma_has_vf_representative δ
  have hbδ' : vfValue b = δ.val := by simpa only [valueHom_eq_value] using hbδ
  have hNonempty : (aboveFiniteVFValues E).Nonempty := by
    refine ⟨b,hb,?_,fun a ha => ?_⟩
    · rw [hbδ']
      exact (le_max_right _ _).trans_lt hδ
    · have haγ : finiteValue a (hNZ a ha) ≤ γ := by
        have h := hγ (Set.mem_image_of_mem values ha)
        simpa only [values,dif_pos (hNZ a ha)] using h
      rw [hbδ']
      exact haγ.trans_lt ((le_max_left _ _).trans_lt hδ)
  obtain ⟨c,hcP,hcDef⟩ := exists_named_positive_choice Valued.v hv hc h00 V S hV hVS hSV hnt
    (aboveFiniteVFValues E) (aboveFiniteVFValues_definable hc E hE) hNonempty
    (fun a ha => ⟨ha.1,ha.2.1.le⟩)
    (fun a ha b hb hab => ⟨hb,ha.2.1.trans_le hab,fun x hx => (ha.2.2 x hx).trans_le hab⟩)
  exact ⟨c,hcP.1,hcDef,hcP.2⟩

end DiamondIntegral.Section6
