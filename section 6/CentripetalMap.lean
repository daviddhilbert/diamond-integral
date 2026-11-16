import «section 6».CentripetalData

/-! The actual definable finite-aperture bijection. Both lifted clauses
are assembled over the original base, with nonzero finite branch tags.
The focus code is proved definable by extension from its actual domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def focusCode (D : CentripetalData (G := G) A) := scalarCodeExtension D.focusMap

def productCode (D : CentripetalData (G := G) A) (z : Fin n ⊕ Fin r → M) : M :=
  iVFMul D.coefficient.val (D.focusCode z)

def differenceCode (D : CentripetalData (G := G) A) (z : Fin n ⊕ Fin r → M) : M :=
  iVFAdd (z (.inl D.coordinate)) (iVFNeg (D.focusCode z))

def coreCode (D : CentripetalData (G := G) A) (z : Fin n ⊕ Fin r → M) : Prop :=
  ¬ iLe (iRv (D.differenceCode z)) (iRv (D.productCode z))

theorem coreCode_at (D : CentripetalData (G := G) A) (p : Mixed M n r) :
    D.coreCode (mixedValues p) ↔ D.core p = true := by
  change (¬ iLe (rv M (p.1 D.coordinate - D.extendedFocus p)).val
    (rv M (D.coefficient * D.extendedFocus p)).val) ↔ decide _ = true
  rw [decide_eq_true_eq,← Values.vrv_le_iff,not_le]
  rfl

def codes (D : CentripetalData (G := G) A) (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin (1+r) → M := by
  classical
  exact Sum.elim
    (fun i => if i = D.coordinate then
      if D.coreCode z then iVFAdd (D.differenceCode z) (D.productCode z) else D.differenceCode z
      else z (.inl i))
    (Fin.append (fun _ : Fin 1 => if D.coreCode z then (branchTag (M := M) true).val
      else (branchTag (M := M) false).val) (z ∘ Sum.inr))

theorem codes_definable (D : CentripetalData (G := G) A) : S.DefinableMap LRV D.codes := by
  classical
  have hFocus : S.DefinableFun LRV D.focusCode := scalarCodeExtension_definable D.focusMap
  have hCoeff : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => D.coefficient.val) :=
    definable_named_constant D.coefficient.val D.coefficient_definable
  have hProduct : S.DefinableFun LRV D.productCode := scalarMulCode_definable hCoeff hFocus
  have hDiff : S.DefinableFun LRV D.differenceCode :=
    scalarSubCode_definable (Set.DefinableFun.proj LRV) hFocus
  have hCore : S.Definable LRV {z | D.coreCode z} :=
    (rvCode_compare_definable (rv_scalarCode_definable hDiff) (rv_scalarCode_definable hProduct)).compl
  have hSum := scalarAddCode_definable hDiff hProduct
  have hOut := Set.DefinableFun.ite hCore hSum hDiff
  have hTag := Set.DefinableFun.ite hCore
    (branchTag_definable S true) (branchTag_definable S false)
  rintro (i | i)
  · by_cases hi : i = D.coordinate
    · simpa only [codes,Sum.elim_inl,hi,ite_true] using hOut
    · simpa only [codes,Sum.elim_inl,hi,ite_false] using
        (show S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => z (.inl i)) from Set.DefinableFun.proj LRV)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [codes,Sum.elim_inr,Fin.append_left] using hTag
    · simpa only [codes,Sum.elim_inr,Fin.append_right,Function.comp_apply] using
        (show S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => z (.inr i)) from Set.DefinableFun.proj LRV)

theorem codes_at (D : CentripetalData (G := G) A) (p : Mixed M n r) :
    D.codes (mixedValues p) = mixedValues (D.point p) := by
  classical
  have hCore := D.coreCode_at p
  funext i
  cases i with
  | inl i =>
    by_cases hi : i = D.coordinate
    · subst i
      by_cases hc : D.core p = true
      · have hcc := hCore.mpr hc
        simp only [codes,Sum.elim_inl,ite_true]
        rw [if_pos hcc]
        simp only [point,mixedValues,Sum.elim_inl,vfValues,Function.update_self,hc,ite_true,
          focusCode,differenceCode,productCode,extendedFocus,add_zero]
        rfl
      · have hcc : ¬ D.coreCode (mixedValues p) := fun h => hc (hCore.mp h)
        simp only [codes,Sum.elim_inl,ite_true]
        rw [if_neg hcc]
        simp only [point,mixedValues,Sum.elim_inl,vfValues,Function.update_self,hc,Bool.false_eq_true,ite_false,
          focusCode,differenceCode,productCode,extendedFocus,add_zero]
        rfl
    · simp only [codes,Sum.elim_inl,hi,ite_false,point,mixedValues,vfValues,Function.update_of_ne hi]
  | inr i =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · by_cases hc : D.core p = true
      · have hcc := hCore.mpr hc
        simp only [codes,Sum.elim_inr,Fin.append_left]
        rw [if_pos hcc]
        simp only [point,mixedValues,Sum.elim_inr,rvValues,Fin.append_left,hc]
      · have hcc : ¬ D.coreCode (mixedValues p) := fun h => hc (hCore.mp h)
        have hfalse : D.core p = false := Bool.eq_false_iff.mpr hc
        simp only [codes,Sum.elim_inr,Fin.append_left]
        rw [if_neg hcc]
        simp only [point,mixedValues,Sum.elim_inr,rvValues,Fin.append_left,hfalse]
    · simp only [codes,Sum.elim_inr,Fin.append_right,point,mixedValues,rvValues,Function.comp_apply]

def map (D : CentripetalData (G := G) A) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (1+r)) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n (1+r)
  have hcode (c : P.domain) : mixedValues (D.point (P.decode c)) = D.codes c.val :=
    (D.codes_at (P.decode c)).symm.trans (congrArg D.codes (mixedValues_decode c))
  have hdom (c : P.domain) : D.codes c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A D.point D.codes D.codes_definable hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨D.codes c.val,hdom c⟩).trans (hcode c).symm

def bijection (D : CentripetalData (G := G) A) := D.map.toImage

theorem bijection_apply (D : CentripetalData (G := G) A) (p : A) : (D.bijection p).val = D.point p.val := rfl

theorem image_carrier (D : CentripetalData (G := G) A) : D.map.image.carrier = D.point '' A.carrier := by
  ext q
  exact ⟨fun ⟨p,he⟩ => ⟨p.val,p.property,he⟩,fun ⟨p,hp,he⟩ => ⟨⟨p,hp⟩,he⟩⟩

theorem bijective (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective D.bijection := by
  constructor
  · intro p q he
    exact Subtype.ext (D.point_injective_on h00 p.property q.property (congrArg Subtype.val he))
  · rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩

end DiamondIntegral.Section6.CentripetalData
