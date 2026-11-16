import «section 6».IdentityStage

/-! The permitted preliminary zero-centered preparation. It translates
each zero-centered coordinate ball by a named nonzero VF point and
retains a nonzero finite branch tag for every coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

structure ZeroCenteredData (A : DefSet (rawMixedSpace (M := M) n r) S) where
  sourceProper : ProperInvariant S A.carrier
  center : VF M
  center_nonzero : center ≠ 0
  center_definable : S.Definable₁ LRV {center.val}
  invariant : ∀ u, AlphaInvariant (fun _ => finiteValue center center_nonzero) (vfFibre A.carrier u)

namespace ZeroCenteredData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def core (D : ZeroCenteredData A) (p : Mixed M n r) (i : Fin n) : Bool :=
  decide (vfValue D.center < vfValue (p.1 i))

def shift (D : ZeroCenteredData A) (b : Fin n → Bool) : Fin n → VF M :=
  fun i => if b i then D.center else 0

def tags (D : ZeroCenteredData A) (u : Fin r → RVInfinity M) (b : Fin n → Bool) :=
  Fin.append (fun i => branchTag (M := M) (b i)) u

def point (D : ZeroCenteredData A) (p : Mixed M n r) : Mixed M n (n+r) :=
  (p.1 + D.shift (D.core p),D.tags p.2 (D.core p))

theorem tags_injective (D : ZeroCenteredData A) (h00 : M ⊨ Axioms.ACVF00)
    (u : Fin r → RVInfinity M) : Function.Injective (D.tags u) := by
  intro b c he
  funext i
  apply branchTag_injective h00
  simpa only [tags,Fin.append_left] using congrFun he (Fin.castAdd r i)

theorem point_injective (D : ZeroCenteredData A) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Injective D.point := by
  intro p q he
  have hu : p.2 = q.2 := funext (fun i => by
    simpa only [point,tags,Fin.append_right] using
      congrArg (fun z : Mixed M n (n+r) => z.2 (Fin.natAdd n i)) he)
  have hb : D.core p = D.core q := D.tags_injective h00 p.2 (by
    simpa only [point,hu] using congrArg Prod.snd he)
  have hVF : p.1 = q.1 := add_right_cancel (by
    simpa only [point,hb] using congrArg Prod.fst he)
  exact Prod.ext hVF hu

def coreCode (D : ZeroCenteredData A) (z : Fin n ⊕ Fin r → M) (i : Fin n) : Prop :=
  ¬ iLe (iRv (z (.inl i))) (iRv D.center.val)

theorem coreCode_at (D : ZeroCenteredData A) (p : Mixed M n r) (i : Fin n) :
    D.coreCode (mixedValues p) i ↔ D.core p i = true := by
  change (¬ iLe (rv M (p.1 i)).val (rv M D.center).val) ↔ decide _ = true
  rw [decide_eq_true_eq,← Values.vrv_le_iff,not_le]
  rfl

def codes (D : ZeroCenteredData A) (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin (n+r) → M := by
  classical
  exact Sum.elim
    (fun i => if D.coreCode z i then iVFAdd (z (.inl i)) D.center.val else z (.inl i))
    (Fin.append (fun i => if D.coreCode z i then (branchTag (M := M) true).val
      else (branchTag (M := M) false).val) (z ∘ Sum.inr))

theorem codes_definable (D : ZeroCenteredData A) : S.DefinableMap LRV D.codes := by
  classical
  have hc : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => D.center.val) :=
    definable_named_constant _ D.center_definable
  have hcore (i : Fin n) : S.Definable LRV {z | D.coreCode z i} :=
    (rvCode_compare_definable
      (rv_scalarCode_definable (Set.DefinableFun.proj LRV)) (rv_scalarCode_definable hc)).compl
  rintro (i | i)
  · exact Set.DefinableFun.ite (hcore i)
      (scalarAddCode_definable (Set.DefinableFun.proj LRV) hc) (Set.DefinableFun.proj LRV)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [codes,Sum.elim_inr,Fin.append_left] using
        Set.DefinableFun.ite (hcore i) (branchTag_definable S true) (branchTag_definable S false)
    · simpa only [codes,Sum.elim_inr,Fin.append_right,Function.comp_apply] using
        (show S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => z (.inr i)) from Set.DefinableFun.proj LRV)

theorem codes_at (D : ZeroCenteredData A) (p : Mixed M n r) :
    D.codes (mixedValues p) = mixedValues (D.point p) := by
  classical
  funext i
  cases i with
  | inl i =>
    simp only [codes,Sum.elim_inl]
    by_cases hc : D.core p i = true
    · rw [if_pos ((D.coreCode_at p i).mpr hc)]
      simp only [point,mixedValues,Sum.elim_inl,vfValues,Pi.add_apply,shift,hc,ite_true]
      rfl
    · have hn : ¬ D.coreCode (mixedValues p) i := fun h => hc ((D.coreCode_at p i).mp h)
      rw [if_neg hn]
      have hf := Bool.eq_false_iff.mpr hc
      simp only [point,mixedValues,Sum.elim_inl,vfValues,Pi.add_apply,shift,hf,Bool.false_eq_true,ite_false,add_zero]
  | inr i =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [codes,Sum.elim_inr,Fin.append_left]
      by_cases hc : D.core p i = true
      · rw [if_pos ((D.coreCode_at p i).mpr hc)]
        simp only [point,mixedValues,Sum.elim_inr,rvValues,tags,Fin.append_left,hc]
      · have hn : ¬ D.coreCode (mixedValues p) i := fun h => hc ((D.coreCode_at p i).mp h)
        rw [if_neg hn]
        simp only [point,mixedValues,Sum.elim_inr,rvValues,tags,Fin.append_left,Bool.eq_false_iff.mpr hc]
    · simp only [codes,Sum.elim_inr,Fin.append_right,point,mixedValues,rvValues,tags,Function.comp_apply]

def map (D : ZeroCenteredData A) : Map A (DefSet.univ (rawMixedSpace (M := M) n (n+r)) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n (n+r)
  have hcode (c : P.domain) : mixedValues (D.point (P.decode c)) = D.codes c.val :=
    (D.codes_at (P.decode c)).symm.trans (congrArg D.codes (mixedValues_decode c))
  have hdom (c : P.domain) : D.codes c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A D.point D.codes D.codes_definable hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨D.codes c.val,hdom c⟩).trans (hcode c).symm

def bijection (D : ZeroCenteredData A) := D.map.toImage

theorem bijective (D : ZeroCenteredData A) (h00 : M ⊨ Axioms.ACVF00) : Function.Bijective D.bijection := by
  constructor
  · intro p q he
    exact Subtype.ext (D.point_injective h00 (congrArg Subtype.val he))
  · rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩

theorem image_carrier (D : ZeroCenteredData A) : D.map.image.carrier = D.point '' A.carrier := by
  ext q
  exact ⟨fun ⟨p,he⟩ => ⟨p.val,p.property,he⟩,fun ⟨p,hp,he⟩ => ⟨⟨p,hp⟩,he⟩⟩

end ZeroCenteredData
end DiamondIntegral.Section6
