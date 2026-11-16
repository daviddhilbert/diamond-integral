import Section8.IsolationRadius
import «section 6».OriginalBaseOrdinaryMatching
import «section 6».OrdinaryLocalTranslations
import «section 6».UnaryPullbackPreservation

/-! A bijective unary RV matching between RV-pullbacks pairs zero
fibres with zero fibres. A nonzero RV disc contains distinct VF points,
whereas a zero RV fibre is a singleton with its old tags fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem exists_distinct_same_rv (a : VF M) (ha : a ≠ 0) : ∃ b : VF M,b ≠ a ∧ rv M b=rv M a := by
  obtain ⟨δ,hδ⟩ := exists_gt (finiteValue a ha)
  obtain ⟨e,he0,heValue⟩ := gamma_has_vf_representative δ
  have heValue' : vfValue e=δ.val := by simpa only [valueHom_eq_value] using heValue
  have hSmall : vfValue a < vfValue e := by rw [heValue']; exact hδ
  refine ⟨a+e,?_,(rv_eq_iff_value_close ha).mpr ?_⟩
  · intro he
    exact he0 (add_left_cancel (show a+e=a+0 by simpa only [add_zero] using he))
  · simpa only [add_sub_cancel_left] using hSmall

theorem unary_zero_rv_key_injective (p q : Mixed M 1 r)
    (hKey : rvCoordinates M p=rvCoordinates M q) (hp0 : ordinaryUnaryField p=(0 : VF M)) : p=q := by
  have hFV := congrArg Prod.fst hKey
  have hLead : rv M (ordinaryUnaryField q)=rv M (0 : VF M) :=
    (congrFun hFV 0).symm.trans (congrArg (rv M) hp0)
  have hq0 : ordinaryUnaryField q=(0 : VF M) :=
    (SpecialTransformations.Section5.rv_eq_zero_iff (ordinaryUnaryField q)).mp hLead
  apply Prod.ext
  · funext i
    fin_cases i
    exact hp0.trans hq0.symm
  · have hh := congrArg Prod.snd hKey
    exact hh

theorem rv_contractible_injection_reflects_zero
    (f : Map A B) (hf : Function.Injective f) (hA : IsRVPullback A.carrier)
    (hContractible : ∀ p q : A,rvCoordinates M p.val=rvCoordinates M q.val →
      rvCoordinates M (f p).val=rvCoordinates M (f q).val) (p : A)
    (hp0 : ordinaryUnaryField (f p).val=(0 : VF M)) : ordinaryUnaryField p.val=(0 : VF M) := by
  by_contra hp
  obtain ⟨b,hbp,hbRV⟩ := exists_distinct_same_rv (ordinaryUnaryField p.val) hp
  let qPoint : Mixed M 1 r := (fun _ => b,p.val.2)
  have hVF : tupleRV M p.val.1=tupleRV M qPoint.1 := by
    funext i
    fin_cases i
    exact hbRV.symm
  have hq : qPoint ∈ A.carrier := rvPullback_mem_of_sameRV hA p.property hVF rfl
  let q : A := ⟨qPoint,hq⟩
  have hKey : rvCoordinates M p.val=rvCoordinates M q.val := Prod.ext hVF rfl
  have hOutput : f p=f q := Subtype.ext (unary_zero_rv_key_injective (f p).val (f q).val (hContractible p q hKey) hp0)
  have hpq : p=q := hf hOutput
  have hh := congrArg (fun a : A => ordinaryUnaryField a.val) hpq
  exact hbp hh.symm

theorem OriginalBaseOrdinaryUnaryMatching.zero_iff {f : Map A B}
    (F : OriginalBaseOrdinaryUnaryMatching A B f) (p : F.source) :
    ordinaryUnaryField p.val=(0 : VF M) ↔ ordinaryUnaryField (F.map p).val=(0 : VF M) := by
  constructor
  · intro hp0
    have hInvInj : Function.Injective (F.map.inverse F.bijective) := by
      intro x y he
      have hh := congrArg F.map he
      simpa only [Map.apply_inverse] using hh
    apply rv_contractible_injection_reflects_zero (F.map.inverse F.bijective) hInvInj F.targetPullback F.reverse (F.map p)
    rw [Map.inverse_apply]
    exact hp0
  · exact rv_contractible_injection_reflects_zero F.map F.bijective.injective F.sourcePullback F.forward p

end DiamondIntegral.Section6
