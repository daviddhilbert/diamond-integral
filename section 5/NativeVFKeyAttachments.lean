import «section 3».GammaGroundMixedProducts
import «section 5».NativeMixedCodeBridge

/-! Attaching selected VF residues as additional RV keys is an actual
original-language native bijection onto its image. VF coordinates and
every old RV parameter are retained, and finite RV fibres are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r d : ℕ}

def universalAttachSelectedVFKeys (S : Set M) (j : Fin d → Fin n) :
    Map (DefSet.univ (rawMixedSpace (M := M) n r) S) (DefSet.univ (rawMixedSpace n (d+r)) S) := by
  let f (q : Section2.Mixed M n r) : Section2.Mixed M n (d+r) :=
    (q.1,Fin.append (Section2.tupleRV M (q.1 ∘ j)) q.2)
  let F (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin (d+r) → M :=
    Sum.elim (z ∘ Sum.inl) (Fin.append (fun i => iRv (z (.inl (j i)))) (z ∘ Sum.inr))
  have hcode (c : (rawMixedSpace (M := M) n r).domain) :
      mixedValues (f ((rawMixedSpace n r).decode c)) = F c.val := by
    funext i
    cases i with
    | inl t => exact congrFun (mixedValues_decode c) (.inl t)
    | inr t =>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) t
      · simp only [f,F,mixedValues,Sum.elim_inr,rvValues,Fin.append_left,Function.comp_apply]
        change iRv (((rawMixedSpace n r).decode c).1 (j k)).val = iRv (c.val (.inl (j k)))
        exact congrArg iRv (congrFun (mixedValues_decode c) (.inl (j k)))
      · simpa only [f,F,mixedValues,Sum.elim_inr,Fin.append_right,rvValues,Function.comp_apply]
          using congrFun (mixedValues_decode c) (.inr k)
  refine Map.ofCodes _ f F ?_
    (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((rawMixedSpace n r).decode c))) ?_
  · intro i
    cases i with
    | inl t => exact Set.DefinableFun.proj LRV
    | inr t =>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) t
      · simp only [F,Sum.elim_inr,Fin.append_left]
        exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
          (show S.DefinableMap LRV (fun z : Fin n ⊕ Fin r → M => ![z (.inl (j k))]) from
            fun i => by fin_cases i; exact Set.DefinableFun.proj LRV)
      · simp only [F,Sum.elim_inr,Fin.append_right,Function.comp_apply]
        exact Set.DefinableFun.proj LRV
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hcode c).symm

def nativeAttachSelectedVFKeys (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) n (d+r))) :=
  GammaGroundMap.ofGlobal A _ (universalAttachSelectedVFKeys B.real j) (fun _ => Set.mem_univ _)

theorem nativeAttachSelectedVFKeys_value (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (a : A) :
    ((nativeAttachSelectedVFKeys A j) a).val =
      (a.val.1,Fin.append (Section2.tupleRV M (a.val.1 ∘ j)) a.val.2) := rfl

theorem nativeAttachSelectedVFKeys_injective
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n) :
    Function.Injective (nativeAttachSelectedVFKeys A j) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  have hVF : a.val.1 = b.val.1 := congrArg (fun q : Section2.Mixed M n (d+r) => q.1) h
  apply Subtype.ext
  refine Prod.ext hVF (funext (fun i => ?_))
  have hi := congrFun (congrArg Prod.snd h) (Fin.natAdd d i)
  simpa only [nativeAttachSelectedVFKeys_value,Fin.append_right] using hi

def nativeAttachSelectedVFKeysBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n) :
    GammaGroundBijection A (nativeAttachSelectedVFKeys A j).image :=
  ⟨(nativeAttachSelectedVFKeys A j).toImage,
    (nativeAttachSelectedVFKeys A j).toImage_bijective (nativeAttachSelectedVFKeys_injective A j)⟩

theorem nativeAttachSelectedVFKeys_finite
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) :
    ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ (nativeAttachSelectedVFKeys A j).image.carrier}.Finite := by
  intro x
  apply ((hf x).image (fun t => Fin.append (Section2.tupleRV M (x ∘ j)) t)).subset
  rintro t ⟨a,ha⟩
  change (a.val.1,Fin.append (Section2.tupleRV M (a.val.1 ∘ j)) a.val.2) = (x,t) at ha
  have hx : a.val.1 = x := congrArg Prod.fst ha
  refine ⟨a.val.2,?_,?_⟩
  · have ha' : (a.val.1,a.val.2) ∈ A.carrier := a.property
    exact hx ▸ ha'
  · exact (congrArg (fun z => Fin.append (Section2.tupleRV M (z ∘ j)) a.val.2) hx).symm.trans
      (congrArg Prod.snd ha)

end DiamondIntegral.Section5
