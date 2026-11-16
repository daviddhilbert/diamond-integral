import «section 6».Regularization
import Section4.MixedTagging
import Section4.VFRealFibres

/-! Extend an actual definable scalar map by VF zero on all other real
codes. This supplies code functions for partial focus maps without adding
parameters or assuming the extension's definability. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawVFSpace (M := M) 1) S}

def scalarCodeExtension (f : Map A B) (z : Fin n ⊕ Fin r → M) : M := by
  classical
  exact if hz : z ∈ (rawMixedSpace n r).preimage A.carrier then
    ((f ⟨(rawMixedSpace n r).decode ⟨z,hz.choose⟩,hz.choose_spec⟩).val 0).val else iVFZero

theorem scalarCodeExtension_at (f : Map A B) (p : A) :
    scalarCodeExtension f (mixedValues p.val) = ((f p).val 0).val := by
  classical
  have hz : mixedValues p.val ∈ (rawMixedSpace n r).preimage A.carrier :=
    ⟨mixedValues_mem_domain p.val,by simpa only [decode_mixedValues] using p.property⟩
  rw [scalarCodeExtension,dite_eq_left hz]
  have hp : (⟨(rawMixedSpace n r).decode ⟨mixedValues p.val,hz.choose⟩,hz.choose_spec⟩ : A) = p :=
    Subtype.ext (decode_mixedValues p.val)
  rw [hp]

theorem scalarCodeExtension_isVF (f : Map A B) (z : Fin n ⊕ Fin r → M) :
    iVF (scalarCodeExtension f z) := by
  classical
  by_cases hz : z ∈ (rawMixedSpace n r).preimage A.carrier
  · rw [scalarCodeExtension,dite_eq_left hz]
    exact ((f _).val 0).property
  · rw [scalarCodeExtension,dite_eq_right hz]
    exact (0 : VF M).property

theorem scalarCodeExtension_graph (f : Map A B) (z : Fin n ⊕ Fin r → M) (y : M) :
    Sum.elim z (fun _ : Fin 1 => y) ∈
      (rawMixedSpace n r).relation (rawVFSpace 1) f.graph ↔
      z ∈ (rawMixedSpace n r).preimage A.carrier ∧ scalarCodeExtension f z = y := by
  classical
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) 1
  constructor
  · rintro ⟨hx,hy,p,hp,hfp⟩
    have hz : z ∈ P.preimage A.carrier := ⟨hx,hp ▸ p.property⟩
    have hpcode : mixedValues p.val = z := by rw [hp]; exact mixedValues_decode _
    have hycode : vfValues (f p).val = (fun _ : Fin 1 => y) := by rw [hfp]; exact vfValues_decode _
    exact ⟨hz,by rw [← hpcode,scalarCodeExtension_at]; exact congrFun hycode 0⟩
  · rintro ⟨hz,hy⟩
    let p : A := ⟨P.decode ⟨z,hz.choose⟩,hz.choose_spec⟩
    have hpcode : mixedValues p.val = z := mixedValues_decode _
    have hval : ((f p).val 0).val = y := by
      rw [← scalarCodeExtension_at f p,hpcode]
      exact hy
    have hycode : vfValues (f p).val = (fun _ : Fin 1 => y) := by
      funext i
      fin_cases i
      exact hval
    have htarget : (fun _ : Fin 1 => y) ∈ Q.domain := ⟨(f p).val,hycode⟩
    refine ⟨hz.choose,htarget,p,rfl,?_⟩
    apply vfValues_injective
    have hdecode : vfValues (Q.decode ⟨(fun _ : Fin 1 => y),htarget⟩) = (fun _ : Fin 1 => y) :=
      vfValues_decode ⟨_,htarget⟩
    exact hycode.trans hdecode.symm

theorem scalarCodeExtension_definable (f : Map A B) :
    S.DefinableFun LRV (scalarCodeExtension f) := by
  classical
  let I := Fin n ⊕ Fin r
  let π : I ⊕ Fin 1 → Option I := Sum.elim some (fun _ => none)
  have hgraph : S.Definable LRV ((rawMixedSpace n r).relation (rawVFSpace 1) f.graph) :=
    f.graph_definable
  have hactive := hgraph.preimage_comp π
  have hsrc := A.definable.preimage_comp (some : I → Option I)
  have hzero : S.Definable LRV {w : Option I → M | iVFZero = w none} :=
    (vfZeroCode_definable S).ofPred_eq (Set.DefinableFun.proj LRV)
  have h := hactive.union (hsrc.compl.inter hzero)
  change S.Definable LRV (Function.tupleGraph (scalarCodeExtension f))
  convert h using 1
  ext w
  have hπ : w ∘ π = Sum.elim (w ∘ some) (fun _ : Fin 1 => w none) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i; rfl
  change scalarCodeExtension f (w ∘ some) = w none ↔ _
  simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_preimage,Set.mem_setOf_eq]
  rw [hπ,scalarCodeExtension_graph]
  by_cases hw : w ∘ some ∈ (rawMixedSpace n r).preimage A.carrier
  · simp only [hw,true_and,not_true_eq_false,false_and,or_false]
  · simp only [hw,false_and,not_false_eq_true,true_and,false_or]
    rw [scalarCodeExtension,dite_eq_right hw]
    rfl

theorem definable_named_constant {I : Type} (a : M)
    (ha : S.Definable₁ LRV {a}) : S.DefinableFun LRV (fun _ : I → M => a) := by
  have h := ha.preimage_comp (fun _ : Fin 1 => (none : Option I))
  change S.Definable LRV (Function.tupleGraph (fun _ : I → M => a))
  convert h using 1
  ext w
  exact eq_comm

end DiamondIntegral.Section6
