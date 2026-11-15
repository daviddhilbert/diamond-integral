import «section 5».NativeMixedMapFibres
import «section 5».NativeSortedGroundTransfer
import Section3.GammaClosureLaws

/-! Evaluating an actual native map adds only definable parameters.+Bijective chart changes therefore give equivalent exact raw bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {n r p q : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}

theorem nativeMixedMap_value_singleton (f : GammaGroundMap A C) (a : A) :
    DefinableOverBase ⟨B.real ∪ Set.range (nativeMixedCode a.val),B.gamma⟩
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
      {nativeMixedCode (f a).val} := by
  have hd := gamma_tuple_parameter_specialize _ _ (nativeMixedCode a.val) (nativeMixedMapGraph_definable f)
  convert hd using 1 <;> try rfl
  ext w
  constructor
  · rintro rfl
    exact ⟨a,rfl⟩
  · rintro ⟨b,hb⟩
    have hab : a = b := by
      apply Subtype.ext
      apply nativeMixedCode_injective
      exact funext (fun i => by
        have he := congrFun hb (Fin.castAdd (p+q) i)
        simpa only [Fin.append_left] using he)
    subst b
    apply funext
    intro i
    have he := congrFun hb (Fin.natAdd (n+r) i)
    simpa only [Fin.append_right] using he

theorem nativeMixedMap_value_coordinate (f : GammaGroundMap A C) (a : A) (i : Fin (p+q)) :
    DefinableClosureAtBase ⟨B.real ∪ Set.range (nativeMixedCode a.val),B.gamma⟩
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv) i)
      (nativeMixedCode (f a).val i) := by
  change DefinableOverBase ⟨B.real ∪ Set.range (nativeMixedCode a.val),B.gamma⟩
    (fun _ : Fin 1 => Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv) i)
    {w | w 0 = nativeMixedCode (f a).val i}
  have hd := (nativeMixedMap_value_singleton f a).image_real (fun _ : Fin 1 => i)
  convert hd using 1 <;> try rfl
  ext w
  change w 0 = nativeMixedCode (f a).val i ↔
    ∃ x ∈ ({nativeMixedCode (f a).val} : Set (Fin (p+q) → M)), x ∘ (fun _ : Fin 1 => i) = w
  constructor
  · intro hw
    refine ⟨_,rfl,?_⟩
    funext j
    exact (Fin.eq_zero j) ▸ hw.symm
  · rintro ⟨x,rfl,hx⟩
    exact (congrFun hx 0).symm

theorem nativeMixedMap_parameter_transfer (f : GammaGroundMap A C) (a : A)
    {d : ℕ} (sn : Fin d → SortTag) (D : Set (Fin d → M))
    (hD : DefinableOverBase ⟨B.real ∪ Set.range (nativeMixedCode (f a).val),B.gamma⟩ sn D) :
    DefinableOverBase ⟨B.real ∪ Set.range (nativeMixedCode a.val),B.gamma⟩ sn D := by
  apply hD.eliminate_definable_params
  · rintro x (hx | ⟨i,rfl⟩)
    · exact (subset_closureBase ⟨B.real ∪ Set.range (nativeMixedCode a.val),B.gamma⟩).1 (Or.inl hx)
    · exact ⟨_,nativeMixedMap_value_coordinate f a i⟩
  · exact (subset_closureBase ⟨B.real ∪ Set.range (nativeMixedCode a.val),B.gamma⟩).2

end DiamondIntegral.Section5
