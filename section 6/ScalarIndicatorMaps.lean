import «section 6».ProtectedUnaryPreparation

/-! Full original-base scalar membership graphs. A continuous scalar
indicator on a clopen proper domain cuts out a proper invariant piece;
the proof uses its actual two-element range. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def scalarIndicatorMap (A C : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let F (p : Mixed M n r) : Fin 1 → VF M := fun _ => if p ∈ C.carrier then 1 else 0
  let codes (z : Fin n ⊕ Fin r → M) : Fin 1 → M :=
    fun _ => if z ∈ (rawMixedSpace n r).preimage C.carrier then (1 : VF M).val else (0 : VF M).val
  have hone : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => iVFOne) :=
    (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
      (show S.DefinableMap LRV (fun _ : Fin n ⊕ Fin r → M => Fin.elim0) from fun j => j.elim0)
  have hzero : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => iVFZero) :=
    (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp
      (show S.DefinableMap LRV (fun _ : Fin n ⊕ Fin r → M => Fin.elim0) from fun j => j.elim0)
  have hd : S.DefinableMap LRV codes := fun _ => Set.DefinableFun.ite C.definable hone hzero
  have hdom (c : (rawMixedSpace (M := M) n r).domain) : codes c.val ∈ (rawVFSpace 1).domain := by
    by_cases hc : c.val ∈ (rawMixedSpace n r).preimage C.carrier
    · exact ⟨fun _ => 1,by funext i; exact (if_pos hc).symm⟩
    · exact ⟨fun _ => 0,by funext i; exact (if_neg hc).symm⟩
  refine Map.ofCodes A F codes hd hdom ?_
  intro c
  apply vfValues_injective
  have hcode := vfValues_decode (M := M) ⟨codes c.val,hdom c⟩
  refine hcode.trans ?_
  funext i
  have hcond : c.val ∈ (rawMixedSpace n r).preimage C.carrier ↔
      (rawMixedSpace n r).decode c ∈ C.carrier :=
    ⟨fun h => h.2,fun h => ⟨c.property,h⟩⟩
  by_cases hc : (rawMixedSpace n r).decode c ∈ C.carrier
  · simp only [codes,F,if_pos hc,if_pos (hcond.mpr hc),vfValues]
  · simp only [codes,F,if_neg hc,if_neg (fun h => hc (hcond.mp h)),vfValues]

theorem scalarIndicatorMap_value (A C : DefSet (rawMixedSpace (M := M) n r) S) (p : A) :
    (scalarIndicatorMap A C p).val 0 = if p.val ∈ C.carrier then 1 else 0 := rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem clopen_indicator_level {X : Type*} [TopologicalSpace X]
    (C : Set X) (hC : IsClopen C) (g : X → VF M) (hg : ContinuousOn g C)
    (hRange : ∀ x ∈ C, g x = 0 ∨ g x = 1) : IsClopen {x | x ∈ C ∧ g x = 1} := by
  have hClosed : IsClosed {x | x ∈ C ∧ g x = 1} :=
    hg.preimage_isClosed_of_isClosed hC.isClosed isClosed_singleton
  have hEq : {x | x ∈ C ∧ g x = 1} = C ∩ g ⁻¹' ({0}ᶜ : Set (VF M)) := by
    ext x
    constructor
    · rintro ⟨hx,he⟩
      exact ⟨hx,by simpa only [Set.mem_preimage,Set.mem_compl_iff,Set.mem_singleton_iff,he] using
        (one_ne_zero : (1 : VF M) ≠ 0)⟩
    · rintro ⟨hx,hn⟩
      exact ⟨hx,(hRange x hx).resolve_left hn⟩
  exact ⟨hClosed,hEq ▸ hg.isOpen_inter_preimage hC.isOpen isClosed_singleton.isOpen_compl⟩

def scalarLevelOne {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) : DefSet (rawMixedSpace (M := M) n r) S := by
  have hone : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => iVFOne) :=
    (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
      (show S.DefinableMap LRV (fun _ : Fin n ⊕ Fin r → M => Fin.elim0) from fun j => j.elim0)
  refine ⟨{p | p ∈ A.carrier ∧ scalarCodeExtension f (mixedValues p) = (1 : VF M).val},?_⟩
  have hone' : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => (1 : VF M).val) := hone
  have hA : S.Definable LRV ((rawMixedSpace n r).preimage A.carrier) := A.definable
  change S.Definable LRV ((rawMixedSpace n r).preimage
    {p | p ∈ A.carrier ∧ scalarCodeExtension f (mixedValues p) = (1 : VF M).val})
  convert hA.inter ((scalarCodeExtension_definable f).ofPred_eq hone') using 1
  ext z
  constructor
  · rintro ⟨hz,ha,he⟩
    refine ⟨⟨hz,ha⟩,?_⟩
    change scalarCodeExtension f z = (1 : VF M).val
    simpa only [mixedValues_decode] using he
  · rintro ⟨⟨hz,ha⟩,he⟩
    change scalarCodeExtension f z = (1 : VF M).val at he
    exact ⟨hz,ha,by simpa only [mixedValues_decode] using he⟩

theorem mem_scalarLevelOne {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : Mixed M n r) :
    p ∈ (scalarLevelOne f).carrier ↔ p ∈ A.carrier ∧ totalFocusFibre f p.2 p.1 0 = 1 := by
  constructor
  · rintro ⟨hp,he⟩
    exact ⟨hp,Subtype.ext he⟩
  · rintro ⟨hp,he⟩
    exact ⟨hp,congrArg Subtype.val he⟩

theorem scalarLevelOne_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : ProperInvariant S A.carrier)
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ u, Continuous (FMT.focusFibre f u))
    (hRange : ∀ p : A, (f p).val 0 = 0 ∨ (f p).val 0 = 1) :
    ProperInvariant S (scalarLevelOne f).carrier := by
  have hSub : (scalarLevelOne f).carrier ⊆ A.carrier := fun _ hp => hp.1
  apply (lemma_6_5 h00 hc hκ hs hv _ (scalarLevelOne f).definable
    (hA.vfBounded.mono hSub) (hA.rvBounded.mono hSub)).mpr
  intro u
  have hCont : ContinuousOn (fun x => totalFocusFibre f u x 0) (vfFibre A.carrier u) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hf u using 1
    funext x
    exact congrFun (totalFocusFibre_at f u x.val x.property) 0
  have hValues (x) (hx : x ∈ vfFibre A.carrier u) :
      totalFocusFibre f u x 0 = 0 ∨ totalFocusFibre f u x 0 = 1 := by
    rw [totalFocusFibre_at f u x hx]
    exact hRange ⟨(x,u),hx⟩
  convert clopen_indicator_level (vfFibre A.carrier u) (hA.clopen_fibres hv u)
    (fun x => totalFocusFibre f u x 0) hCont hValues using 1
  ext x
  exact mem_scalarLevelOne f (x,u)

end DiamondIntegral.Section6
