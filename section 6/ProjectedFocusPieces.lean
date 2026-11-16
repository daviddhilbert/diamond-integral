import «section 6».ContinuousFocusFreezing

/-! Actual full-graph projected pieces for the aperture release
argument. Inserting a continuous focus into a clopen protected piece
gives a clopen original-base set on the projected ambient domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawVFSpace (M := M) 1) S}

def focusGraphPoint (f : Map C B) (p : Mixed M n r) : Mixed M (n+1) r :=
  (Fin.snoc p.1 (totalFocusFibre f p.2 p.1 0),p.2)

def focusGraphCodes (f : Map C B) (z : Fin n ⊕ Fin r → M) : Fin (n+1) ⊕ Fin r → M :=
  Sum.elim (Fin.snoc (z ∘ Sum.inl) (scalarCodeExtension f z)) (z ∘ Sum.inr)

theorem focusGraphCodes_definable (f : Map C B) : S.DefinableMap LRV (focusGraphCodes f) := by
  rintro (i | i)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [focusGraphCodes,Sum.elim_inl,Fin.snoc_last] using scalarCodeExtension_definable f
    · simpa only [focusGraphCodes,Sum.elim_inl,Fin.snoc_castSucc,Function.comp_apply] using
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl j : Fin n ⊕ Fin r)))
  · exact Set.DefinableFun.proj LRV

theorem focusGraphCodes_at (f : Map C B) (p : Mixed M n r) :
    mixedValues (focusGraphPoint f p) = focusGraphCodes f (mixedValues p) := by
  funext i
  cases i with
  | inl i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [focusGraphPoint,focusGraphCodes,mixedValues,vfValues,Sum.elim_inl,Fin.snoc_last,totalFocusFibre]
    · simp only [focusGraphPoint,focusGraphCodes,mixedValues,vfValues,Sum.elim_inl,Fin.snoc_castSucc,Function.comp_apply]
  | inr i => rfl

def focusGraphMap (f : Map C B) : Map C (DefSet.univ (rawMixedSpace (M := M) (n+1) r) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) (n+1) r
  have hcode (z : P.domain) : mixedValues (focusGraphPoint f (P.decode z)) = focusGraphCodes f z.val :=
    (focusGraphCodes_at f (P.decode z)).trans (congrArg (focusGraphCodes f) (mixedValues_decode z))
  have hdom (z : P.domain) : focusGraphCodes f z.val ∈ Q.domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  exact Map.ofCodes C (focusGraphPoint f) (focusGraphCodes f) (focusGraphCodes_definable f) hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨_,hdom z⟩).trans (hcode z).symm))

def projectedFocusPiece (f : Map C B) (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    DefSet (rawMixedSpace (M := M) n r) S :=
  ⟨{p | ∃ q : C, q.val = p ∧ (focusGraphMap f q).val ∈ A.carrier},
    Map.definable_preimage (focusGraphMap f) A.definable⟩

theorem mem_projectedFocusPiece (f : Map C B) (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (p : Mixed M n r) : p ∈ (projectedFocusPiece f A).carrier ↔
      p ∈ C.carrier ∧ focusGraphPoint f p ∈ A.carrier := by
  constructor
  · rintro ⟨q,rfl,hq⟩
    exact ⟨q.property,hq⟩
  · rintro ⟨hp,hg⟩
    exact ⟨⟨p,hp⟩,rfl,hg⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem focusGraphPoint_fibre_continuousOn
    (f : Map C B) (u : Fin r → RVInfinity M) (hf : Continuous (FMT.focusFibre f u)) :
    ContinuousOn (fun a : Fin n → VF M => (focusGraphPoint f (a,u)).1) (vfFibre C.carrier u) := by
  apply continuousOn_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [focusGraphPoint,Fin.snoc_last]
    change ContinuousOn (fun a => totalFocusFibre f u a 0) (vfFibre C.carrier u)
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hf using 1
    funext a
    exact congrFun (totalFocusFibre_at f u a.val a.property) 0
  · simpa only [focusGraphPoint,Fin.snoc_castSucc] using
      (continuous_apply j : Continuous (fun a : Fin n → VF M => a j)).continuousOn

theorem projectedFocusPiece_clopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map C B) (hC : ProperInvariant S C.carrier)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (hf : ∀ u, Continuous (FMT.focusFibre f u)) (u : Fin r → RVInfinity M) :
    IsClopen (vfFibre (projectedFocusPiece f A).carrier u) := by
  have he : vfFibre (projectedFocusPiece f A).carrier u =
      vfFibre C.carrier u ∩ (fun a => (focusGraphPoint f (a,u)).1) ⁻¹' vfFibre A.carrier u := by
    ext a
    exact mem_projectedFocusPiece f A (a,u)
  rw [he]
  have hg := focusGraphPoint_fibre_continuousOn f u (hf u)
  exact ⟨hg.preimage_isClosed_of_isClosed (hC.clopen_fibres hv u).isClosed (hA.clopen_fibres hv u).isClosed,
    hg.isOpen_inter_preimage (hC.clopen_fibres hv u).isOpen (hA.clopen_fibres hv u).isOpen⟩

theorem projectedFocusPiece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map C B) (hC : ProperInvariant S C.carrier)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (hf : ∀ u, Continuous (FMT.focusFibre f u)) :
    ProperInvariant S (projectedFocusPiece f A).carrier := by
  have hsub : (projectedFocusPiece f A).carrier ⊆ C.carrier := fun p hp =>
    ((mem_projectedFocusPiece f A p).mp hp).1
  exact (lemma_6_5 h00 hc hκ hs hv _ (projectedFocusPiece f A).definable
    (hC.vfBounded.mono hsub) (hC.rvBounded.mono hsub)).mpr
      (projectedFocusPiece_clopen hv f hC A hA hf)

end DiamondIntegral.Section6
