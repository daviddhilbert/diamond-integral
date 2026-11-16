import «section 6».RVGeometryParameterLoci

/-! A current mixed source has constant VF leading terms on each old
RV-label fibre exactly on a definable parameter locus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

def taggedSourceCodeCondition (ι : Type) (n r : ℕ) :
    Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r)) → M) :=
  {z | (∀ j : Fin r,z (.inr (.inl (.inr j)))=z (.inr (.inr (.inr j)))) →
    ∀ i : Fin n,iRv (z (.inr (.inl (.inl i))))=iRv (z (.inr (.inr (.inl i))))}

theorem taggedSourceCodeCondition_definable :
    S.Definable LRV (taggedSourceCodeCondition (M := M) ι n r) := by
  let Z := ι ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin r))
  have hRV (j : Fin r) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inr j)))=z (.inr (.inr (.inr j)))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hVF (i : Fin n) : S.Definable LRV {z : Z → M |
      iRv (z (.inr (.inl (.inl i))))=iRv (z (.inr (.inr (.inl i))))} :=
    (rv_scalarCode_definable (Set.DefinableFun.proj LRV)).ofPred_eq
      (rv_scalarCode_definable (Set.DefinableFun.proj LRV))
  convert (Set.definable_iInter_of_finite hRV).compl.union (Set.definable_iInter_of_finite hVF) using 1
  ext z
  simp only [taggedSourceCodeCondition,Set.mem_union,Set.mem_compl_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change (_ → _) ↔ ¬ _ ∨ _
  exact imp_iff_not_or

def taggedSourceParameterLocus (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) : Set (ι → M) :=
  binaryGraphConditionLocus R (taggedSourceCodeCondition ι n r)

theorem taggedSourceParameterLocus_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (taggedSourceParameterLocus R) :=
  binaryGraphConditionLocus_definable _ _ hR taggedSourceCodeCondition_definable

theorem mem_taggedSourceParameterLocus_iff
    (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (a : ι → M)
    (A : DefSet (rawMixedSpace (M := M) n r) T)
    (hSource : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).preimage A.carrier) :
    a ∈ taggedSourceParameterLocus R ↔
      ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  let P := rawMixedSpace (M := M) n r
  have hAt (p : Mixed M n r) : Sum.elim a (mixedValues p) ∈ R ↔ p ∈ A.carrier := by
    have h := P.preimage_decode A.carrier ⟨mixedValues p,mixedValues_mem_domain _⟩
    rw [decode_mixedValues] at h
    exact (Set.ext_iff.mp hSource _).trans h
  constructor
  · intro h p hp q hq hu
    have hCode := h (mixedValues p) (mixedValues q) ((hAt p).mpr hp) ((hAt q).mpr hq)
      (fun j => congrArg (fun u => (u j).val) hu)
    exact funext (fun i => Subtype.ext (hCode i))
  · intro h x y hx hy hTags
    obtain ⟨hxDom,hxA⟩ := (Set.ext_iff.mp hSource x).mp hx
    obtain ⟨hyDom,hyA⟩ := (Set.ext_iff.mp hSource y).mp hy
    let p := P.decode ⟨x,hxDom⟩
    let q := P.decode ⟨y,hyDom⟩
    have hP : mixedValues p=x := mixedValues_decode _
    have hQ : mixedValues q=y := mixedValues_decode _
    have hRV : p.2=q.2 := by
      funext j
      exact Subtype.ext ((congrFun hP (.inr j)).trans ((hTags j).trans (congrFun hQ (.inr j)).symm))
    intro i
    have hVF := congrArg Subtype.val (congrFun (h p hxA q hyA hRV) i)
    change iRv (x (.inl i))=iRv (y (.inl i))
    change iRv (p.1 i).val=iRv (q.1 i).val at hVF
    rw [← congrFun hP (.inl i),← congrFun hQ (.inl i)]
    exact hVF

end DiamondIntegral.Section6
