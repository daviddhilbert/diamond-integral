import «section 5».ElementaryRawGraphMaps
import «section 5».EmptyGammaSortedDefinability
import «section 4».FiniteTupleGraphProduct

/-! Full ordinary definable raw RV graphs realize actual native maps
and bijections over the same real ground, with the literal domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge FiniteTupleBlocks
variable {M P : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (c : P → M) {n m : ℕ}

def rawRVSetNative (A : LRV.DefinableSet (Set.range c) (Fin n))
    (hA : ∀ x ∈ A.val,∀ i,iRV (x i)) :
    GammaGroundDefSet hc (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) n) :=
  ofRaw A.val ((emptyGamma_sorted_definable_iff hc _ _ _).mpr ⟨A.property,hA⟩)

variable {hc c}
variable {A : LRV.DefinableSet (Set.range c) (Fin n)} {B : LRV.DefinableSet (Set.range c) (Fin m)}

def rawGraphExtension (f : RawDefinableGraphMap c A B) (x : Fin n → M) : Fin m → M :=
  if hx : x ∈ A.val then (f.toFun ⟨x,hx⟩).val else fun _ => iRVZero

def joinedToCanonicalIndices (n m : ℕ) : Fin (n+m) → Fin (m+n) :=
  Fin.append (headIndex m n) (tailIndex m n)

theorem comp_joinedToCanonical {Q : Type} (w : Fin (m+n) → Q) :
    w ∘ joinedToCanonicalIndices n m = Fin.append (w ∘ headIndex m n) (w ∘ tailIndex m n) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [joinedToCanonicalIndices,Function.comp_def]

theorem rawGraphExtension_graph_definable (f : RawDefinableGraphMap c A B) :
    (Set.range c).Definable LRV (RVMeasuredCharts.graphOn A.val (rawGraphExtension f)) := by
  have hd := f.graph_definable.preimage_comp (joinedToCanonicalIndices n m)
  suffices he : {w : Fin (m+n) → M | w ∘ joinedToCanonicalIndices n m ∈ f.graph.val} =
      RVMeasuredCharts.graphOn A.val (rawGraphExtension f) by exact he ▸ hd
  ext w
  change (w ∘ joinedToCanonicalIndices n m ∈ f.graph.val) ↔ _
  rw [comp_joinedToCanonical,f.graph_append_iff]
  constructor
  · rintro ⟨a,ha,hf⟩
    refine ⟨ha ▸ a.property,?_⟩
    rw [rawGraphExtension,dif_pos (ha ▸ a.property)]
    have he : (⟨w ∘ headIndex m n,ha ▸ a.property⟩ : A.val) = a := Subtype.ext ha.symm
    exact (congrArg (fun b : A.val => (f.toFun b).val) he).trans hf
  · rintro ⟨hx,hf⟩
    refine ⟨⟨w ∘ headIndex m n,hx⟩,rfl,?_⟩
    simpa only [rawGraphExtension,dif_pos hx] using hf

variable (hc c)
variable (hA : ∀ x ∈ A.val,∀ i,iRV (x i)) (hB : ∀ x ∈ B.val,∀ i,iRV (x i))

include hA hB in
theorem rawGraphExtension_graph_sorted (f : RawDefinableGraphMap c A B) :
    ∀ w ∈ RVMeasuredCharts.graphOn A.val (rawGraphExtension f),∀ i,iRV (w i) := by
  intro w hw
  apply GammaBoundedProducts.all_coordinates m n iRV w
  · exact hA _ hw.1
  · intro i
    have h := hB (f.toFun ⟨w ∘ headIndex m n,hw.1⟩).val (f.toFun ⟨w ∘ headIndex m n,hw.1⟩).property i
    have he : (f.toFun ⟨w ∘ headIndex m n,hw.1⟩).val = w ∘ tailIndex m n := by
      simpa only [rawGraphExtension,dif_pos hw.1] using hw.2
    exact (congrArg iRV (congrFun he i)).mp h

def rawGraphNativeMap (f : RawDefinableGraphMap c A B) :
    GammaGroundMap (rawRVSetNative hc c A hA) (rawRVSetNative hc c B hB) := by
  let hFA : DefinableOverBase (EmptyGammaGround.base (Set.range c))
      (fun _ : Fin (m+n) => .rv) (RVMeasuredCharts.graphOn A.val (rawGraphExtension f)) :=
    (emptyGamma_sorted_definable_iff hc _ _ _).mpr
    ⟨rawGraphExtension_graph_definable f,rawGraphExtension_graph_sorted c hA hB f⟩
  let g := mapOfRaw (hc := hc) A.val ((emptyGamma_sorted_definable_iff hc _ _ _).mpr ⟨A.property,hA⟩)
    (rawGraphExtension f) hFA (by
      intro x hx
      rw [rawGraphExtension,dif_pos hx]
      exact hB _ (f.toFun ⟨x,hx⟩).property)
  exact g.corestrict (B' := rawRVSetNative hc c B hB) (by
    intro a
    change rawGraphExtension f (rvValues a.val) ∈ B.val
    have hv : rawGraphExtension f (rvValues a.val) = (f.toFun ⟨rvValues a.val,a.property⟩).val :=
      dif_pos a.property
    exact (congrArg (fun t : Fin m → M => t ∈ B.val) hv).mpr
      (f.toFun ⟨rvValues a.val,a.property⟩).property)

theorem rawGraphNativeMap_value (f : RawDefinableGraphMap c A B) (a : rawRVSetNative hc c A hA) :
    rvValues ((rawGraphNativeMap hc c hA hB f) a).val = (f.toFun ⟨rvValues a.val,a.property⟩).val := by
  have h : rvValues ((rawGraphNativeMap hc c hA hB f) a).val =
      rawGraphExtension f (rvValues a.val) := rfl
  exact h.trans (dif_pos a.property)

theorem rawGraphNativeMap_bijective (f : RawDefinableGraphMap c A B) (hf : Function.Bijective f.toFun) :
    Function.Bijective (rawGraphNativeMap hc c hA hB f) := by
  constructor
  · intro a b he
    have h := congrArg (fun z : rawRVSetNative hc c B hB => rvValues z.val) he
    rw [rawGraphNativeMap_value,rawGraphNativeMap_value] at h
    have hh := hf.1 (Subtype.ext h)
    exact Subtype.ext (rvValues_injective (congrArg Subtype.val hh))
  · intro b
    obtain ⟨x,hx⟩ := hf.2 ⟨rvValues b.val,b.property⟩
    let a : rawRVSetNative hc c A hA := ⟨fun i => ⟨x.val i,hA x.val x.property i⟩,x.property⟩
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply rvValues_injective
    rw [rawGraphNativeMap_value]
    exact congrArg Subtype.val hx

end DiamondIntegral.Section5
