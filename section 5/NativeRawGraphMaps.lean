import «section 5».ElementaryRawGraphMaps
import «section 5».EmptyGammaSortedDefinability
import «section 4».FiniteTupleGraphProduct

/-! Actual native RV maps have full ordinary first-order raw graph maps.
The canonical coordinate order is source followed by target; all zero
coordinates and all original named parameters are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge FiniteTupleBlocks
variable {M P : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (c : P → M) {n m : ℕ}

def nativeRawDomainSet
    (D : GammaGroundDefSet hc (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) n)) :
    LRV.DefinableSet (Set.range c) (Fin n) := ⟨rawDomain D,emptyGamma_rawDomain_definable hc _ D⟩

def canonicalToJoinedIndices (n m : ℕ) : Fin (m+n) → Fin (n+m) :=
  join m n (Fin.castAdd m) (Fin.natAdd n)

theorem append_comp_canonicalToJoined {Q : Type} (x : Fin n → Q) (y : Fin m → Q) :
    Fin.append x y ∘ canonicalToJoinedIndices n m = join m n x y := by
  apply FiniteTupleGraphProduct.block_ext m n <;> funext i <;>
    simp only [Function.comp_apply,canonicalToJoinedIndices,join_head,join_tail,Fin.append_left,Fin.append_right]

variable {hc c}
variable {D : GammaGroundDefSet hc (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) n)}
variable {E : GammaGroundDefSet hc (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) m)}

def nativeRawTupleMap (f : GammaGroundMap D E) :
    (nativeRawDomainSet hc c D).val → (nativeRawDomainSet hc c E).val :=
  fun a => ⟨rvValues (f ((rawEquiv D).symm a)).val,
    ⟨(f ((rawEquiv D).symm a)).val,(f ((rawEquiv D).symm a)).property,rfl⟩⟩

theorem nativeRawTupleMap_graph_definable (f : GammaGroundMap D E) :
    (Set.range c).Definable LRV
      {w | ∃ a : (nativeRawDomainSet hc c D).val,w = Fin.append a.val (nativeRawTupleMap f a).val} := by
  have hd := (((emptyGamma_sorted_definable_iff hc _ _ _).mp (joinedGraph_definable f)).1).preimage_comp
    (canonicalToJoinedIndices n m)
  suffices he : {w : Fin (n+m) → M | w ∘ canonicalToJoinedIndices n m ∈ joinedGraph f} =
      {w | ∃ a : (nativeRawDomainSet hc c D).val,w = Fin.append a.val (nativeRawTupleMap f a).val} by
    exact he ▸ hd
  ext w
  constructor
  · rintro ⟨a,ha⟩
    have hs : w ∘ Fin.castAdd m = rvValues a.val := by
      funext i
      simpa only [Function.comp_apply,canonicalToJoinedIndices,join_head] using congrFun ha (headIndex m n i)
    have ht : w ∘ Fin.natAdd n = rvValues (f a).val := by
      funext i
      simpa only [Function.comp_apply,canonicalToJoinedIndices,join_tail] using congrFun ha (tailIndex m n i)
    refine ⟨rawEquiv D a,?_⟩
    change w = Fin.append (rvValues a.val) (rvValues (f ((rawEquiv D).symm (rawEquiv D a))).val)
    rw [_root_.Equiv.symm_apply_apply]
    exact (Fin.append_castAdd_natAdd (f := w)).symm.trans (congrArg₂ Fin.append hs ht)
  · rintro ⟨b,rfl⟩
    let a := (rawEquiv D).symm b
    refine ⟨a,?_⟩
    rw [append_comp_canonicalToJoined]
    change join m n b.val (rvValues (f a).val) = join m n (rvValues a.val) (rvValues (f a).val)
    exact congrArg (fun z => join m n z (rvValues (f a).val)) (rawEquiv_symm_value D b).symm

def nativeRawGraphMap (f : GammaGroundMap D E) :
    RawDefinableGraphMap c (nativeRawDomainSet hc c D) (nativeRawDomainSet hc c E) where
  toFun := nativeRawTupleMap f
  graph_definable := nativeRawTupleMap_graph_definable f

theorem nativeRawGraphMap_bijective (f : GammaGroundMap D E) (hf : Function.Bijective f) :
    Function.Bijective (nativeRawGraphMap f).toFun :=
  (rawEquiv E).bijective.comp (hf.comp (rawEquiv D).symm.bijective)

end DiamondIntegral.Section5
