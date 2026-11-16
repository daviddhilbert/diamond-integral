import «section 6».BranchedShearData
import «section 6».CarriedDefinableMaps
import «section 6».VFTupleArithmeticMaps

/-! Actual full maps selected by continuous branched shear data.
The source graph supplies a definable unique label choice, and the VF
coordinate update is constructed from actual definable arithmetic maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BranchedShearData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def graphMap (T : BranchedShearData (G := G) A) :
    Map T.domain (DefSet.univ (rawMixedSpace (M := M) (n+1) T.arity) S) := by
  let δ := (rvFamilyMap (DefSet.univ (rawMixedSpace (M := M) n (r+T.arity)) S) T.offset T.offset_definable).comp
    (vfDropLast T.domain)
  let a := (vfTupleSelectMap S (fun _ : Fin 1 => Fin.last n)).comp (mixedVFHeadMap T.domain)
  let y := (vfTupleBinaryMap S .add).comp (a.pair δ).toUniv
  let F := appendTailMap (vfDropLast T.domain) y
  exact (selectRVLabelsMap (DefSet.univ (rawMixedSpace (M := M) (n+1) (r+T.arity)) S) (Fin.natAdd r)).comp F

theorem graphMap_value (T : BranchedShearData (G := G) A) (p : T.domain) :
    (T.graphMap p).val=
      (Fin.snoc (Fin.init p.val.1) (p.val.1 (Fin.last n)+T.offset p.val.2 (Fin.init p.val.1) 0),p.val.2 ∘ Fin.natAdd r) := by
  change (productTuple (Fin.init p.val.1)
    (fun j : Fin 1 => p.val.1 (Fin.last n)+T.offset p.val.2 (Fin.init p.val.1) j),p.val.2 ∘ Fin.natAdd r)=_
  have hTail : (fun j : Fin 1 => p.val.1 (Fin.last n)+T.offset p.val.2 (Fin.init p.val.1) j)=
      (fun _ : Fin 1 => p.val.1 (Fin.last n)+T.offset p.val.2 (Fin.init p.val.1) 0) := by
    funext j
    rw [show j=(0 : Fin 1) from Subsingleton.elim _ _]
  rw [hTail]
  rw [productTuple_singleton_eq_snoc]

def rawMap (T : BranchedShearData (G := G) A) := T.graphMap.comp T.selectedPoint

def target (T : BranchedShearData (G := G) A) := T.rawMap.image

def map (T : BranchedShearData (G := G) A) : Map A T.target := T.rawMap.toImage

def outputLabels (T : BranchedShearData (G := G) A) (p : A) : Fin T.arity → RVInfinity M :=
  (T.selectedPoint p).val.2 ∘ Fin.natAdd r

theorem selectedPoint_labels (T : BranchedShearData (G := G) A) (p : A) :
    (T.selectedPoint p).val.2=Fin.append p.val.2 (T.outputLabels p) := by
  have hOld : (T.selectedPoint p).val.2 ∘ Fin.castAdd T.arity=p.val.2 :=
    congrArg (fun q : A => q.val.2) (T.selectedPoint_source p)
  calc
    _=Fin.append ((T.selectedPoint p).val.2 ∘ Fin.castAdd T.arity) (T.outputLabels p) := Fin.append_castAdd_natAdd.symm
    _=_ := congrArg (fun u => Fin.append u (T.outputLabels p)) hOld

theorem selected_indicator (T : BranchedShearData (G := G) A) (p : A) :
    T.indicator (Fin.append p.val.2 (T.outputLabels p)) p.val.1 0=1 := by
  have h := (T.mem_domain (T.selectedPoint p).val).mp (T.selectedPoint p).property
  rw [T.selectedPoint_labels,T.selectedPoint_vf] at h
  exact h

theorem map_value (T : BranchedShearData (G := G) A) (p : A) :
    (T.map p).val=
      (Fin.snoc (Fin.init p.val.1)
        (p.val.1 (Fin.last n)+T.offset (Fin.append p.val.2 (T.outputLabels p)) (Fin.init p.val.1) 0),T.outputLabels p) := by
  change (T.graphMap (T.selectedPoint p)).val=_
  rw [T.graphMap_value,T.selectedPoint_vf,T.selectedPoint_labels]
  apply Prod.ext
  · rfl
  · funext i
    exact Fin.append_right p.val.2 (T.outputLabels p) i

theorem map_base (T : BranchedShearData (G := G) A) (p : A) : Fin.init (T.map p).val.1=Fin.init p.val.1 := by
  rw [T.map_value,Fin.init_snoc]

theorem map_last (T : BranchedShearData (G := G) A) (p : A) :
    (T.map p).val.1 (Fin.last n)=p.val.1 (Fin.last n)+
      T.offset (Fin.append p.val.2 (T.outputLabels p)) (Fin.init p.val.1) 0 := by
  simp only [T.map_value,Fin.snoc_last]

theorem map_labels (T : BranchedShearData (G := G) A) (p : A) : (T.map p).val.2=T.outputLabels p := by
  rw [T.map_value]

theorem map_retained (T : BranchedShearData (G := G) A) (p : A) (i : Fin r) :
    (T.map p).val.2 (T.labels i)=p.val.2 i := by
  rw [T.map_labels]
  exact congrFun (T.retained _ _ _ (T.selected_indicator p)) i

theorem map_leading (T : BranchedShearData (G := G) A) (p : A) :
    rv M ((T.map p).val.1 (Fin.last n))=(T.map p).val.2 T.leading := by
  rw [T.map_last,T.map_labels]
  exact T.leading_value _ _ _ (T.selected_indicator p)

theorem map_nonzero (T : BranchedShearData (G := G) A) (p : A) (i : Fin T.arity) :
    ((T.map p).val.2 i).val ≠ iRVZero := by
  rw [T.map_labels]
  exact T.nonzero _ _ _ (T.selected_indicator p) i

end DiamondIntegral.Section6.BranchedShearData
