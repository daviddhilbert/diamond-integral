import «section 6».BranchedShearBijections
import «section 6».ProperGraphChartContinuity

/-! Every fixed-label branch of the actual selected map is a global
continuous shear restricted to the indicator's clopen source. Its graph
range is clopen and its VF graph map is continuous. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BranchedShearData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def fieldMap (T : BranchedShearData (G := G) A) (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M)
    (x : Fin (n+1) → VF M) : Fin (n+1) → VF M :=
  Fin.snoc (Fin.init x) (x (Fin.last n)+T.offset (Fin.append u v) (Fin.init x) 0)

def fieldHomeomorph (T : BranchedShearData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M) :
    (Fin (n+1) → VF M) ≃ₜ (Fin (n+1) → VF M) where
  toFun := T.fieldMap u v
  invFun := fun y => Fin.snoc (Fin.init y) (y (Fin.last n)-T.offset (Fin.append u v) (Fin.init y) 0)
  left_inv x := by simp [fieldMap]
  right_inv y := by simp [fieldMap]
  continuous_toFun := by
    have hInit : Continuous (fun x : Fin (n+1) → VF M => Fin.init x) := by fun_prop
    have hOffset := (continuous_apply (0 : Fin 1)).comp ((T.offset_continuous (Fin.append u v)).comp hInit)
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hC := continuous_add.comp ((continuous_apply (Fin.last n)).prodMk hOffset)
      simpa only [fieldMap,Fin.snoc_last,Function.comp_def] using hC
    · simpa only [fieldMap,Fin.snoc_castSucc,Fin.init] using (continuous_apply j.castSucc)
  continuous_invFun := by
    have hInit : Continuous (fun x : Fin (n+1) → VF M => Fin.init x) := by fun_prop
    have hOffset := (continuous_apply (0 : Fin 1)).comp ((T.offset_continuous (Fin.append u v)).comp hInit)
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hC := continuous_sub.comp ((continuous_apply (Fin.last n)).prodMk hOffset)
      simpa only [Fin.snoc_last,Function.comp_def] using hC
    · simpa only [Fin.snoc_castSucc,Fin.init] using (continuous_apply j.castSucc)

theorem graph_iff (T : BranchedShearData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M)
    (a b : Fin (n+1) → VF M) :
    graphFibre T.map u v a b ↔ T.indicator (Fin.append u v) a 0=1 ∧ b=T.fieldMap u v a := by
  constructor
  · rintro ⟨p,hp,hfp⟩
    have hVF : p.val.1=a := congrArg Prod.fst hp
    have hIn := congrArg Prod.snd hp
    have hOut := congrArg Prod.snd hfp
    change T.outputLabels p=v at hOut
    have hχ := T.selected_indicator p
    rw [hVF,hIn,hOut] at hχ
    refine ⟨hχ,?_⟩
    have hValue := T.map_value p
    rw [hVF,hIn,hOut] at hValue
    have hF := congrArg Prod.fst hfp
    exact hF.symm.trans (congrArg Prod.fst hValue)
  · rintro ⟨hχ,hb⟩
    have ha : (a,u) ∈ A.carrier := (T.source a u).mpr ⟨v,hχ⟩
    let p : A := ⟨(a,u),ha⟩
    have hLabels : T.outputLabels p=v := T.unique a u _ v (T.selected_indicator p) hχ
    have hValue : (T.map p).val=(T.fieldMap u v a,v) := by
      rw [T.map_value,hLabels]
      rfl
    exact ⟨p,rfl,hValue.trans (Prod.ext hb.symm rfl)⟩

theorem graph_source (T : BranchedShearData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M) :
    graphFibreSource T.map u v={x | T.indicator (Fin.append u v) x 0=1} := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    exact ((T.graph_iff u v x y).mp hy).1
  · intro hx
    exact ⟨T.fieldMap u v x,(T.graph_iff u v x _).mpr ⟨hx,rfl⟩⟩

theorem graph_range (T : BranchedShearData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M) :
    graphFibreRange T.map u v=T.fieldMap u v '' graphFibreSource T.map u v := by
  ext y
  constructor
  · rintro ⟨x,hxy⟩
    have h := (T.graph_iff u v x y).mp hxy
    exact ⟨x,⟨y,hxy⟩,h.2.symm⟩
  · rintro ⟨x,hx,rfl⟩
    rw [T.graph_source] at hx
    exact ⟨x,(T.graph_iff u v x _).mpr ⟨hx,rfl⟩⟩

theorem graph_source_clopen (T : BranchedShearData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M) : IsClopen (graphFibreSource T.map u v) := by
  rw [T.graph_source]
  have h := clopen_indicator_level Set.univ isClopen_univ
    (fun x => T.indicator (Fin.append u v) x 0)
    (((continuous_apply (0 : Fin 1)).comp (T.indicator_continuous (Fin.append u v))).continuousOn)
    (fun x _ => T.binary (Fin.append u v) x)
  simpa only [Set.mem_univ,true_and] using h

theorem graph_range_clopen (T : BranchedShearData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin T.arity → RVInfinity M) : IsClopen (graphFibreRange T.map u v) := by
  rw [T.graph_range]
  have hD := T.graph_source_clopen u v
  exact ⟨(T.fieldHomeomorph u v).isClosedMap _ hD.isClosed,(T.fieldHomeomorph u v).isOpenMap _ hD.isOpen⟩

theorem map_continuous (T : BranchedShearData (G := G) A) : ContinuousOnGraphFibres T.map := by
  intro u v
  apply ((T.fieldHomeomorph u v).continuous.continuousOn).congr
  intro x hx
  exact ((T.graph_iff u v x _).mp (graphFibreMap_graph T.map u v hx)).2

end DiamondIntegral.Section6.BranchedShearData
