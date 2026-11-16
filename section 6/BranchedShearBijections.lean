import «section 6».BranchedShearMaps

/-! The selected shear is a bijection onto its actual image. Both
the original RV tuple and the active input point are recovered from
the output tuple and the fixed inactive coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BranchedShearData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem map_injective (T : BranchedShearData (G := G) A) : Function.Injective T.map := by
  intro p q he
  have hLabels : T.outputLabels p=T.outputLabels q := by
    have h := congrArg (fun z : T.target => z.val.2) he
    simpa only [T.map_labels] using h
  have hOld : p.val.2=q.val.2 := by
    funext i
    exact (T.map_retained p i).symm.trans
      ((congrArg (fun z : T.target => z.val.2 (T.labels i)) he).trans (T.map_retained q i))
  have hBase : Fin.init p.val.1=Fin.init q.val.1 := by
    have h := congrArg (fun z : T.target => Fin.init z.val.1) he
    simpa only [T.map_base] using h
  have hLast : p.val.1 (Fin.last n)=q.val.1 (Fin.last n) := by
    have h := congrArg (fun z : T.target => z.val.1 (Fin.last n)) he
    rw [T.map_last,T.map_last,hLabels,hOld,hBase] at h
    exact add_right_cancel h
  apply Subtype.ext
  apply Prod.ext
  · calc
      _=Fin.snoc (Fin.init p.val.1) (p.val.1 (Fin.last n)) := (Fin.snoc_init_self _).symm
      _=Fin.snoc (Fin.init q.val.1) (q.val.1 (Fin.last n)) := congrArg₂ Fin.snoc hBase hLast
      _=_ := Fin.snoc_init_self _
  · exact hOld

theorem map_bijective (T : BranchedShearData (G := G) A) : Function.Bijective T.map :=
  ⟨T.map_injective,map_toImage_surjective T.rawMap⟩

theorem map_relative (T : BranchedShearData (G := G) A) (p : A) (i : Fin n) :
    (T.map p).val.1 i.castSucc=p.val.1 i.castSucc := congrFun (T.map_base p) i

theorem map_shear_displacement (T : BranchedShearData (G := G) A) :
    SameLabelShearDisplacement T.map (Fin.last n) := by
  intro p q hInput hOutput hInactive
  have hLabels : T.outputLabels p=T.outputLabels q := by
    simpa only [T.map_labels] using hOutput
  have hBase : Fin.init p.val.1=Fin.init q.val.1 := funext (fun i => hInactive i.castSucc (Fin.castSucc_ne_last i))
  rw [T.map_last,T.map_last,hInput,hLabels,hBase]
  abel

end DiamondIntegral.Section6.BranchedShearData
