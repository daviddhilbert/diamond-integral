import «section 6».ShearChartFamilyValues
import «section 6».BranchedShearContractions

/-! Extract continuous original-base indicator and inactive offset
families from an actual strengthened contraction stage. Their exact
source, label and leading-term conditions are proved on the full graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem RVSupportDoublyBounded.nonzero_code
    {B : Set (Mixed M n s)} (hB : RVSupportDoublyBounded B) (p : Mixed M n s) (hp : p ∈ B) (i : Fin s) :
    (p.2 i).val ≠ iRVZero := by
  obtain ⟨β,hβ⟩ := hB
  intro hz
  have hInf := (Values.vrv_eq_infinity_iff (p.2 i)).mpr hz
  have h := (hβ p hp i).2
  rw [hInf] at h
  exact β.property (le_antisymm (Values.le_infinity _) h)

namespace ShearContractionStage
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def indicatorFamily (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M)) :=
  totalFocusFibre (graphChartSourceIndicator hc T.stage.lift)

def offsetFamily (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M)) :=
  totalFocusFibre (graphShearBaseDisplacement hc T.stage.lift T.displacement)

theorem indicatorFamily_eq_one_iff
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (u : Fin r → RVInfinity M) (v : Fin T.stage.arity → RVInfinity M) (x : Fin (n+1) → VF M) :
    T.indicatorFamily hc (Fin.append u v) x 0=1 ↔ x ∈ graphFibreSource T.stage.lift u v := by
  simpa only [indicatorFamily,Function.comp_def,Fin.append_left,Fin.append_right] using
    graphChartSourceIndicator_eq_one_iff hc T.stage.lift (Fin.append u v) x

theorem offsetFamily_at_graph
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (u : Fin r → RVInfinity M) (v : Fin T.stage.arity → RVInfinity M)
    (x y : Fin (n+1) → VF M) (hGraph : graphFibre T.stage.lift u v x y) :
    T.offsetFamily hc (Fin.append u v) (Fin.init x) 0=y (Fin.last n)-x (Fin.last n) :=
  graphShearBaseDisplacement_at_graph hc T.stage.lift T.displacement u v x y hGraph

theorem indicatorFamily_source
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) :
    (x,u) ∈ A.carrier ↔ ∃ v,T.indicatorFamily hc (Fin.append u v) x 0=1 := by
  constructor
  · intro hx
    let p : A := ⟨(x,u),hx⟩
    exact ⟨(T.stage.lift p).val.2,(T.indicatorFamily_eq_one_iff hc u _ x).mpr
      ⟨(T.stage.lift p).val.1,p,rfl,rfl⟩⟩
  · rintro ⟨v,hv⟩
    obtain ⟨y,p,hp,hfp⟩ := (T.indicatorFamily_eq_one_iff hc u v x).mp hv
    exact hp ▸ p.property

theorem indicatorFamily_unique
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) (v w : Fin T.stage.arity → RVInfinity M)
    (hv : T.indicatorFamily hc (Fin.append u v) x 0=1)
    (hw : T.indicatorFamily hc (Fin.append u w) x 0=1) : v=w := by
  obtain ⟨y,p,hp,hfp⟩ := (T.indicatorFamily_eq_one_iff hc u v x).mp hv
  obtain ⟨z,q,hq,hfq⟩ := (T.indicatorFamily_eq_one_iff hc u w x).mp hw
  have he : p=q := Subtype.ext (hp.trans hq.symm)
  have hV := congrArg Prod.snd hfp
  have hW := congrArg Prod.snd hfq
  exact hV.symm.trans ((congrArg (fun a : A => (T.stage.lift a).val.2) he).trans hW)

theorem indicatorFamily_retained
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) (v : Fin T.stage.arity → RVInfinity M)
    (hv : T.indicatorFamily hc (Fin.append u v) x 0=1) : v ∘ T.stage.oldLabels=u := by
  obtain ⟨y,p,hp,hfp⟩ := (T.indicatorFamily_eq_one_iff hc u v x).mp hv
  have hInput := congrArg Prod.snd hp
  have hOutput := congrArg Prod.snd hfp
  funext i
  have h := T.stage.retained p i
  rw [hInput,hOutput] at h
  exact h

theorem indicatorFamily_nonzero
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) (v : Fin T.stage.arity → RVInfinity M)
    (hv : T.indicatorFamily hc (Fin.append u v) x 0=1) (i : Fin T.stage.arity) : (v i).val ≠ iRVZero := by
  obtain ⟨y,p,hp,hfp⟩ := (T.indicatorFamily_eq_one_iff hc u v x).mp hv
  have h := T.stage.proper.rvBounded.nonzero_code (T.stage.lift p).val (T.stage.lift p).property i
  have hOutput := congrArg Prod.snd hfp
  rw [hOutput] at h
  exact h

theorem indicatorFamily_leading
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) (v : Fin T.stage.arity → RVInfinity M)
    (hv : T.indicatorFamily hc (Fin.append u v) x 0=1) :
    rv M (x (Fin.last n)+T.offsetFamily hc (Fin.append u v) (Fin.init x) 0)=v T.stage.leading := by
  obtain ⟨y,hGraph⟩ := (T.indicatorFamily_eq_one_iff hc u v x).mp hv
  rw [T.offsetFamily_at_graph hc u v x y hGraph]
  obtain ⟨p,hp,hfp⟩ := hGraph
  have hTarget : (y,v) ∈ T.stage.target.carrier := hfp ▸ (T.stage.lift p).property
  have hLeading := ((T.stage.recover_target (y,v)).mp hTarget).2
  have he : x (Fin.last n)+(y (Fin.last n)-x (Fin.last n))=y (Fin.last n) := by abel
  rw [he]
  exact hLeading

end ShearContractionStage
end DiamondIntegral.Section6
