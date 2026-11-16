import «section 6».UniformMixedDifferentiability
import «section 6».ContinuousShears

/-! A relatively unary map whose displacement is constant on each
fixed-label inactive fibre has actual shear charts. Its generic unit
total derivative follows from definable differentiability, without an
extra differentiability premise for a chosen focus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def SameLabelShearDisplacement (f : Map A B) (j : Fin n) : Prop :=
  ∀ p q : A,p.val.2=q.val.2 → (f p).val.2=(f q).val.2 →
    (∀ i,i ≠ j → p.val.1 i=q.val.1 i) →
    (f p).val.1 j-p.val.1 j=(f q).val.1 j-q.val.1 j

def graphShearFocus (f : Map A B) (j : Fin n)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (b : Fin n → VF M) : VF M :=
  if h : ∃ q : A,q.val.2=u ∧ (f q).val.2=v ∧ Function.update q.val.1 j 0=b then
    (f h.choose).val.1 j-h.choose.val.1 j else 0

theorem graphShearFocus_value (f : Map A B) (j : Fin n) (hStable : SameLabelShearDisplacement f j)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (p : A) (hIn : p.val.2=u) (hOut : (f p).val.2=v) :
    graphShearFocus f j u v (Function.update p.val.1 j 0)=(f p).val.1 j-p.val.1 j := by
  have h : ∃ q : A,q.val.2=u ∧ (f q).val.2=v ∧ Function.update q.val.1 j 0=Function.update p.val.1 j 0 :=
    ⟨p,hIn,hOut,rfl⟩
  rw [graphShearFocus,dite_eq_left h]
  obtain ⟨hQIn,hQOut,hErase⟩ := h.choose_spec
  apply hStable h.choose p (hQIn.trans hIn.symm) (hQOut.trans hOut.symm)
  intro i hi
  simpa only [Function.update_of_ne hi] using congrFun hErase i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem relative_shear_chart
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (j : Fin n)
    (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (hStable : SameLabelShearDisplacement f j)
    (hOpen : ∀ u v,IsOpen (graphFibreSource f u v)) (p : A) :
    IsVFChartAt f p (coordinateShear j (graphShearFocus f j p.val.2 (f p).val.2)) := by
  have hp : p.val.1 ∈ graphFibreSource f p.val.2 (f p).val.2 := ⟨(f p).val.1,p,rfl,rfl⟩
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1 ((hOpen _ _).mem_nhds hp)
  refine ⟨ρ,fun x hx => ?_⟩
  obtain ⟨b,q,hq,hfq⟩ := hρ hx
  have hSource : (x,p.val.2) ∈ A.carrier := hq ▸ q.property
  have hTyped : (⟨(x,p.val.2),hSource⟩ : A)=q := Subtype.ext hq.symm
  refine ⟨hSource,?_⟩
  change (f (⟨(x,p.val.2),hSource⟩ : A)).val=_
  rw [hTyped]
  have hVF : q.val.1=x := congrArg Prod.fst hq
  have hIn := congrArg Prod.snd hq
  have hOut := congrArg Prod.snd hfq
  apply Prod.ext
  · change (f q).val.1=coordinateShear j (graphShearFocus f j p.val.2 (f p).val.2) x
    rw [← hVF]
    funext i
    by_cases hi : i=j
    · subst i
      simp only [coordinateShear,Function.update_self]
      rw [graphShearFocus_value f j hStable _ _ q hIn hOut]
      abel
    · rw [coordinateShear_other j i hi]
      exact hRelative q i hi
  · exact hOut

theorem relative_shear_generic_unit
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (j : Fin n)
    (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (hStable : SameLabelShearDisplacement f j)
    (hOpen : ∀ u v,IsOpen (graphFibreSource f u v))
    (p : A) (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) : HasMixedUnitDerivativeAt f p := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  exact mixed_unit_derivative_of_shear_chart f p j _
    (relative_shear_chart hv f j hRelative hStable hOpen p)
    (mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f p hInd)

end DiamondIntegral.Section6
