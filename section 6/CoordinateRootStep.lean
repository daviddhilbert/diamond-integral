import «section 6».CoordinateStepFibres

/-! The actual remaining roots after a last-coordinate permitted step.
Only the noncore flag is retained. Every new fiber is contained in the
strictly smaller arithmetic child of its actual old mean-root fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def remainingRoots (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A) :=
  rvTagSlice ((centripetalStepMap D).restrict R.subset).image
    (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) false

theorem remainingRoots_iff (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (q : Mixed M (n+1) ((n+1)+(1+r))) :
    q ∈ (R.remainingRoots D).carrier ↔ ∃ a : A, a.val ∈ R.roots.carrier ∧
      D.core a.val = false ∧ regularize (D.point a.val) = q := by
  constructor
  · rintro ⟨⟨p,hp⟩,hflag⟩
    let a : A := ⟨p.val,R.subset p.property⟩
    have he : regularize (D.point a.val) = q := hp
    have hh := congrArg (fun z : Mixed M (n+1) ((n+1)+(1+r)) =>
      z.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1)))) he
    rw [D.regularized_core_flag] at hh
    exact ⟨a,p.property,branchTag_injective h00 (hh.trans hflag),he⟩
  · rintro ⟨a,ha,hCore,he⟩
    refine ⟨⟨⟨a.val,ha⟩,he⟩,?_⟩
    rw [← he,D.regularized_core_flag,hCore]

def cutoff (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (b : Fin n → VF M) (u : Fin r → RVInfinity M) : Gamma M :=
  if h : D.coefficient*Barycentre.mean (R.fibre b u) ≠ 0 then finiteValue _ h else 1

theorem remainingRoots_child_subset (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2))
    (b : Fin n → VF M) (u : Fin ((n+1)+(1+r)) → RVInfinity M) (x : VF M)
    (hx : (Fin.snoc b x,u) ∈ (R.remainingRoots D).carrier) :
    x ∈ noncoreRootChild (R.fibre b (coordinateStepOldTags u)) (R.cutoff D b (coordinateStepOldTags u))
      (u (Fin.castAdd (1+r) (Fin.last n))) := by
  obtain ⟨a,ha,hCore,he⟩ := (R.remainingRoots_iff D h00 _).mp hx
  have hOld : a.val.2 = coordinateStepOldTags u := by
    funext i
    have hh := congrArg (fun q : Mixed M (n+1) ((n+1)+(1+r)) =>
      q.2 (Fin.natAdd (n+1) (Fin.natAdd 1 i))) he
    simpa only [regularize,CentripetalData.point,Fin.append_right,coordinateStepOldTags] using hh
  have hInit : Fin.init a.val.1 = b := by
    funext i
    have hh := congrArg (fun q : Mixed M (n+1) ((n+1)+(1+r)) => q.1 i.castSucc) he
    simpa only [regularize,CentripetalData.point,hj,Function.update_of_ne (Fin.castSucc_ne_last i),
      Fin.snoc_castSucc,Fin.init] using hh
  have hFocus : D.extendedFocus a.val = Barycentre.mean (R.fibre b (coordinateStepOldTags u)) := by
    rw [hMean a.val ha,hInit,hOld]
  have hxValue : a.val.1 (Fin.last n)-Barycentre.mean (R.fibre b (coordinateStepOldTags u)) = x := by
    have hh := congrArg (fun q : Mixed M (n+1) ((n+1)+(1+r)) => q.1 (Fin.last n)) he
    simpa only [regularize,CentripetalData.point,hj,Function.update_self,hCore,Bool.false_eq_true,
      ite_false,add_zero,hFocus,Fin.snoc_last] using hh
  have hRV : rv M (a.val.1 (Fin.last n)-Barycentre.mean (R.fibre b (coordinateStepOldTags u))) =
      u (Fin.castAdd (1+r) (Fin.last n)) := by
    have hh := congrArg (fun q : Mixed M (n+1) ((n+1)+(1+r)) =>
      q.2 (Fin.castAdd (1+r) (Fin.last n))) he
    simp only [regularize,Fin.append_left] at hh
    change rv M ((D.point a.val).1 (Fin.last n)) = _ at hh
    simpa only [CentripetalData.point,hj,Function.update_self,hCore,Bool.false_eq_true,
      ite_false,add_zero,hFocus] using hh
  have hprod : D.coefficient*Barycentre.mean (R.fibre b (coordinateStepOldTags u)) ≠ 0 := by
    rw [← hFocus]
    exact mul_ne_zero D.coefficient_nonzero (D.focus_nonzero a.property (hActive a.val ha))
  have hCutoff : (R.cutoff D b (coordinateStepOldTags u)).val =
      vfValue (D.coefficient*Barycentre.mean (R.fibre b (coordinateStepOldTags u))) := by
    rw [cutoff,dite_eq_left hprod]
    rfl
  have hCut : vfValue (a.val.1 (Fin.last n)-Barycentre.mean (R.fibre b (coordinateStepOldTags u))) ≤
      (R.cutoff D b (coordinateStepOldTags u)).val := by
    have hh : vfValue (a.val.1 D.coordinate-D.extendedFocus a.val) ≤
        vfValue (D.coefficient*D.extendedFocus a.val) := le_of_not_gt (of_decide_eq_false hCore)
    simpa only [hj,hFocus,hCutoff] using hh
  refine Finset.mem_image.mpr ⟨a.val.1 (Fin.last n),Finset.mem_filter.mpr ⟨?_,hCut,hRV⟩,hxValue⟩
  rw [R.mem_fibre,← hInit,← hOld,Fin.snoc_init_self]
  exact ha

end DiamondIntegral.Section6.CoordinateRootFamily
