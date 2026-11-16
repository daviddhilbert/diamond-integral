import «section 6».CentripetalPullbackPreservation

/-! Actual last-coordinate step fibers, retained parent tags and the
exact noncore inverse. Restriction membership is transported through
that inverse, with no assumption that the focus is globally constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def coordinateStepOldTags (u : Fin ((n+1)+(1+r)) → RVInfinity M) : Fin r → RVInfinity M :=
  fun i => u (Fin.natAdd (n+1) (Fin.natAdd 1 i))

theorem mem_centripetalStep_target (D : CentripetalData (G := G) A)
    (q : Mixed M (n+1) ((n+1)+(1+r))) :
    q ∈ (regularizeMap D.map.image).image.carrier ↔ ∃ a, a ∈ A.carrier ∧ regularize (D.point a) = q := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨a,ha⟩ := z.property
    exact ⟨a.val,a.property,(congrArg regularize ha).trans hz⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨D.bijection ⟨a,ha⟩,he⟩

theorem centripetalStepMap_surjective (D : CentripetalData (G := G) A) :
    Function.Surjective (centripetalStepMap D) := by
  intro q
  obtain ⟨a,ha,he⟩ := (mem_centripetalStep_target D q.val).mp q.property
  exact ⟨⟨a,ha⟩,Subtype.ext he⟩

namespace CentripetalData

def lastTagFocus (D : CentripetalData (G := G) A) (b : Fin n → VF M) (u : Fin r → RVInfinity M) : VF M :=
  if u ∈ D.activeTags.carrier then D.focus (Fin.snoc b 0) u else 0

theorem extendedFocus_last (D : CentripetalData (G := G) A) (hj : D.coordinate = Fin.last n)
    (a : Mixed M (n+1) r) (ha : a ∈ A.carrier) :
    D.extendedFocus a = D.lastTagFocus (Fin.init a.1) a.2 := by
  by_cases hu : a.2 ∈ D.activeTags.carrier
  · rw [D.extendedFocus_active ha hu,lastTagFocus,if_pos hu]
    congr 1
    rw [hj]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.update_self,Fin.snoc_last]
    · simp only [Function.update_of_ne (Fin.castSucc_ne_last j),Fin.snoc_castSucc,Fin.init]
  · rw [D.extendedFocus_inactive hu,lastTagFocus,if_neg hu]

theorem noncore_input_last (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate = Fin.last n) (q : Mixed M (n+1) ((n+1)+(1+r)))
    (hq : q ∈ (regularizeMap D.map.image).image.carrier)
    (hflag : q.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    ∃ p : A, regularize (D.point p.val) = q ∧ D.core p.val = false ∧
      p.val = (Fin.snoc (Fin.init q.1)
        (q.1 (Fin.last n)+D.lastTagFocus (Fin.init q.1) (coordinateStepOldTags q.2)),coordinateStepOldTags q.2) := by
  obtain ⟨a,ha,he⟩ := (mem_centripetalStep_target D q).mp hq
  have hOld : a.2 = coordinateStepOldTags q.2 := by
    funext i
    have hh := congrArg (fun p : Mixed M (n+1) ((n+1)+(1+r)) =>
      p.2 (Fin.natAdd (n+1) (Fin.natAdd 1 i))) he
    simpa only [regularize,point,Fin.append_right,coordinateStepOldTags] using hh
  have hInit : Fin.init a.1 = Fin.init q.1 := by
    funext i
    have hh := congrArg (fun p : Mixed M (n+1) ((n+1)+(1+r)) => p.1 i.castSucc) he
    simpa only [regularize,point,hj,Function.update_of_ne (Fin.castSucc_ne_last i),Fin.init] using hh
  have hCore : D.core a = false := by
    have hh := congrArg (fun p : Mixed M (n+1) ((n+1)+(1+r)) =>
      p.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1)))) he
    rw [D.regularized_core_flag] at hh
    exact branchTag_injective h00 (hh.trans hflag)
  have hFocus : D.extendedFocus a = D.lastTagFocus (Fin.init q.1) (coordinateStepOldTags q.2) := by
    rw [D.extendedFocus_last hj a ha,hInit,hOld]
  have hLast : a.1 (Fin.last n) = q.1 (Fin.last n)+D.lastTagFocus (Fin.init q.1) (coordinateStepOldTags q.2) := by
    have hh := congrArg (fun p : Mixed M (n+1) ((n+1)+(1+r)) => p.1 (Fin.last n)) he
    simp only [regularize,point,hj,Function.update_self,hCore,Bool.false_eq_true,ite_false,add_zero,hFocus] at hh
    exact (sub_add_cancel (a.1 (Fin.last n)) _).symm.trans (congrArg (fun x => x+_) hh)
  refine ⟨⟨a,ha⟩,he,hCore,?_⟩
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hLast
    · simpa only [Fin.snoc_castSucc,Fin.init] using congrFun hInit j
  · exact hOld

theorem noncore_restricted_image_mem_iff
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (P : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hPA : P.carrier ⊆ A.carrier)
    (q : Mixed M (n+1) ((n+1)+(1+r))) (hq : q ∈ (regularizeMap D.map.image).image.carrier)
    (hflag : q.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    q ∈ ((centripetalStepMap D).restrict hPA).image.carrier ↔
      (Fin.snoc (Fin.init q.1) (q.1 (Fin.last n)+D.lastTagFocus (Fin.init q.1) (coordinateStepOldTags q.2)),
        coordinateStepOldTags q.2) ∈ P.carrier := by
  obtain ⟨a,he,hCore,hPoint⟩ := D.noncore_input_last h00 hj q hq hflag
  rw [← hPoint]
  constructor
  · rintro ⟨p,hp⟩
    have heq : a.val = p.val := D.point_injective_on h00 a.property (hPA p.property)
      (regularize_injective (he.trans hp.symm))
    exact heq.symm ▸ p.property
  · intro ha
    exact ⟨⟨a.val,ha⟩,he⟩

end CentripetalData
end DiamondIntegral.Section6
