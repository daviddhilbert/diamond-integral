import «section 6».ShearContractionStages
import «section 6».SurjectiveMapDescent
import «section 6».TupleCoordinateMaps
import «section 6».VFTupleArithmeticMaps
import «section 6».MixedVFProjectionMaps

/-! Lemma 7.20, step 1: the fibres of a contraction stage with label-determined
displacement.

For a stage `T` of a standard contraction whose displacement in the last VF
coordinate depends only on the labels and the other coordinates
(`SameLabelShearDisplacement`), the displacement descends to a definable map
`offset T hD` on the contracted set. Over a point `b` of the contracted set, the
fibre of the stage in the last coordinate is the translate
`offset b + t^♯` of the RV-disc of the leading label `t` of `b`
(`contraction_eq_iff`, `exists_mem_fibre`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Stage
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (T : StandardContractionStage (G := G) A)

/-- The last VF coordinate of a point of `A`, as a map. -/
def lastSource : Map A (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfTupleSelectMap S (fun _ : Fin 1 => Fin.last n)).comp (mixedVFHeadMap A)

/-- The last VF coordinate of the lift, as a map. -/
def lastTarget : Map A (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfTupleSelectMap S (fun _ : Fin 1 => Fin.last n)).comp ((mixedVFHeadMap T.target).comp T.lift)

/-- The displacement `p_last - (lift p)_last`, as a map. -/
def diffMap : Map A (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfTupleBinaryMap S .sub).comp ((lastSource (A := A)).pair (lastTarget T)).toUniv

theorem diffMap_value (p : A) :
    (diffMap T p).val 0 = p.val.1 (Fin.last n) - (T.lift p).val.1 (Fin.last n) := rfl

/-- The labels of a point of `A` are recovered from its contraction. -/
theorem labels_of_contraction (p : A) (i : Fin r) :
    p.val.2 i = (T.contraction p).val.2 (T.oldLabels i) :=
  (T.retained p i).symm

theorem diffMap_compat (hD : SameLabelShearDisplacement T.lift (Fin.last n))
    (p q : A) (he : T.contraction p = T.contraction q) : diffMap T p = diffMap T q := by
  have hval : (Fin.init (T.lift p).val.1, (T.lift p).val.2) = (Fin.init (T.lift q).val.1, (T.lift q).val.2) := by
    rw [← T.contraction_value, ← T.contraction_value, he]
  have hInit : Fin.init (T.lift p).val.1 = Fin.init (T.lift q).val.1 := (Prod.mk.inj hval).1
  have hOut : (T.lift p).val.2 = (T.lift q).val.2 := (Prod.mk.inj hval).2
  have hIn : p.val.2 = q.val.2 := by
    funext i
    rw [labels_of_contraction T p i, labels_of_contraction T q i, he]
  have hOther : ∀ i, i ≠ Fin.last n → p.val.1 i = q.val.1 i := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    rw [← T.relative p j, ← T.relative q j]
    exact congrFun hInit j
  have h := hD p q hIn hOut hOther
  apply Subtype.ext
  funext k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  rw [diffMap_value, diffMap_value]
  have h' : -( (T.lift p).val.1 (Fin.last n) - p.val.1 (Fin.last n)) =
      -((T.lift q).val.1 (Fin.last n) - q.val.1 (Fin.last n)) := by rw [h]
  simpa only [neg_sub] using h'

/-- **The offset** of a stage with label-determined displacement: a definable map on
the contracted set with `offset (contraction p) = p_last - (lift p)_last`. -/
def offset (hD : SameLabelShearDisplacement T.lift (Fin.last n)) :
    Map T.contracted (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  descendSurjectiveMap T.contraction T.contraction_surjective (diffMap T) (diffMap_compat T hD)

theorem offset_contraction (hD : SameLabelShearDisplacement T.lift (Fin.last n)) (p : A) :
    (offset T hD (T.contraction p)).val 0 = p.val.1 (Fin.last n) - (T.lift p).val.1 (Fin.last n) := by
  rw [offset, descendSurjectiveMap_factor]
  rfl

/-- The scalar offset at a point of the contracted set. -/
def eps (hD : SameLabelShearDisplacement T.lift (Fin.last n)) (b : T.contracted) : VF M :=
  (offset T hD b).val 0

theorem lift_last (hD : SameLabelShearDisplacement T.lift (Fin.last n)) (p : A) :
    (T.lift p).val.1 (Fin.last n) = p.val.1 (Fin.last n) - eps T hD (T.contraction p) := by
  rw [eps, offset_contraction]
  ring

/-- **Fibres of a stage.** A point `p` of `A` lies over `b` exactly when its other VF
coordinates are those of `b`, its labels are recovered from `b`, and its last coordinate
lies in `eps b + t^♯`, where `t` is the leading label of `b`. -/
theorem contraction_eq_iff (hD : SameLabelShearDisplacement T.lift (Fin.last n))
    (p : A) (b : T.contracted) :
    T.contraction p = b ↔
      Fin.init p.val.1 = b.val.1 ∧ (∀ i, p.val.2 i = b.val.2 (T.oldLabels i)) ∧
        rv M (p.val.1 (Fin.last n) - eps T hD b) = b.val.2 T.leading := by
  constructor
  · rintro rfl
    refine ⟨(T.contraction_fixes_complement p).symm, labels_of_contraction T p, ?_⟩
    have hmem := (T.recover_target (T.lift p).val).mp (T.lift p).property
    rw [← lift_last T hD p]
    exact hmem.2
  · rintro ⟨hInit, hLab, hRV⟩
    let q : Mixed M (n+1) T.arity := (Fin.snoc b.val.1 (p.val.1 (Fin.last n) - eps T hD b), b.val.2)
    have hq : q ∈ T.target.carrier := by
      refine (T.recover_target q).mpr ⟨?_, ?_⟩
      · have hb : (Fin.init q.1, q.2) = b.val := by
          simp only [q, Fin.init_snoc]; rfl
        rw [hb]
        exact b.property
      · simp only [q, Fin.snoc_last]
        exact hRV
    obtain ⟨p', hp'⟩ := T.home.bijective.surjective ⟨q, hq⟩
    have hc : T.contraction p' = b := by
      apply Subtype.ext
      rw [T.contraction_value, hp']
      simp only [q, Fin.init_snoc]; rfl
    have hInit' : Fin.init p'.val.1 = b.val.1 := by
      rw [← hc]
      exact (T.contraction_fixes_complement p').symm
    have hLast' : p'.val.1 (Fin.last n) = p.val.1 (Fin.last n) := by
      have h1 := lift_last T hD p'
      rw [hp', hc] at h1
      simp only [q, Fin.snoc_last] at h1
      exact (sub_left_inj.mp h1).symm
    have hpp : p' = p := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact hLast'
        · have h1 := congrFun hInit' j
          have h2 := congrFun hInit j
          simp only [Fin.init] at h1 h2
          rw [h1, h2]
      · funext i
        rw [labels_of_contraction T p' i, hc, hLab i]
    rw [← hpp]
    exact hc

/-- Every point of the translated disc over `b` is realized in `A`. -/
theorem exists_mem_fibre (hD : SameLabelShearDisplacement T.lift (Fin.last n))
    (b : T.contracted) (y : VF M) (hy : rv M (y - eps T hD b) = b.val.2 T.leading) :
    ∃ p : A, T.contraction p = b ∧ p.val.1 (Fin.last n) = y := by
  let q : Mixed M (n+1) T.arity := (Fin.snoc b.val.1 (y - eps T hD b), b.val.2)
  have hq : q ∈ T.target.carrier := by
    refine (T.recover_target q).mpr ⟨?_, ?_⟩
    · have hb : (Fin.init q.1, q.2) = b.val := by
        simp only [q, Fin.init_snoc]; rfl
      rw [hb]
      exact b.property
    · simp only [q, Fin.snoc_last]
      exact hy
  obtain ⟨p, hp⟩ := T.home.bijective.surjective ⟨q, hq⟩
  have hc : T.contraction p = b := by
    apply Subtype.ext
    rw [T.contraction_value, hp]
    simp only [q, Fin.init_snoc]; rfl
  refine ⟨p, hc, ?_⟩
  have h1 := lift_last T hD p
  rw [hp, hc] at h1
  simp only [q, Fin.snoc_last] at h1
  exact (sub_left_inj.mp h1).symm

end Stage

end DiamondIntegral.Section7.Lemma720
