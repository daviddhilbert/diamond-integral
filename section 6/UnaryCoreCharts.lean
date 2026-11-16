import «section 6».UnaryRelativeStepMaps
import «section 6».UnaryFocusPointMaps

/-! Exact affine charts on whole original unary cores. A chart gives
surjectivity onto the entire current disc, and composes with an actual
variable step whenever its retained branch is constant. This supplies
core transport independently of ordinary-prefix commutation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def unaryTaggedDisc (p : Mixed M 1 r) (γ : Gamma M) : Set (Mixed M 1 r) :=
  {a | a.2=p.2 ∧ γ.val<vfValue (a.1 0-p.1 0)}

structure UnaryCoreChart (f : Map A B) (p : A) (γ : Gamma M) : Prop where
  field : ∀ a : A,a.val.2=p.val.2 → γ.val<vfValue (a.val.1 0-p.val.1 0) →
    (f a).val.1 0=a.val.1 0-p.val.1 0+(f p).val.1 0
  tags : ∀ a : A,a.val.2=p.val.2 → γ.val<vfValue (a.val.1 0-p.val.1 0) →
    (f a).val.2=(f p).val.2

namespace UnaryCoreChart
variable {f : Map A B} {p : A} {γ : Gamma M}

theorem source_disc_subset (hA : IsRVPullback A.carrier) (hp : p.val.1 0≠0)
    (hγ : vfValue (p.val.1 0) ≤ γ.val) : unaryTaggedDisc p.val γ ⊆ A.carrier := by
  rintro a ⟨hTags,hClose⟩
  have hRV := (rv_eq_iff_value_close hp).mpr (hγ.trans_lt hClose)
  apply rvPullback_mem_of_sameRV (q := a) hA p.property _ hTags.symm
  funext i
  fin_cases i
  exact hRV.symm

def image (C : UnaryCoreChart f p γ) : Set (Mixed M 1 s) :=
  {q | ∃ a : A,a.val ∈ unaryTaggedDisc p.val γ ∧ (f a).val=q}

theorem image_exact (C : UnaryCoreChart f p γ) (hA : IsRVPullback A.carrier)
    (hp : p.val.1 0≠0) (hγ : vfValue (p.val.1 0) ≤ γ.val) :
    C.image=unaryTaggedDisc (f p).val γ := by
  ext q
  constructor
  · rintro ⟨a,⟨hTags,hClose⟩,rfl⟩
    refine ⟨C.tags a hTags hClose,?_⟩
    rw [C.field a hTags hClose,add_sub_cancel_right]
    exact hClose
  · rintro ⟨hTags,hClose⟩
    let x : Mixed M 1 r := ((fun _ => q.1 0-(f p).val.1 0+p.val.1 0),p.val.2)
    have hx : x ∈ unaryTaggedDisc p.val γ := by
      refine ⟨rfl,?_⟩
      simpa only [x,add_sub_cancel_right] using hClose
    have hxA := source_disc_subset hA hp hγ hx
    let a : A := ⟨x,hxA⟩
    refine ⟨a,hx,Prod.ext ?_ ?_⟩
    · funext i
      fin_cases i
      have h := C.field a hx.1 hx.2
      change (f a).val.1 0=q.1 0
      rw [h]
      change q.1 0-(f p).val.1 0+p.val.1 0-p.val.1 0+(f p).val.1 0=q.1 0
      abel
    · exact (C.tags a hx.1 hx.2).trans hTags.symm

theorem image_rvPullback (C : UnaryCoreChart f p γ) (hA : IsRVPullback A.carrier)
    (hp : p.val.1 0≠0) (hγ : vfValue (p.val.1 0) ≤ γ.val)
    (hImageNZ : (f p).val.1 0≠0) (hValue : vfValue ((f p).val.1 0)=γ.val) :
    IsRVPullback C.image := by
  rw [C.image_exact hA hp hγ]
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨z,⟨hTags,hClose⟩,hVF,hRV⟩ := (mem_rvHull_iff (unaryTaggedDisc (f p).val γ) q).mp hq
  refine ⟨hRV.symm.trans hTags,?_⟩
  have hzRV : rv M (z.1 0)=rv M ((f p).val.1 0) :=
    (rv_eq_iff_value_close hImageNZ).mpr (hValue ▸ hClose)
  have hqRV : rv M (q.1 0)=rv M ((f p).val.1 0) := (congrFun hVF 0).symm.trans hzRV
  exact hValue ▸ (rv_eq_iff_value_close hImageNZ).mp hqRV

theorem identity (p : A) (γ : Gamma M) : UnaryCoreChart (Map.id A) p γ where
  field a hTags hClose := (sub_add_cancel _ _).symm
  tags a hTags hClose := hTags

theorem afterRelativeStep (C : UnaryCoreChart f p γ) (D : UnaryRelativeApertureData B)
    (hCore : ∀ a : A,a.val ∈ unaryTaggedDisc p.val γ → D.core (f a).val=D.core (f p).val)
    (hBound : vfValue ((D.point (f p).val).1 0) ≤ γ.val) :
    UnaryCoreChart (D.stepMap.comp f) p γ := by
  have hDiff (a : A) (ha : a.val ∈ unaryTaggedDisc p.val γ) :
      (D.point (f a).val).1 0-(D.point (f p).val).1 0=a.val.1 0-p.val.1 0 := by
    have h := D.branch_translation (f a).property (f p).property (C.tags a ha.1 ha.2) (hCore a ha)
    rw [C.field a ha.1 ha.2,add_sub_cancel_right] at h
    exact h
  have hNZ : (D.point (f p).val).1 0≠0 := by
    intro hz
    have h := hBound
    rw [hz,value_zero] at h
    exact γ.property (le_antisymm (Values.le_infinity _) h)
  refine ⟨?_,?_⟩
  · intro a hTags hClose
    have h := hDiff a ⟨hTags,hClose⟩
    change (D.point (f a).val).1 0=a.val.1 0-p.val.1 0+(D.point (f p).val).1 0
    linear_combination h
  · intro a hTags hClose
    have hCore' := hCore a ⟨hTags,hClose⟩
    have hOldTags := C.tags a hTags hClose
    have hRV : rv M ((D.point (f a).val).1 0)=rv M ((D.point (f p).val).1 0) := by
      apply (rv_eq_iff_value_close hNZ).mpr
      rw [hDiff a ⟨hTags,hClose⟩]
      exact hBound.trans_lt hClose
    change Fin.append (tupleRV M (D.point (f a).val).1) (D.point (f a).val).2=
      Fin.append (tupleRV M (D.point (f p).val).1) (D.point (f p).val).2
    have hVF : tupleRV M (D.point (f a).val).1=tupleRV M (D.point (f p).val).1 := by
      funext i
      fin_cases i
      exact hRV
    rw [hVF]
    congr 1
    simp only [UnaryRelativeApertureData.point,hCore',hOldTags]

end UnaryCoreChart
end DiamondIntegral.Section6
