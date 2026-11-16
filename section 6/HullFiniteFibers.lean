import «section 6».InvariantHull
import Section3.GammaDensity

/-! R170 in the actual VF/RV sorts. A graph has singleton RV fibers,
whereas its RV-hull complement has an infinite fiber. The interval
parameter has the paper's order; multiplicative 1 denotes additive 0. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def r170Support (δ : Gamma M) : Set (RVInfinity M) :=
  {t | (1 : GammaInfinity M) < Values.vrv t ∧ Values.vrv t < δ.val}

def r170Graph (δ : Gamma M) : Set (Mixed M 1 1) :=
  {p | rv M (p.1 0) = rv M 1 ∧ p.2 0 ∈ r170Support δ ∧
    p.2 0 = rv M (p.1 0 - 1)}

theorem r170Support_infinite (δ : Gamma M) (hδ : 1 < δ) :
    (r170Support δ).Infinite := by
  have hI : (Set.Ioo (1 : Gamma M) δ).Infinite := Set.Ioo_infinite hδ
  have him : (Subtype.val '' Set.Ioo (1 : Gamma M) δ).Infinite :=
    hI.image Subtype.val_injective.injOn
  have hsub : Subtype.val '' Set.Ioo (1 : Gamma M) δ ⊆
      Values.vrv '' r170Support δ := by
    rintro _ ⟨γ,hγ,rfl⟩
    obtain ⟨t,ht⟩ := Values.vrv_surjective γ.val
    refine ⟨t,?_,ht⟩
    change (1 : GammaInfinity M) < Values.vrv t ∧ Values.vrv t < δ.val
    rw [ht]
    exact hγ
  intro hfin
  exact him ((hfin.image Values.vrv).subset hsub)

theorem r170Support_nonzero {δ : Gamma M} {t : RVInfinity M}
    (ht : t ∈ r170Support δ) : t ≠ rvZero M := by
  intro he
  have hi := ht.2
  rw [he] at hi
  change Values.infinity < δ.val at hi
  exact hi.not_ge (Values.le_infinity _)

theorem r170Graph_finite_rv_fibers (δ : Gamma M) (x : Fin 1 → VF M) :
    {t : Fin 1 → RVInfinity M | (x,t) ∈ r170Graph δ}.Finite := by
  apply Set.Subsingleton.finite
  intro t ht s hs
  funext i
  fin_cases i
  exact ht.2.2.trans hs.2.2.symm

theorem r170Graph_properInvariantGeometry (δ : Gamma M) (hδ : 1 < δ) :
    ProperInvariantGeometry (r170Graph δ) := by
  have value_one : vfValue (1 : VF M) = 1 := Values.vf_value_one
  have value_x (p : Mixed M 1 1) (hp : p ∈ r170Graph δ) : vfValue (p.1 0) = 1 :=
    (congrArg Values.vrv hp.1).trans value_one
  refine ⟨?_,?_,fun t => ⟨fun _ => δ,?_⟩⟩
  · refine ⟨1,fun p hp i => ?_⟩
    fin_cases i
    change (1 : GammaInfinity M) ≤ vfValue (p.1 0)
    exact (value_x p hp).ge
  · refine ⟨δ,fun p hp i => ?_⟩
    fin_cases i
    have hlow : (δ⁻¹).val ≤ (1 : GammaInfinity M) :=
      show (δ⁻¹).val ≤ (1 : Gamma M).val from inv_le_one'.mpr hδ.le
    exact ⟨hlow.trans hp.2.1.1.le,hp.2.1.2.le⟩
  · have step (x y : Fin 1 → VF M) (hxy : Congruent (fun _ => δ) x y)
        (hx : (x,t) ∈ r170Graph δ) : (y,t) ∈ r170Graph δ := by
      have hnear : δ.val < vfValue (y 0 - x 0) := hxy.symm 0
      have hvx : vfValue (x 0) = 1 := value_x (x,t) hx
      have hryx : rv M (y 0) = rv M (x 0) :=
        rv_eq_of_close_at_radius δ (by rw [hvx]; exact hδ.le) hnear
      have hxminus : vfValue (x 0 - 1) < δ.val := by
        calc
          vfValue (x 0 - 1) = Values.vrv (t 0) := (congrArg Values.vrv hx.2.2).symm
          _ < δ.val := hx.2.1.2
      have hrminus : rv M (y 0 - 1) = rv M (x 0 - 1) := by
        apply rv_eq_of_close_at_radius δ hxminus.le
        rwa [show y 0 - 1 - (x 0 - 1) = y 0 - x 0 by abel]
      exact ⟨hryx.trans hx.1,hx.2.1,hx.2.2.trans hrminus.symm⟩
    intro x y hxy
    exact ⟨step x y hxy,step y x hxy.symm⟩

theorem r170_hull (δ : Gamma M) :
    rvHull (r170Graph δ) =
      {p : Mixed M 1 1 | rv M (p.1 0) = rv M 1 ∧ p.2 0 ∈ r170Support δ} := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,hrv,ht⟩ := (mem_rvHull_iff _ p).mp hp
    refine ⟨(congrFun hrv 0).symm.trans hq.1,?_⟩
    rw [← ht]
    exact hq.2.1
  · rintro ⟨hp,hU⟩
    obtain ⟨z,hz⟩ := rv_surjective (p.2 0)
    have hr : rv M (1 + z) = rv M 1 := by
      apply rv_eq_of_value_close one_ne_zero
      rw [show (1 : VF M) + z - 1 = z by abel]
      have hvz : vfValue z = Values.vrv (p.2 0) := congrArg Values.vrv hz
      rw [hvz]
      have hv1 : vfValue (1 : VF M) = 1 := Values.vf_value_one
      rw [hv1]
      exact hU.1
    let q : Mixed M 1 1 := (fun _ => 1 + z,p.2)
    refine (mem_rvHull_iff _ p).mpr ⟨q,?_,?_,rfl⟩
    · refine ⟨hr,hU,?_⟩
      change p.2 0 = rv M (1 + z - 1)
      rw [show (1 : VF M) + z - 1 = z by abel]
      exact hz.symm
    · funext i
      fin_cases i
      exact hr.trans hp.symm

theorem r170_complement_fiber_infinite (δ : Gamma M) (hδ : 1 < δ) :
    {t : Fin 1 → RVInfinity M |
      ((fun _ => (1 : VF M)),t) ∈ rvHull (r170Graph δ) \ r170Graph δ}.Infinite := by
  let embed (t : RVInfinity M) : Fin 1 → RVInfinity M := fun _ => t
  have hinj : Function.Injective embed := fun t s he => congrFun he 0
  have hsub : embed '' r170Support δ ⊆
      {t : Fin 1 → RVInfinity M |
        ((fun _ => (1 : VF M)),t) ∈ rvHull (r170Graph δ) \ r170Graph δ} := by
    rintro _ ⟨t,ht,rfl⟩
    refine ⟨?_,?_⟩
    · rw [r170_hull]
      exact ⟨rfl,ht⟩
    · intro hgraph
      apply r170Support_nonzero ht
      have he : t = rv M ((1 : VF M) - 1) := hgraph.2.2
      simpa only [sub_self,rv_zero] using he
  exact ((r170Support_infinite δ hδ).image hinj.injOn).mono hsub

end DiamondIntegral.Section6
