import «section 2».Conventions
import Section3.MeanInBalls
import Section3.ValuedNeighbourhood
import ValuedFieldExtension

set_option backward.isDefEq.respectTransparency false

/-!
# §2.1, `rvfiber`, R023: graph-fibre continuity and composition

The graph convention fixes BOTH input and output RV tags before testing
continuity. A map into RV therefore has constant (empty) VF output on
each such fibre. Intermediate labels must be retained during composition.

The counterexample below uses the actual tags `rv(1)` and `rv(-1)` in an
ACVF(0,0) model. Its discontinuity after forgetting the intermediate label
uses the valuation topology. The author confirmed that composition in the
manuscript retains these labels; `labelledComp` proves that convention,
without strengthening continuity or changing the topology on RV.
-/

noncomputable section

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

/-- The manuscript tests the VF part on graph fibres with both tags fixed. -/
def GraphFibreContinuous {X Y I J : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X × I → Y × J) : Prop :=
  ∀ i j, ContinuousOn (fun x => (f (x, i)).1) {x | (f (x, i)).2 = j}

/-- Compose while recording the intermediate RV tag together with the output tag. -/
def labelledComp {X Y Z I J K : Type*} (f : X × I → Y × J) (g : Y × J → Z × K)
    (p : X × I) : Z × (J × K) :=
  ((g (f p)).1, ((f p).2, (g (f p)).2))

/-- After fixing input, intermediate and output tags, ordinary continuous
VF maps compose on the preimage of the next branch's domain. -/
theorem GraphFibreContinuous.labelledComp {X Y Z I J K : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X × I → Y × J} {g : Y × J → Z × K}
    (hf : GraphFibreContinuous f) (hg : GraphFibreContinuous g) :
    GraphFibreContinuous (labelledComp f g) := by
  intro i ⟨j,k⟩
  let D : Set X := {x | ((f (x,i)).2, (g (f (x,i))).2) = (j,k)}
  have hpair (x : X) (hx : x ∈ D) : f (x,i) = ((f (x,i)).1,j) :=
    Prod.ext rfl (congrArg Prod.fst hx)
  have hF : ContinuousOn (fun x => (f (x,i)).1) D :=
    (hf i j).mono (fun x hx => congrArg Prod.fst hx)
  have hmaps : Set.MapsTo (fun x => (f (x,i)).1) D {y | (g (y,j)).2 = k} := by
    intro x hx
    change (g ((f (x,i)).1,j)).2 = k
    rw [← hpair x hx]
    exact congrArg Prod.snd hx
  have hcomp := (hg j k).comp hF hmaps
  change ContinuousOn (fun x => (g (f (x,i))).1) D
  exact hcomp.congr (fun x hx => by rw [hpair x hx]; rfl)

@[simp] theorem labelledComp_forget {X Y Z I J K : Type*}
    (f : X × I → Y × J) (g : Y × J → Z × K) (p : X × I) :
    ((labelledComp f g p).1, (labelledComp f g p).2.2) = (g ∘ f) p := rfl

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def r023_f (p : VF M × Unit) : Unit × RVInfinity M :=
  ((), if p.1 = 0 then rv M 1 else rv M (-1))

/-- This total extension agrees with the manuscript's g on its two-point domain. -/
def r023_g (p : Unit × RVInfinity M) : VF M × Unit :=
  (if p.2 = rv M 1 then 0 else 1, ())

theorem r023_distinct_tags (h00 : M ⊨ Axioms.ACVF00)
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (VF M) Γ₀)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) :
    rv M (1 : VF M) ≠ rv M (-1 : VF M) := by
  intro he
  have hq := (CanonicalRV.same_fibers v hv (1 : VF M) (-1)).mpr he
  have hlt := (_root_.RVCalc.rv_eq_iff (show (1 : VF M) ≠ 0 from one_ne_zero)
    (neg_ne_zero.mpr (show (1 : VF M) ≠ 0 from one_ne_zero))).mp hq
  have htwo : v (2 : VF M) = 1 := Barycentre.natCast_value_one v hv h00 2 (by decide)
  have hsub : (1 : VF M) - -1 = 2 := by ring
  simpa only [hsub, htwo, Valuation.map_one, lt_self_iff_false] using hlt

theorem r023_composite (hne : rv M (1 : VF M) ≠ rv M (-1 : VF M)) (p : VF M × Unit) :
    (r023_g ∘ r023_f) p = (if p.1 = 0 then 0 else 1, ()) := by
  by_cases hp : p.1 = 0 <;> simp [r023_f, r023_g, Function.comp_def, hp, hne.symm]

theorem r023_f_graphFibreContinuous [TopologicalSpace (VF M)] :
    GraphFibreContinuous (r023_f (M := M)) := by
  intro i j
  exact continuousOn_const

theorem r023_g_graphFibreContinuous [TopologicalSpace (VF M)] :
    GraphFibreContinuous (r023_g (M := M)) := by
  intro i j
  change ContinuousOn (fun _ : Unit => if i = rv M 1 then (0 : VF M) else 1) {u : Unit | () = j}
  exact continuousOn_const

/-- R023's example is continuous under the author's retained-label convention. -/
theorem r023_labelled_composite_continuous [TopologicalSpace (VF M)] :
    GraphFibreContinuous (labelledComp (r023_f (M := M)) r023_g) :=
  r023_f_graphFibreContinuous.labelledComp r023_g_graphFibreContinuous

private theorem jump_not_continuousAt_zero {K Γ₀ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hnt : ∃ ε : K, ε ≠ 0 ∧ Valued.v ε < 1) :
    ¬ ContinuousAt (fun x : K => if x = 0 then (0 : K) else 1) 0 := by
  intro hc
  have hn : {y : K | y ≠ 1} ∈ 𝓝 (0 : K) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simp)
  have hp := hc.preimage_mem_nhds (by simpa using hn)
  have he : (fun x : K => if x = 0 then (0 : K) else 1) ⁻¹' {y | y ≠ 1} = {0} := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  rw [he] at hp
  exact (infinite_valued_neighbourhood hnt 0 hp) (Set.finite_singleton 0)

/-- Forgetting the intermediate label can destroy graph-fibre continuity.
The topology is constructed from the supplied compatible valuation, and
nontriviality and distinctness of the tags are proved from the model axioms. -/
theorem forgetting_intermediate_tags_counterexample (h00 : M ⊨ Axioms.ACVF00)
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (VF M) Γ₀)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) :
    letI : Valued (VF M) Γ₀ := Valued.mk' v
    GraphFibreContinuous (r023_f (M := M)) ∧
      GraphFibreContinuous (r023_g (M := M)) ∧
      ¬ GraphFibreContinuous (r023_g ∘ r023_f (M := M)) := by
  letI : Valued (VF M) Γ₀ := Valued.mk' v
  refine ⟨r023_f_graphFibreContinuous, r023_g_graphFibreContinuous, ?_⟩
  intro hc
  have hne := r023_distinct_tags h00 v hv
  have hcont : Continuous (fun x : VF M => if x = 0 then (0 : VF M) else 1) := by
    apply continuousOn_univ.mp
    simpa only [r023_composite hne, Set.ofPred_true] using hc () ()
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have hεv : v ε < 1 := by
    have hh := (not_congr (hv 1 ε)).mp hε
    simpa only [Valuation.map_one, not_le] using hh
  exact jump_not_continuousAt_zero ⟨ε, hε0, hεv⟩ hcont.continuousAt

end DiamondIntegral.Section2
