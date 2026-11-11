import «section 2».AtomicDiscs
import Section3.GammaFullDescent

/-! Higher-dimensional atomic RV base change. Coordinate sections retain
every other VF coordinate as a named parameter. Scalar promotion removes
those temporary names before invoking original-base atomicity. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Name exactly the indicated finite tuple, retaining the Gamma base. -/
def tupleBase (B : ParameterBase M) {n : ℕ} (a : Fin n → M) : ParameterBase M :=
  ⟨B.real ∪ Set.range a, B.gamma⟩

omit [LRV.Structure M] hM in
private theorem unary_eta (z : Fin 1 → M) : (fun _ : Fin 1 => z 0) = z := by
  funext i
  fin_cases i
  rfl

omit [LRV.Structure M] hM in
private theorem rectangle_update {n : ℕ} (D : Fin n → Set M) {a : Fin n → M}
    (ha : ∀ j, a j ∈ D j) (i : Fin n) {x : M} (hx : x ∈ D i) :
    ∀ j, Function.update a i x j ∈ D j := by
  classical
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hx
  · simpa only [Function.update_of_ne hj] using ha j

private theorem coordinate_definable {B : ParameterBase M} {n : ℕ}
    (D : Fin n → Set M)
    (hA : IsAtomic B (fun _ : Fin n => .vf) {z | ∀ j, z j ∈ D j})
    (i : Fin n) : GammaParameters.DefinableAtBase B .vf (D i) := by
  classical
  obtain ⟨a, ha⟩ := hA.2.1
  have hp := hA.1.image_real (fun _ : Fin 1 => i)
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ D i}
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · intro hz
    refine ⟨Function.update a i (z 0), rectangle_update D ha i hz, ?_⟩
    funext k
    fin_cases k
    simp
  · rintro ⟨b, hb, he⟩
    have hi := hb i
    have he0 : b i = z 0 := congrFun he 0
    rwa [he0] at hi

/-- Restricting a definable tuple set to a coordinate line only names the
other coordinates. In particular the varying coordinate is never named. -/
theorem coordinate_section_definable (B : ParameterBase M) {n : ℕ}
    (i : Fin (n + 1)) (a : Fin n → M) (ha : ∀ j, iVF (a j))
    (C : Set (Fin (n + 1) → M))
    (hC : GammaParameters.DefinableOverBase B (fun _ => .vf) C) :
    GammaParameters.DefinableAtBase (tupleBase B a) .vf
      {x | Fin.insertNth i x a ∈ C} := by
  let E := tupleBase B a
  have hC' := hC.mono (show B.real ⊆ E.real from Set.subset_union_left)
    (Set.Subset.refl _)
  have ha' (j : Fin n) : GammaParameters.DefinableClosureAtBase E .vf (a j) :=
    GammaParameters.real_definableAtBase E .vf {a j}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self j)) (ha j))
  have hnames := (GammaParameters.tuple_singleton_definable_base E
    (fun _ : Fin n => .vf) a ha').preimage_real (fun _ : Fin (n + 1) => .vf) i.succAbove
  have hp := (hC'.inter hnames).image_real (fun _ : Fin 1 => i)
  change GammaParameters.DefinableOverBase E (fun _ : Fin 1 => .vf)
    {z | Fin.insertNth i (z 0) a ∈ C}
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · intro hz
    let w : Fin (n + 1) → M := Fin.insertNth i (z 0) a
    have hws : w ∈ GammaParameters.sortedUniverse (fun _ => .vf) :=
      fun j => hC.proper w hz j
    refine ⟨w, ⟨hz, ?_⟩, ?_⟩
    · exact ⟨by simp [w, Fin.insertNth_comp_succAbove], hws⟩
    · funext j
      fin_cases j
      simp [w]
  · rintro ⟨w, ⟨hwC, hwa, _⟩, he⟩
    have hwi : w i = z 0 := congrFun he 0
    have hwa' : Fin.removeNth i w = a := hwa
    have hw : Fin.insertNth i (z 0) a = w := by
      rw [← hwa', ← hwi, Fin.insertNth_self_removeNth]
    change Fin.insertNth i (z 0) a ∈ C
    rwa [hw]

/-- A coordinate line of an atomic rectangle is atomic over the other
coordinates. The varying coordinate is never named. -/
theorem coordinate_line_atomic {B : ParameterBase M} {n : ℕ}
    (D : Fin (n + 1) → Set M)
    (hA : IsAtomic B (fun _ => .vf) {z | ∀ j, z j ∈ D j})
    (a : Fin (n + 1) → M) (ha : ∀ j, a j ∈ D j) (i : Fin (n + 1)) :
    IsAtomic (tupleBase B (Fin.removeNth i a)) (fun _ : Fin 1 => .vf)
      {z | z 0 ∈ D i} := by
  classical
  let E := tupleBase B (Fin.removeNth i a)
  have hDi := coordinate_definable D hA i
  refine ⟨hDi.mono Set.subset_union_left (Set.Subset.refl _),
    ⟨fun _ => a i, ha i⟩, ?_, ?_⟩
  · intro z hz j
    fin_cases j
    exact hDi.proper (z 0) hz
  · intro C hC
    let C₀ : Set M := {x | (fun _ : Fin 1 => x) ∈ C}
    have hC₀ : GammaParameters.DefinableAtBase E .vf C₀ := by
      change GammaParameters.DefinableOverBase E (fun _ : Fin 1 => .vf)
        {z | (fun _ : Fin 1 => z 0) ∈ C}
      simpa only [unary_eta, Set.ofPred_mem_eq] using hC
    have hnames (j : Fin n) : iVF (Fin.removeNth i a j) :=
      hA.2.2.1 ha (i.succAbove j)
    obtain ⟨P, hP, hrow⟩ := GammaParameters.promote_scalar_definable_base B
      (fun _ : Fin n => .vf) (Fin.removeNth i a) hnames .vf C₀ hC₀
    have hst : Fin.lastCases SortTag.vf (fun _ : Fin n => .vf) =
        (fun _ : Fin (n + 1) => .vf) := by
      funext j
      exact Fin.lastCases (by simp) (fun _ => by simp) j
    rw [hst] at hP
    let π : Fin (n + 1) → Fin (n + 1) := Fin.lastCases i i.succAbove
    have hinit (z : Fin (n + 1) → M) :
        Fin.init (z ∘ π) = Fin.removeNth i z := by
      funext j
      simp [π, Fin.init, Fin.removeNth]
    have hlast (z : Fin (n + 1) → M) : (z ∘ π) (Fin.last n) = z i := by
      simp [π]
    let U : Set (Fin (n + 1) → M) :=
      {z | (Fin.removeNth i z, z i) ∈ P ∧
        z ∈ GammaParameters.sortedUniverse (fun _ => .vf)}
    have hU : GammaParameters.DefinableOverBase B (fun _ => .vf) U := by
      have hp := hP.preimage_real (fun _ : Fin (n + 1) => .vf) π
      convert hp using 1
      ext z
      change ((Fin.removeNth i z, z i) ∈ P ∧ _) ↔
        ((Fin.init (z ∘ π), (z ∘ π) (Fin.last n)) ∈ P ∧ _)
      rw [hinit, hlast]
    rcases hA.2.2.2 U hU with hsub | hdis
    · left
      intro z hz
      have hupdate := rectangle_update D ha i hz
      have hrel := (hsub hupdate).1
      simp only [Fin.removeNth_update, Function.update_self] at hrel
      have hc0 : z 0 ∈ C₀ := (Set.ext_iff.mp hrow (z 0)).mp hrel
      change (fun _ : Fin 1 => z 0) ∈ C at hc0
      rwa [unary_eta] at hc0
    · right
      apply Set.disjoint_left.mpr
      intro z hz hzC
      have hupdate := rectangle_update D ha i hz
      have hc0 : z 0 ∈ C₀ := by
        change (fun _ : Fin 1 => z 0) ∈ C
        rwa [unary_eta]
      have hrel := (Set.ext_iff.mp hrow (z 0)).mpr hc0
      change (Fin.removeNth i a, z 0) ∈ P at hrel
      have hUmem : Function.update a i (z 0) ∈ U := by
        refine ⟨?_, hA.2.2.1 hupdate⟩
        simpa only [Fin.removeNth_update, Function.update_self] using hrel
      exact Set.disjoint_left.mp hdis hupdate hUmem

private theorem coordinate_update_rv (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) {n : ℕ} (D : Fin (n + 1) → Set M)
    (hball : ∀ j, IsBall (D j)) (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {z | ∀ j, z j ∈ D j})
    (t : RVInfinity M) (C : Set (Fin (n + 1) → M))
    (hC : GammaParameters.DefinableOverBase (adjoinRV B t) (fun _ => .vf) C)
    (a : Fin (n + 1) → M) (ha : ∀ j, a j ∈ D j) (haC : a ∈ C)
    (i : Fin (n + 1)) (x : M) (hx : x ∈ D i) : Function.update a i x ∈ C := by
  classical
  have hnames (j : Fin n) : iVF (Fin.removeNth i a j) := hA.2.2.1 ha (i.succAbove j)
  have hline := lemma_2_24_unary h00 (tupleBase B (Fin.removeNth i a)) (D i)
    (hball i) (hinf i) (coordinate_line_atomic D hA a ha i) t
  have hsec := coordinate_section_definable (adjoinRV B t) i
    (Fin.removeNth i a) hnames C hC
  have hbase : tupleBase (adjoinRV B t) (Fin.removeNth i a) =
      adjoinRV (tupleBase B (Fin.removeNth i a)) t := by
    simp only [tupleBase, adjoinRV, Set.insert_union]
  rw [hbase] at hsec
  let L : Set (Fin 1 → M) := {z |
    (Fin.insertNth i (z 0) (Fin.removeNth i a) : Fin (n + 1) → M) ∈ C}
  have hL : GammaParameters.DefinableOverBase
      (adjoinRV (tupleBase B (Fin.removeNth i a)) t) (fun _ : Fin 1 => .vf) L := hsec
  rcases hline.2.2.2 L hL with hsub | hdis
  · have h := hsub (show (fun _ : Fin 1 => x) ∈ {z | z 0 ∈ D i} from hx)
    change Fin.insertNth i x (Fin.removeNth i a) ∈ C at h
    simpa only [Fin.insertNth_removeNth] using h
  · have haLine : (fun _ : Fin 1 => a i) ∈ {z | z 0 ∈ D i} := ha i
    have haSec : (fun _ : Fin 1 => a i) ∈
        {z : Fin 1 → M | Fin.insertNth i (z 0) (Fin.removeNth i a) ∈ C} := by
      change Fin.insertNth i (a i) (Fin.removeNth i a) ∈ C
      rwa [Fin.insertNth_self_removeNth]
    exact (Set.disjoint_left.mp hdis haLine haSec).elim

/-- Lemma 2.24 in every finite VF arity over the original real/Gamma
base. An atomic product of infinite valuative discs remains atomic after
adjoining any actual RV name. Coordinate sections name only the other VF
coordinates, and promotion proves their original-base atomicity internally.
No ground-value-group nontriviality or cited 2.23 input is assumed.
Additional DC ground names are outside this base interface. -/
theorem lemma_2_24 (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) {n : ℕ}
    (D : Fin n → Set M) (hball : ∀ j, IsBall (D j)) (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {z | ∀ j, z j ∈ D j}) (t : RVInfinity M) :
    IsAtomic (adjoinRV B t) (fun _ => .vf) {z | ∀ j, z j ∈ D j} := by
  classical
  refine ⟨hA.1.mono (Set.subset_insert _ _) (Set.Subset.refl _),
    hA.2.1, hA.2.2.1, ?_⟩
  intro C hC
  have hstep (a : Fin n → M) (ha : ∀ j, a j ∈ D j) (haC : a ∈ C)
      (i : Fin n) (x : M) (hx : x ∈ D i) : Function.update a i x ∈ C := by
    cases n with
    | zero => exact i.elim0
    | succ m => exact coordinate_update_rv h00 B D hball hinf hA t C hC a ha haC i x hx
  by_cases hne : ({z | ∀ j, z j ∈ D j} ∩ C).Nonempty
  · obtain ⟨a, ha, haC⟩ := hne
    left
    intro b hb
    let v (s : Finset (Fin n)) : Fin n → M := fun j => if j ∈ s then b j else a j
    have hvA (s : Finset (Fin n)) : ∀ j, v s j ∈ D j := by
      intro j
      by_cases hj : j ∈ s
      · simpa only [v, ite_eq_left hj] using hb j
      · simpa only [v, ite_eq_right hj] using ha j
    have hvC (s : Finset (Fin n)) : v s ∈ C := by
      induction s using Finset.induction_on with
      | empty => simpa only [v, Finset.notMem_empty, ite_false] using haC
      | @insert i s _hi ih =>
        have h := hstep (v s) (hvA s) ih i (b i) (hb i)
        have he : v (insert i s) = Function.update (v s) i (b i) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp [v]
          · simp [v, hj]
        rwa [he]
    simpa only [v, Finset.mem_univ, ite_true] using hvC Finset.univ
  · right
    exact Set.disjoint_left.mpr (fun z hz hzC => hne ⟨z, hz, hzC⟩)

/-- Finite tuples of RV names can be retained together. Each extension
uses the checked scalar theorem over the currently enlarged ground base. -/
theorem lemma_2_24_rv_tuple (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) {n m : ℕ}
    (D : Fin n → Set M) (hball : ∀ j, IsBall (D j)) (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {z | ∀ j, z j ∈ D j})
    (t : Fin m → RVInfinity M) :
    IsAtomic ⟨B.real ∪ Set.range (fun j => (t j).val), B.gamma⟩
      (fun _ => .vf) {z | ∀ j, z j ∈ D j} := by
  classical
  let E (s : Finset (Fin m)) : ParameterBase M :=
    ⟨B.real ∪ (fun j => (t j).val) '' (s : Set (Fin m)), B.gamma⟩
  have hE (s : Finset (Fin m)) : IsAtomic (E s) (fun _ => .vf) {z | ∀ j, z j ∈ D j} := by
    induction s using Finset.induction_on with
    | empty => simpa only [E, Finset.coe_empty, Set.image_empty, Set.union_empty] using hA
    | @insert i s _hi ih =>
      have h := lemma_2_24 h00 (E s) D hball hinf ih (t i)
      simpa only [E, adjoinRV, Finset.coe_insert, Set.image_insert_eq, Set.union_insert] using h
  simpa only [E, Finset.coe_univ, Set.image_univ] using hE Finset.univ

end DiamondIntegral.Section2
