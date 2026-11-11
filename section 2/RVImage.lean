import «section 2».AtomicImages

/-! Lemma 2.26 from the full VF graph of the manuscript's set-valued
function. The actual rv map is interpreted by a well-sorted formula;
existential image retains all RV-infinity tags, including rv(0). -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The actual rv equation, with all ambient coordinate sorts guarded. -/
theorem rv_eq_definable (B : ParameterBase M) {m : ℕ}
    (sn : Fin m → SortTag) (i j : Fin m) (hi : sn i = .vf) (hj : sn j = .rv) :
    GammaParameters.DefinableOverBase B sn
      {z | z ∈ GammaParameters.sortedUniverse sn ∧ iRv (z i) = z j} := by
  let p : Parameters B.real := ⟨0, Fin.elim0, (fun _ => .vf), (fun i => i.elim0), (fun i => i.elim0)⟩
  let t : LRV.Term (Fin 0 ⊕ Fin m) := .func Fn.rvMap ![.var (.inr i)]
  let φ : LRV.BoundedFormula (Fin 0) m := .equal t (.var (.inr j))
  have hti : TmSort p.sorts sn (.var (.inr i)) = some .vf := by
    change some (sn i) = some .vf
    rw [hi]
  have ht : TmSort p.sorts sn t = some .rv := by
    apply tmSort_func
    intro k
    fin_cases k
    exact hti
  have htj : TmSort p.sorts sn (.var (.inr j)) = some .rv := by
    change some (sn j) = some .rv
    rw [hj]
  have hw : WellSorted p.sorts sn φ := .equal _ ht htj
  have he (z : Fin m → M) : φ.Realize p.values z ↔ iRv (z i) = z j := by
    have htval : t.realize (Sum.elim p.values z) = iRv (z i) := by
      change Structure.funMap (L := LRV) Fn.rvMap
        (fun k : Fin 1 => (![Term.var (.inr i)] k : LRV.Term (Fin 0 ⊕ Fin m)).realize
          (Sum.elim p.values z)) = Structure.funMap (L := LRV) Fn.rvMap ![z i]
      congr 1
      funext k
      fin_cases k
      rfl
    change t.realize (Sum.elim p.values z) = z j ↔ iRv (z i) = z j
    rw [htval]
  apply GammaParameters.real_definableOverBase B sn
  refine ⟨p, φ, hw, ?_⟩
  ext z
  exact and_congr Iff.rfl (he z).symm

def vfRVImage {n : ℕ} (F : Set ((Fin n → M) × M)) : Set ((Fin n → M) × M) :=
  {p | ∃ y, (p.1, y) ∈ F ∧ iRv y = p.2}

/-- Existential image under the actual language map rv, with the complete
VF-input/RV-output graph definable over the original genuine Gamma base. -/
theorem vfRVImage_definable (B : ParameterBase M) {n : ℕ}
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) :
    GammaParameters.DefinableOverBase B (Fin.lastCases .rv (fun _ : Fin n => .vf))
      {z | (Fin.init z, z (Fin.last n)) ∈ vfRVImage F} := by
  let sn : Fin (n + 2) → SortTag := Fin.lastCases .rv (fun _ : Fin (n + 1) => .vf)
  let iy : Fin (n + 2) := (Fin.last n).castSucc
  let it : Fin (n + 2) := Fin.last (n + 1)
  have heq := rv_eq_definable B sn iy it (by simp [sn, iy]) (by simp [sn, it])
  have hF' := hF.preimage_real sn Fin.castSucc
  let π : Fin (n + 1) → Fin (n + 2) :=
    Fin.lastCases it (fun j : Fin n => j.castSucc.castSucc)
  have hp := (hF'.inter heq).image_real π
  have hst : sn ∘ π = Fin.lastCases .rv (fun _ : Fin n => .vf) := by
    funext j
    exact Fin.lastCases (by simp [sn, π, it]) (fun k => by simp [sn, π]) j
  rw [hst] at hp
  convert hp using 1
  ext z
  constructor
  · rintro ⟨y, hyF, hyt⟩
    change (Fin.init z, y) ∈ F at hyF
    change iRv y = z (Fin.last n) at hyt
    let w : Fin (n + 2) → M := Fin.snoc (Fin.snoc (Fin.init z) y) (z (Fin.last n))
    have hrow : (Fin.snoc (Fin.init z) y : Fin (n + 1) → M) ∈
        {z : Fin (n + 1) → M | (Fin.init z, z (Fin.last n)) ∈ F} := by
      simpa only [Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq] using hyF
    have hySort := hF.proper (Fin.snoc (Fin.init z) y) hrow (Fin.last n)
    have hyVF : iVF y := by simpa only [Fin.snoc_last, sortEval, iVF] using hySort
    have hytRV : iRV (z (Fin.last n)) := by
      rw [← hyt]
      exact (rv M (⟨y, hyVF⟩ : VF M)).property
    have hws : w ∈ GammaParameters.sortedUniverse sn := by
      intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [sn, w, Fin.lastCases_last, Fin.snoc_last, sortEval, iRV] using hytRV
      · simpa only [sn, w, Fin.lastCases_castSucc, Fin.snoc_castSucc] using hF.proper _ hrow k
    have hwF : w ∘ Fin.castSucc ∈ {z : Fin (n + 1) → M | (Fin.init z, z (Fin.last n)) ∈ F} := by
      change (Fin.init (Fin.init w), (Fin.init w) (Fin.last n)) ∈ F
      simpa only [w, Fin.init_snoc, Fin.snoc_last] using hyF
    have hwEq : iRv (w iy) = w it := by
      simpa only [w, iy, it, Fin.snoc_castSucc, Fin.snoc_last] using hyt
    refine ⟨w, ⟨⟨hwF, hws⟩, hws, hwEq⟩, ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [w, π, it]
    · simp [w, π, Fin.init]
  · rintro ⟨w, ⟨⟨hwF, _⟩, _, hwEq⟩, he⟩
    have hwa : Fin.init (w ∘ Fin.castSucc) = Fin.init z := by
      funext j
      have h := congrFun he j.castSucc
      simpa only [Function.comp_apply, π, Fin.lastCases_castSucc, Fin.init] using h
    have hwt : w it = z (Fin.last n) := by
      have h := congrFun he (Fin.last n)
      simpa only [Function.comp_apply, π, Fin.lastCases_last] using h
    refine ⟨w iy, ?_, hwEq.trans hwt⟩
    change (Fin.init (w ∘ Fin.castSucc), w iy) ∈ F at hwF
    rwa [hwa] at hwF

/-- Constancy of the complete rv image of any ground-definable VF relation
on an atomic polydisc. All absorbing-zero RV tags are retained. -/
theorem rv_image_constant_on_atomic_polydisc (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) {n : ℕ} (D : Fin n → Set M)
    (hball : ∀ j, IsBall (D j)) (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ a' ∈ {z | ∀ j, z j ∈ D j},
      iRv '' {y | (a, y) ∈ F} = iRv '' {y | (a', y) ∈ F} :=
  lemma_2_26_rv_relation h00 B D hball hinf hA (vfRVImage F) (vfRVImage_definable B F hF)

/-- Lemma 2.26 with the manuscript's finitary and fibrewise rv-injectivity
hypotheses retained. The image-constancy proof establishes a stronger result;
these extra hypotheses are used when extracting VF branches later. -/
theorem lemma_2_26 (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) {n : ℕ}
    (D : Fin n → Set M) (hball : ∀ j, IsBall (D j)) (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F})
    (_hfinite : ∀ a ∈ {z | ∀ j, z j ∈ D j}, {y | (a, y) ∈ F}.Finite)
    (_hrv : ∀ a ∈ {z | ∀ j, z j ∈ D j}, Set.InjOn iRv {y | (a, y) ∈ F}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ a' ∈ {z | ∀ j, z j ∈ D j},
      iRv '' {y | (a, y) ∈ F} = iRv '' {y | (a', y) ∈ F} :=
  rv_image_constant_on_atomic_polydisc h00 B D hball hinf hA F hF

end DiamondIntegral.Section2
