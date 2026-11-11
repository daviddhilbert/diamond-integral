import «section 2».AtomicDiscGroundChange
import «section 2».RVImage

/-! Full RV-image graphs and fixed RV rows over retained finite DC names.
All absorbing-zero tags and the original parameter base are preserved. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfRVImage_definable_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F}) :
    DefinableOverFiniteDiscNames B ground d τ (Fin.lastCases .rv (fun _ : Fin n => .vf))
      {z | (Fin.init z, z (Fin.last n)) ∈ vfRVImage F} := by
  have hproper (z : Fin (n+1) → M) (hz : (Fin.init z,z (Fin.last n)) ∈ F) := hF.proper hz
  let sn : Fin (n + 2) → SortTag := Fin.lastCases .rv (fun _ : Fin (n + 1) => .vf)
  let iy : Fin (n + 2) := (Fin.last n).castSucc
  let it : Fin (n + 2) := Fin.last (n + 1)
  have heq := definableOverFiniteDiscNames_of_ground B ground d τ sn _
    (rv_eq_definable B sn iy it (by simp [sn, iy]) (by simp [sn, it]))
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
    have hySort := hproper (Fin.snoc (Fin.init z) y) hrow (Fin.last n)
    have hyVF : iVF y := by simpa only [Fin.snoc_last, sortEval, iVF] using hySort
    have hytRV : iRV (z (Fin.last n)) := by
      rw [← hyt]
      exact (rv M (⟨y, hyVF⟩ : VF M)).property
    have hws : w ∈ GammaParameters.sortedUniverse sn := by
      intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [sn, w, Fin.lastCases_last, Fin.snoc_last, sortEval, iRV] using hytRV
      · simpa only [sn, w, Fin.lastCases_castSucc, Fin.snoc_castSucc] using hproper _ hrow k
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

theorem rv_row_definable_disc_names (B : ParameterBase M) {k n : ℕ}
    (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (R : Set ((Fin n → M) × M))
    (hR : DefinableOverFiniteDiscNames B ground d τ
      (Fin.lastCases .rv (fun _ : Fin n => .vf))
      {z | (Fin.init z, z (Fin.last n)) ∈ R}) (t : RVInfinity M) :
    DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin n => .vf)
      {a | (a, t.val) ∈ R} := by
  let E := adjoinRV B t
  let sn : Fin (n + 1) → SortTag := Fin.lastCases .rv (fun _ => .vf)
  have hR' : DefinableOverFiniteDiscNames E ground d τ sn
      {z | (Fin.init z, z (Fin.last n)) ∈ R} :=
    hR.mono (show B.real ⊆ E.real from Set.subset_insert _ _) (Set.Subset.refl _)
  have ht : GammaParameters.DefinableClosureAtBase E .rv t.val :=
    GammaParameters.real_definableAtBase E .rv {t.val}
      (definableClosureAt_of_mem (Set.mem_insert _ _) t.property)
  have hname := definableOverFiniteDiscNames_of_ground E ground d τ sn _
    (ht.preimage_real sn (fun _ : Fin 1 => Fin.last n))
  have hp := (hR'.inter hname).image_real Fin.castSucc
  have hst : sn ∘ Fin.castSucc = (fun _ : Fin n => .vf) := by
    funext j
    simp only [sn, Function.comp_apply, Fin.lastCases_castSucc]
  rw [hst] at hp
  convert hp using 1
  ext a
  constructor
  · intro ha
    let w : Fin (n + 1) → M := Fin.snoc a t.val
    have hwR : (Fin.init w, w (Fin.last n)) ∈ R := by
      simpa only [w, Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq] using ha
    have hws := hR'.proper hwR
    refine ⟨w, ⟨hwR, ?_⟩, ?_⟩
    · exact ⟨by simp [w], hws⟩
    · funext j
      simp only [w, Function.comp_apply, Fin.snoc_castSucc]
  · rintro ⟨w, ⟨hwR, hwt, _⟩, he⟩
    have hwa : Fin.init w = a := he
    have hwl : w (Fin.last n) = t.val := hwt
    change (Fin.init w, w (Fin.last n)) ∈ R at hwR
    change (a, t.val) ∈ R
    rwa [hwa, hwl] at hwR

end DiamondIntegral.Section2
