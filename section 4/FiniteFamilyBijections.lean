import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fintype.Basic

/-! A bijection of finitely labelled unions decomposes into bijections
between its source/target component slices. This is a set-level result;
labels add no coordinates to the component sets. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FiniteFamilyBijections
variable {ι κ X Y : Type*} (A : ι → Set X) (B : κ → Set Y)

abbrev Domain := {p : ι × X // p.2 ∈ A p.1}

variable {A B}

def sourcePiece (f : Domain A ≃ Domain B) (i : ι) (j : κ) : Set X :=
  {x | ∃ hx : x ∈ A i, (f ⟨(i, x), hx⟩).val.1 = j}

def targetPiece (f : Domain A ≃ Domain B) (i : ι) (j : κ) : Set Y :=
  sourcePiece f.symm j i

def pieceMap (f : Domain A ≃ Domain B) (default : Y) (i : ι) (x : X) : Y :=
  if hx : x ∈ A i then (f ⟨(i, x), hx⟩).val.2 else default

theorem pieceMap_on (f : Domain A ≃ Domain B) (default : Y) (i : ι) (x : X) (hx : x ∈ A i) :
    pieceMap f default i x = (f ⟨(i, x), hx⟩).val.2 := by simp only [pieceMap, dite_eq_left hx]

theorem sourcePiece_subset (f : Domain A ≃ Domain B) (i : ι) (j : κ) : sourcePiece f i j ⊆ A i :=
  fun _ h => h.choose

theorem sourcePiece_disjoint (f : Domain A ≃ Domain B) (i : ι) {j j' : κ} (h : j ≠ j') :
    Disjoint (sourcePiece f i j) (sourcePiece f i j') := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hx, hj⟩ ⟨_, hj'⟩
  exact h (hj.symm.trans hj')

theorem sourcePiece_cover (f : Domain A ≃ Domain B) (i : ι) : (⋃ j, sourcePiece f i j) = A i := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact sourcePiece_subset f i j hj
  · intro hx
    exact Set.mem_iUnion.mpr ⟨(f ⟨(i, x), hx⟩).val.1, hx, rfl⟩

theorem pieceMap_mem (f : Domain A ≃ Domain B) (default : Y) (i : ι) (j : κ)
    (x : X) (hx : x ∈ sourcePiece f i j) : pieceMap f default i x ∈ targetPiece f i j := by
  obtain ⟨hx, hj⟩ := hx
  have he : (j, pieceMap f default i x) = (f ⟨(i, x), hx⟩).val := by
    apply Prod.ext
    · exact hj.symm
    · exact pieceMap_on f default i x hx
  have hb : pieceMap f default i x ∈ B j := by
    simpa only [← he] using (f ⟨(i, x), hx⟩).property
  refine ⟨hb, ?_⟩
  have hq : (⟨(j, pieceMap f default i x), hb⟩ : Domain B) = f ⟨(i, x), hx⟩ := Subtype.ext he
  change (f.symm ⟨(j, pieceMap f default i x), hb⟩).val.1 = i
  rw [hq, f.symm_apply_apply]

theorem pieceMap_bijOn (f : Domain A ≃ Domain B) (default : Y) (i : ι) (j : κ) :
    Set.BijOn (pieceMap f default i) (sourcePiece f i j) (targetPiece f i j) := by
  refine ⟨fun x hx => pieceMap_mem f default i j x hx, ?_, ?_⟩
  · rintro x ⟨hx, hjx⟩ y ⟨hy, hjy⟩ he
    have hf : f ⟨(i, x), hx⟩ = f ⟨(i, y), hy⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact hjx.trans hjy.symm
      · exact (pieceMap_on f default i x hx).symm.trans (he.trans (pieceMap_on f default i y hy))
    exact congrArg (fun p : Domain A => p.val.2) (f.injective hf)
  · rintro y ⟨hy, hi⟩
    let p : Domain A := f.symm ⟨(j, y), hy⟩
    have hp : p.val.1 = i := hi
    have hpa : p.val.2 ∈ A i := hp ▸ p.property
    have hpe : (⟨(i, p.val.2), hpa⟩ : Domain A) = p := by
      apply Subtype.ext
      exact Prod.ext hp.symm rfl
    have hfp : f ⟨(i, p.val.2), hpa⟩ = ⟨(j, y), hy⟩ := (congrArg f hpe).trans (f.apply_symm_apply _)
    refine ⟨p.val.2, ⟨hpa, ?_⟩, ?_⟩
    · exact congrArg (fun q : Domain B => q.val.1) hfp
    · rw [pieceMap_on f default i p.val.2 hpa]
      exact congrArg (fun q : Domain B => q.val.2) hfp


def mapDomain {X' : Type*} {A' : ι → Set X'} (c : X → X')
    (hc : ∀ i x, x ∈ A i → c x ∈ A' i) (p : Domain A) : Domain A' :=
  ⟨(p.val.1, c p.val.2), hc p.val.1 p.val.2 p.property⟩

theorem commute_symm {X' Y' : Type*} {A' : ι → Set X'} {B' : κ → Set Y'}
    (f : Domain A ≃ Domain B) (g : Domain A' ≃ Domain B') (c : X → X') (d : Y → Y')
    (hc : ∀ i x, x ∈ A i → c x ∈ A' i) (hd : ∀ j y, y ∈ B j → d y ∈ B' j)
    (h : ∀ p, mapDomain d hd (f p) = g (mapDomain c hc p)) (q : Domain B) :
    mapDomain c hc (f.symm q) = g.symm (mapDomain d hd q) := by
  apply g.injective
  rw [g.apply_symm_apply, ← h, f.apply_symm_apply]

theorem sourcePiece_pullback {X' Y' : Type*} {A' : ι → Set X'} {B' : κ → Set Y'}
    (f : Domain A ≃ Domain B) (g : Domain A' ≃ Domain B') (c : X → X') (d : Y → Y')
    (hc : ∀ i x, x ∈ A i → c x ∈ A' i) (hd : ∀ j y, y ∈ B j → d y ∈ B' j)
    (h : ∀ p, mapDomain d hd (f p) = g (mapDomain c hc p)) (i : ι) (j : κ) :
    sourcePiece f i j = {x | x ∈ A i ∧ c x ∈ sourcePiece g i j} := by
  ext x
  constructor
  · rintro ⟨hx, hj⟩
    refine ⟨hx, hc i x hx, ?_⟩
    have he := congrArg (fun p : Domain B' => p.val.1) (h ⟨(i, x), hx⟩)
    exact he.symm.trans hj
  · rintro ⟨hx, _, hj⟩
    refine ⟨hx, ?_⟩
    have he := congrArg (fun p : Domain B' => p.val.1) (h ⟨(i, x), hx⟩)
    exact he.trans hj

theorem targetPiece_pullback {X' Y' : Type*} {A' : ι → Set X'} {B' : κ → Set Y'}
    (f : Domain A ≃ Domain B) (g : Domain A' ≃ Domain B') (c : X → X') (d : Y → Y')
    (hc : ∀ i x, x ∈ A i → c x ∈ A' i) (hd : ∀ j y, y ∈ B j → d y ∈ B' j)
    (h : ∀ p, mapDomain d hd (f p) = g (mapDomain c hc p)) (i : ι) (j : κ) :
    targetPiece f i j = {y | y ∈ B j ∧ d y ∈ targetPiece g i j} :=
  sourcePiece_pullback f.symm g.symm d c hd hc (fun q => commute_symm f g c d hc hd h q) j i

end DiamondIntegral.Section4.FiniteFamilyBijections
