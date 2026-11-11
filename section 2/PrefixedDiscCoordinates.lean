import «section 2».CoordinateDiscNames

/-! Coordinate substitution retaining a pre-existing tuple of DC names.
The fixed other new coordinates and radii are real/Gamma parameters; every
old disc centre remains a variable of the invariant relation. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finitePolydiscNames_append {k n : ℕ} (c : Fin k → Bool) (e : Fin n → Bool)
    (a : Fin k → VF M) (b : Fin n → VF M) (δ : Fin k → Gamma M) (η : Fin n → Gamma M) :
    finitePolydiscNames (Fin.append c e) (Fin.append a b) (Fin.append δ η) =
      Fin.append (finitePolydiscNames c a δ) (finitePolydiscNames e b η) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [finitePolydiscNames,Fin.append_left,Fin.append_right]

def prefixedCoordinateGammaIndex (s k : ℕ) {n : ℕ} (i : Fin (n+1)) :
    Fin (s+(k+(n+1))) → Fin ((s+n)+(k+1)) :=
  Fin.addCases (fun j => Fin.castAdd (k+1) (Fin.castAdd n j))
    (Fin.addCases (fun j => Fin.natAdd (s+n) j.castSucc)
      (Fin.insertNth i (Fin.natAdd (s+n) (Fin.last k))
        (fun j => Fin.castAdd (k+1) (Fin.natAdd s j))))

theorem prefixedCoordinateGammaIndex_append {s k n : ℕ} (i : Fin (n+1))
    (σ : Fin s → Gamma M) (δ : Fin n → Gamma M) (τ : Fin k → Gamma M) (γ : Gamma M) :
    Fin.append (Fin.append σ δ) (Fin.snoc τ γ) ∘ prefixedCoordinateGammaIndex s k i =
      Fin.append σ (Fin.append τ (Fin.insertNth i γ δ)) := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · simp only [Function.comp_apply,prefixedCoordinateGammaIndex,Fin.addCases_left,Fin.append_left]
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) q
    · simp only [Function.comp_apply,prefixedCoordinateGammaIndex,Fin.addCases_right,Fin.addCases_left,
        Fin.append_right,Fin.snoc_castSucc,Fin.append_left]
    · refine i.succAboveCases ?_ (fun q => ?_) q
      · simp only [Function.comp_apply,prefixedCoordinateGammaIndex,Fin.addCases_right,Fin.insertNth_apply_same,
          Fin.append_right,Fin.snoc_last]
      · simp only [Function.comp_apply,prefixedCoordinateGammaIndex,Fin.addCases_right,Fin.insertNth_apply_succAbove,
          Fin.append_left,Fin.append_right]

def prefixedCoordinateRealMap {k n : ℕ} (b : Fin (n+1) → VF M) (i : Fin (n+1))
    (z : Fin ((k+1)+1) → M) : Fin ((k+(n+1))+(n+1)) → M :=
  Fin.append
    (Fin.append (fun j => z (Fin.castAdd 1 j.castSucc))
      (Fin.insertNth i (z (Fin.castAdd 1 (Fin.last k))) (Fin.removeNth i (vfValues b))))
    (Fin.insertNth i (z (Fin.last (k+1))) (Fin.removeNth i (vfValues b)))

theorem prefixedCoordinateRealMap_definable (B : ParameterBase M) {k n : ℕ}
    (b : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M) (i : Fin (n+1)) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _
      (coordinateDiscBase B b δ i).real (prefixedCoordinateRealMap (k := k) b i) := by
  let T := (coordinateDiscBase B b δ i).real
  have hfixed (q : Fin n) : Fin.removeNth i (vfValues b) q ∈ T := Or.inr (Set.mem_range_self q)
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  intro j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) q
    · simpa only [prefixedCoordinateRealMap,Fin.append_left] using
        (Set.DefinableFun.proj LRV (A := T) (i := (Fin.castAdd 1 q.castSucc : Fin ((k+1)+1))))
    · refine i.succAboveCases ?_ (fun q => ?_) q
      · simpa only [prefixedCoordinateRealMap,Fin.append_left,Fin.append_right,Fin.insertNth_apply_same] using
          (Set.DefinableFun.proj LRV (A := T) (i := (Fin.castAdd 1 (Fin.last k) : Fin ((k+1)+1))))
      · simpa only [prefixedCoordinateRealMap,Fin.append_left,Fin.append_right,Fin.insertNth_apply_succAbove] using
          LRV.definableFun_const (Fin ((k+1)+1)) (hfixed q)
  · refine i.succAboveCases ?_ (fun q => ?_) q
    · simpa only [prefixedCoordinateRealMap,Fin.append_right,Fin.insertNth_apply_same] using
        (Set.DefinableFun.proj LRV (A := T) (i := (Fin.last (k+1) : Fin ((k+1)+1))))
    · simpa only [prefixedCoordinateRealMap,Fin.append_right,Fin.insertNth_apply_succAbove] using
        LRV.definableFun_const (Fin ((k+1)+1)) (hfixed q)

theorem prefixedCoordinateRealMap_append {k n : ℕ} (b : Fin (n+1) → VF M) (i : Fin (n+1))
    (a : Fin k → VF M) (c : VF M) (x : Fin 1 → M) :
    prefixedCoordinateRealMap b i (Fin.append (vfValues (Fin.snoc a c)) x) =
      Fin.append (vfValues (Fin.append a (Fin.insertNth i c (Fin.removeNth i b))))
        (Fin.insertNth i (x 0) (Fin.removeNth i (vfValues b))) := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) q
    · simp only [prefixedCoordinateRealMap,Fin.append_left,vfValues,Fin.snoc_castSucc]
    · refine i.succAboveCases ?_ (fun q => ?_) q <;>
        simp only [prefixedCoordinateRealMap,Fin.append_left,Fin.append_right,vfValues,
          Fin.snoc_last,Fin.snoc_castSucc,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Fin.removeNth]
  · refine i.succAboveCases ?_ (fun q => ?_) q <;>
      simp only [prefixedCoordinateRealMap,Fin.append_right,Fin.append_left,Fin.append_right_eq_snoc,
        Fin.snoc_last,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]

end DiamondIntegral.Section2
