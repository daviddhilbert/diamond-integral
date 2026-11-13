import «section 4».RVResiduePullback

/-! Auxiliary full-parameter value fibres and their pure-field
normalizations. The original object's base is retained in its definition;
enlargement here is used only to prove geometric nonvanishing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueFullFibres
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem value_named (hc : CanonicalStructure.IsCanonical (M := M))
    (t : CanonicalRV.RVSort M) : RVValueDefinable (Set.univ : Set M) (Values.vrv t) := by
  have hl : (Set.univ : Set M).Definable LRV {a : Fin 1 → M | iLe (a 0) t.val} := by
    exact (raw_le_definable Set.univ).preimage_map
      (show (Set.univ : Set M).DefinableMap LRV (fun a : Fin 1 → M => ![a 0, t.val]) from
        fun i => by fin_cases i; exact Set.DefinableFun.proj LRV;
                    exact LRV.definableFun_const (Fin 1) (Set.mem_univ t.val))
  have hr : (Set.univ : Set M).Definable LRV {a : Fin 1 → M | iLe t.val (a 0)} := by
    exact (raw_le_definable Set.univ).preimage_map
      (show (Set.univ : Set M).DefinableMap LRV (fun a : Fin 1 → M => ![t.val, a 0]) from
        fun i => by fin_cases i; exact LRV.definableFun_const (Fin 1) (Set.mem_univ t.val);
                    exact Set.DefinableFun.proj LRV)
  have hd := (definableAt_sort (Set.univ : Set M) .rv).raw_definable.inter (hl.inter hr)
  have he : {a : M | iRV a ∧ iLe a t.val ∧ iLe t.val a} = rvValuePullback (Values.vrv t) := by
    ext a
    constructor
    · rintro ⟨ha, hle, hge⟩
      exact ⟨ha, le_antisymm ((Values.vrv_le_iff ⟨a, ha⟩ t).mpr hle)
        ((Values.vrv_le_iff t ⟨a, ha⟩).mpr hge)⟩
    · rintro ⟨ha, hv⟩
      exact ⟨ha, (Values.vrv_le_iff ⟨a, ha⟩ t).mp hv.le,
        (Values.vrv_le_iff t ⟨a, ha⟩).mp hv.ge⟩
  apply raw_definable_sorted hc Set.univ (rvValuePullback (Values.vrv t)) .rv
  · rw [← he]
    exact hd
  · rintro a ⟨ha, _⟩
    exact ha

def fullBase {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    DefSet (rawRVSpace (M := M) n) Set.univ where
  carrier := A.carrier
  definable := Set.Definable.mono A.definable (Set.subset_univ S)

def fibre (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (s : Fin n → CanonicalRV.RVSort M) :
    DefSet (rawRVSpace (M := M) n) Set.univ :=
  rvValueFibre (fullBase A) (fun i => Values.vrv (s i)) (fun i => value_named hc (s i))

def normalized (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (s : Fin n → CanonicalRV.RVSort M) :
    Set (Fin n → ModelResidue M) := normalizedResidueSet (fibre hc A s) s

theorem normalized_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) : PureDef (normalized hc A s) :=
  RVResiduePullback.normalized_definable hc (fibre hc A s) s

def normalizationEquiv (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) : fibre hc A s ≃ normalized hc A s :=
  residueNormalizationEquiv (fibre hc A s) s (fun _ ht => ht.2)

end DiamondIntegral.Section4.RVResidueFullFibres
