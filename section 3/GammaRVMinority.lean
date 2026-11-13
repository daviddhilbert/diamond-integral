import Section3.GammaRVSeparation
import Section3.RVFibreGeometry
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.ModelTheory
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def gammaRVSmallRow (F : GammaRVFamily (M := M) S) (N : ℕ) (γ : Values.Gamma (M := M)) : Prop :=
  {t | F.relation γ t}.Finite ∧ {t | F.relation γ t}.ncard ≤ N

def gammaRVMinorityRelation (F : GammaRVFamily (M := M) S) (D : Set M) (N : ℕ)
    (γ : Values.Gamma (M := M)) (t : M) : Prop :=
  (gammaRVSmallRow F N γ ∧ F.relation γ t) ∨
    (¬ gammaRVSmallRow F N γ ∧ t ∈ D ∧ ¬ F.relation γ t)

theorem gammaRVMinority_definable (F : GammaRVFamily (M := M) S) (D : Set M)
    (hD : DefinableAt S .rv D) (N : ℕ) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | NonzeroRV p.1 ∧ gammaRVMinorityRelation F D N (codeValue p.1) p.2} := by
  let R : Set (M × M) := {p | F.rawRelation p.1 p.2}
  let C := RawClosure.HasMore R N
  have hR := F.definable
  have hC := @RawClosure.hasMore_definable M (CanonicalStructure.normalize (M := M)) S R hR N
  have hD' := (definableAt_iff_normalized_raw S .rv D).mp hD |>.1
  have hp := nonzero_codes_normalized_definable (M := M) S
  have he (a : M) (ha : NonzeroRV a) : a ∉ C ↔ gammaRVSmallRow F N (codeValue a) := by
    have hrow : {t | (a,t) ∈ R} = {t | F.relation (codeValue a) t} := by
      ext t
      exact and_iff_right ha
    change (¬ ∃ u : Fin (N+1) → M, Function.Injective u ∧ ∀ i, (a,u i) ∈ R) ↔ _
    have hh := RawClosure.no_inj_iff_finite_ncard_le (s := {t | (a,t) ∈ R}) (k := N)
    change (¬ ∃ u : Fin (N+1) → M, Function.Injective u ∧ ∀ i, u i ∈ {t | (a,t) ∈ R}) ↔ _
    rw [hrow]
    simpa only [hrow,gammaRVSmallRow] using hh
  let P := NonzeroRV (M := M)
  let G := gammaRVMinorityRelation F D N
  let V : M → Values.Gamma (M := M) := codeValue
  let H := gammaRVSmallRow F N
  let L := F.relation
  change @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | P p.1 ∧ G (V p.1) p.2}
  letI := CanonicalStructure.normalize (M := M)
  have hpc : S.Definable LRV {z : Fin 2 → M | P (z 0)} := definable_unary_at hp (0 : Fin 2)
  have hcc : S.Definable LRV {z : Fin 2 → M | z 0 ∈ C} := definable_unary_at hC (0 : Fin 2)
  have hdc : S.Definable LRV {z : Fin 2 → M | z 1 ∈ D} := definable_unary_at hD' (1 : Fin 2)
  change S.Definable LRV {z : Fin 2 → M | P (z 0) ∧ G (V (z 0)) (z 1)}
  convert hpc.inter ((hcc.compl.inter hR).union (hcc.inter (hdc.inter hR.compl))) using 1
  ext z
  change (P (z 0) ∧ G (V (z 0)) (z 1)) ↔
    (P (z 0) ∧ ((z 0 ∉ C ∧ (z 0,z 1) ∈ R) ∨ (z 0 ∈ C ∧ z 1 ∈ D ∧ (z 0,z 1) ∉ R)))
  by_cases ha : P (z 0)
  · have hsmall := he (z 0) ha
    change (_ ∧ ((H (V (z 0)) ∧ L (V (z 0)) (z 1)) ∨
      (¬ H (V (z 0)) ∧ z 1 ∈ D ∧ ¬ L (V (z 0)) (z 1)))) ↔ _
    change (_ ∧ _) ↔ (P (z 0) ∧ ((z 0 ∉ C ∧ (P (z 0) ∧ L (V (z 0)) (z 1))) ∨
      (z 0 ∈ C ∧ z 1 ∈ D ∧ ¬ (P (z 0) ∧ L (V (z 0)) (z 1)))))
    simp only [ha,true_and,← hsmall]
    tauto
  · simp only [ha,false_and]

def gammaRVMinority (F : GammaRVFamily (M := M) S) (D : Set M)
    (hD : DefinableAt S .rv D) (N : ℕ) : GammaRVFamily (M := M) S where
  relation := gammaRVMinorityRelation F D N
  sorted γ t ht := ht.elim (fun h => F.sorted γ t h.2) (fun h => hD.2 h.2.1)
  definable := gammaRVMinority_definable F D hD N
end DiamondIntegral.Section3
