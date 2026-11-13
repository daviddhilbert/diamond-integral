import «section 3».RVFiniteValueGammaCorrespondence
import Section3.GammaFullDescent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : GammaParameters.Base (M := M)}

theorem goodGammaRow_mem_code_iff {n : ℕ} {sn : Fin n → SortTag}
    (G : GoodBaseGammaRelation B n sn) (x : Fin n → M) (a : M) (ha : NonzeroRV a) :
    codeValue a ∈ gammaRow G.carrier x ↔ (x,a) ∈ G.carrier := by
  let c : Code (M := M) := ⟨⟨a,ha.1⟩,ha.2⟩
  have hc : value c = codeValue a := (codeValue_raw c).symm
  exact G.invariant x (representative (codeValue a)) c ((representative_value _).trans hc.symm)

def goodUnaryGammaRelation (G : GoodBaseGammaRelation B 1 (fun _ => .rv))
    (γ : Values.Gamma (M := M)) (x : M) : Prop := γ ∈ gammaRow G.carrier ![x]

theorem goodUnaryGammaRelation_sorted (G : GoodBaseGammaRelation B 1 (fun _ => .rv))
    (γ : Values.Gamma (M := M)) (x : M) (hx : goodUnaryGammaRelation G γ x) : iRV x := by
  change (![x],raw (representative γ)) ∈ G.carrier at hx
  let z : Fin 2 → M := Fin.snoc (![x] : Fin 1 → M) (raw (representative γ))
  have hz : (Fin.init z,z (Fin.last 1)) ∈ G.carrier := by
    simpa only [z,Fin.init_snoc,Fin.snoc_last] using hx
  have hp := G.definable.proper z hz (Fin.castSucc (0 : Fin 1))
  simpa only [z,Fin.lastCases_castSucc,Fin.snoc_castSucc,Matrix.cons_val_zero,sortEval,iRV] using hp

theorem goodUnaryGammaRelation_definable (G : GoodBaseGammaRelation B 1 (fun _ => .rv)) :
    DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ goodUnaryGammaRelation G (codeValue (z 0)) (z 1)} := by
  let π : Fin 2 → Fin 2 := Fin.lastCases 0 (fun _ => 1)
  have hh := G.definable.preimage_real (fun _ : Fin 2 => .rv) π
  have he (z : Fin 2 → M) : (Fin.init (z ∘ π),(z ∘ π) (Fin.last 1)) = (![z 1],z 0) := by
    apply Prod.ext
    · funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
  convert hh using 1
  ext z
  change (NonzeroRV (z 0) ∧ goodUnaryGammaRelation G (codeValue (z 0)) (z 1)) ↔
    ((Fin.init (z ∘ π),(z ∘ π) (Fin.last 1)) ∈ G.carrier ∧ z ∈ sortedUniverse (fun _ => .rv))
  rw [he]
  constructor
  · rintro ⟨hn,hr⟩
    have hg := (goodGammaRow_mem_code_iff G ![z 1] (z 0) hn).mp hr
    refine ⟨hg,?_⟩
    intro i
    fin_cases i
    · exact hn.1
    · exact goodUnaryGammaRelation_sorted G _ _ hr
  · rintro ⟨hg,hp⟩
    have hn := G.proper ![z 1] (z 0) hg
    exact ⟨hn,(goodGammaRow_mem_code_iff G ![z 1] (z 0) hn).mpr hg⟩
end DiamondIntegral.Section3
