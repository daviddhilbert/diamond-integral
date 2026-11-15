import «section 5».GammaCellTreeDecoding
import «section 5».GammaCellSyntaxValidity

/-! A whole first-order cylindrical step gives its actual full Gamma
fibre shape and the complete empty-fibre condition off its base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem cylindrical_step_quotient_fibres {P : Type*} {n : ℕ}
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x,y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x,y] ↔ codeValue x < codeValue y))
    (shape : CylinderFibreKind) (C : LRV.Formula (P ⊕ Fin n)) (D : LRV.Formula (P ⊕ Fin (n+1)))
    (v : P → M) (S : Set (Fin n → Values.Gamma (M := M))) (R : Set (Fin (n+1) → Values.Gamma (M := M)))
    (hC : gammaFormulaRepresents C v S) (hD : gammaFormulaRepresents D v R)
    (hstep : (cylindricalStepValidityFormula shape U E T C D).Realize v) :
    (∀ q ∈ R, Fin.tail q ∈ S) ∧
      ∀ η ∈ S, shape.Describes (fun γ : Values.Gamma (M := M) => Fin.cons γ η ∈ R) := by
  have hs := (cylindricalStepValidityFormula_realize shape U E T C D v).mp hstep
  constructor
  · intro q hq
    obtain ⟨z,hz,hqz⟩ := gamma_tuple_code_surjective q
    have hd := (hD z).mpr ⟨hz,hqz.symm ▸ hq⟩
    have hc : C.Realize (Sum.elim v (Fin.tail z)) := by
      by_contra hn
      have hh := (hs (Fin.tail z)).2 hn (fun _ => z 0) ((hU _).mpr (hz 0))
      apply hh
      simpa only [Fin.cons_self_tail] using hd
    have hm := ((hC (Fin.tail z)).mp hc).2
    have he : codeValue ∘ Fin.tail z = Fin.tail q := by
      funext j
      exact congrFun hqz j.succ
    exact he ▸ hm
  · intro η hη
    obtain ⟨y,hy,hqy⟩ := gamma_tuple_code_surjective η
    have hc := (hC y).mpr ⟨hy,hqy.symm ▸ hη⟩
    have hf := (hs y).1 hc
    have hh := (cylindricalFibreValidityFormula_quotient shape U E T (curryFirstCoordinateFormula D)
      (Sum.elim v y) NonzeroRV codeValue (fun γ : Values.Gamma (M := M) => Fin.cons γ η ∈ R)
      hU hE hT EndpointLogic.codeValue_surjective ?_).mp hf
    · exact hh
    · intro t ht
      rw [curryFirstCoordinateFormula_realize,hD]
      have hp : ∀ i, NonzeroRV ((Fin.cons (t 0) y : Fin (n+1) → M) i) := by
        intro i
        exact Fin.cases ht hy i
      have he : codeValue ∘ Fin.cons (t 0) y = Fin.cons (codeValue (t 0)) η := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun hqy j
      rw [he]
      exact and_iff_right hp

end DiamondIntegral.Section5
