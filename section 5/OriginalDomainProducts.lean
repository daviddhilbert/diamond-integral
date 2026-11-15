import «section 5».OriginalSortedPredicates
import «section 5».OriginalPredicateSyntax

/-! Canonical block products of arbitrary original RV-domain schemata.
This construction imposes no finite-value condition on either factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def originalDomainLeftIndex (p a b : ℕ) : Fin (p+a) → Fin (p+(a+b)) :=
  Fin.append (Fin.castAdd (a+b)) (fun j => Fin.natAdd p (Fin.castAdd b j))
def originalDomainRightIndex (p a b : ℕ) : Fin (p+b) → Fin (p+(a+b)) :=
  Fin.append (Fin.castAdd (a+b)) (fun j => Fin.natAdd p (Fin.natAdd a j))

theorem originalDomainLeftIndex_row (z : Fin p → M) (w : Fin (a+b) → M) :
    Fin.append z w ∘ originalDomainLeftIndex p a b = Fin.append z (w ∘ Fin.castAdd b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_def,originalDomainLeftIndex,Fin.append_left,Fin.append_right]

theorem originalDomainRightIndex_row (z : Fin p → M) (w : Fin (a+b) → M) :
    Fin.append z w ∘ originalDomainRightIndex p a b = Fin.append z (w ∘ Fin.natAdd a) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_def,originalDomainRightIndex,Fin.append_left,Fin.append_right]

def originalDomainProduct (F : GammaDomainFormula B p a sp) (G : GammaDomainFormula B p b sp) :
    GammaDomainFormula B p (a+b) sp := by
  let st := Fin.append sp (fun _ : Fin (a+b) => .rv)
  have hL : ∀ i, Fin.append sp (fun _ : Fin a => .rv) i = st (originalDomainLeftIndex p a b i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st,originalDomainLeftIndex,Fin.append_left,Fin.append_right]
  have hR : ∀ i, Fin.append sp (fun _ : Fin b => .rv) i = st (originalDomainRightIndex p a b i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st,originalDomainRightIndex,Fin.append_left,Fin.append_right]
  exact ⟨{w | w ∈ sortedUniverse st ∧ w ∘ originalDomainLeftIndex p a b ∈ F.val ∧
      w ∘ originalDomainRightIndex p a b ∈ G.val},
    ((OriginalSortedPredicate.of_definable F.property).pullback _ hL).conj
      ((OriginalSortedPredicate.of_definable G.property).pullback _ hR)⟩

theorem originalDomainProduct_row (F : GammaDomainFormula B p a sp) (G : GammaDomainFormula B p b sp)
    (z : Fin p → M) (w : Fin (a+b) → M) :
    Fin.append z w ∈ (originalDomainProduct F G).val ↔
      Fin.append z (w ∘ Fin.castAdd b) ∈ F.val ∧ Fin.append z (w ∘ Fin.natAdd a) ∈ G.val := by
  change (_ ∧ _ ∧ _) ↔ _
  rw [originalDomainLeftIndex_row,originalDomainRightIndex_row]
  constructor
  · exact fun h => h.2
  · rintro ⟨hf,hg⟩
    refine ⟨?_,hf,hg⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using F.property.proper _ hf (Fin.castAdd a j)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_right,Function.comp_def] using F.property.proper _ hf (Fin.natAdd p j)
      · simpa only [Fin.append_right,Function.comp_def] using G.property.proper _ hg (Fin.natAdd p j)

end DiamondIntegral.Section5
