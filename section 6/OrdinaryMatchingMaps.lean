import «section 6».OrdinaryUnaryMatching

/-! Actual raw sets and full maps over the original parameter base,
obtained from the ordinary matching's invariant graph certificates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {n m r s : ℕ}

def originalBaseOrdinarySet (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) R n r)
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A)) : DefSet (rawMixedSpace (M := M) n r) S :=
  ⟨SpecialTransformations.Section5.carrier A,ordinary_named_gamma_set_definable hc _ hA⟩

def originalBaseOrdinaryMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) R n r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R m s}
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hB : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier B))
    (f : SpecialTransformations.Section5.Map A B)
    (hF : SpecialTransformations.Section5.GammaGraphDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.pointMapGraph f)) :
    Map (originalBaseOrdinarySet hc A hA) (originalBaseOrdinarySet hc B hB) :=
  ⟨f,ordinary_named_gamma_graph_definable hc _ hF⟩

theorem originalBaseOrdinaryMap_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) R n r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R m s}
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hB : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier B))
    (f : SpecialTransformations.Section5.Map A B)
    (hF : SpecialTransformations.Section5.GammaGraphDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.pointMapGraph f)) (hf : Function.Bijective f) :
    Function.Bijective (originalBaseOrdinaryMap hc hA hB f hF) := hf

theorem originalBaseOrdinaryMap_contractible (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) R n r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R n s}
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hB : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier B))
    (f : SpecialTransformations.Section5.Map A B)
    (hF : SpecialTransformations.Section5.GammaGraphDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.pointMapGraph f))
    (hContract : SpecialTransformations.Section5.Contractible f)
    (p q : originalBaseOrdinarySet hc A hA)
    (hpq : rvCoordinates M p.val=rvCoordinates M q.val) :
    rvCoordinates M (originalBaseOrdinaryMap hc hA hB f hF p).val=
      rvCoordinates M (originalBaseOrdinaryMap hc hA hB f hF q).val := by
  apply Prod.ext
  · exact ((ordinary_sameRV_iff _ _).mp
      (hContract p q ((ordinary_sameRV_iff _ _).mpr (Prod.mk.inj hpq)))).1
  · exact ((ordinary_sameRV_iff _ _).mp
      (hContract p q ((ordinary_sameRV_iff _ _).mpr (Prod.mk.inj hpq)))).2

end DiamondIntegral.Section6
