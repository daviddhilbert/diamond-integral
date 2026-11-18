import «section 3».GammaPresentationTransport
import IntegrationSection6.GammaSchemaIndexedCoproductTransfer

/-! Expose the literal action of the existing indexed coproduct chart,
including its internal presentation transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem gammaIndexedCoprodIso_labels
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (rvValues t)) (hG : ∀ t ∈ T, G.finiteRow (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (S : (F.coprodFormula G).IndexedPresentation BP) (u : S.domain) :
    ∃ w : indexedDomain T (fun t => graphCoprodDomain (F.rowDomain (rvValues t)) (G.rowDomain (rvValues t))),
      w.val = u.val ∧
      ((F.indexedCoprodIsoFromRows G BP hF hG P Q S).equiv u).val =
        (indexedCoprodEquiv T (fun t => F.rowDomain (rvValues t)) (fun t => G.rowDomain (rvValues t)) w).val := by
  have hD : indexedDomain T (fun t => (F.coprodFormula G).rowDomain (rvValues t)) =
      indexedDomain T (fun t => graphCoprodDomain (F.rowDomain (rvValues t)) (G.rowDomain (rvValues t))) := by
    ext w
    exact and_congr Iff.rfl (F.coprod_row_domain_formula G _ (fun j => (indexedLeft w j).property) (indexedRight w))
  let hR := fun w y => and_congr (Iff.of_eq (congrArg (fun D => w ∈ D) hD)) (Iff.rfl (a := indexedVolume BP.totalVolume
    (fun t => (F.coprodFormula G).rowValue (rvValues t)) w = y))
  let Z := S.congrFormula hD hR
  let uZ : Z.domain := ⟨u.val,(gammaPresentationCongr_domain S hD hR).ge u.property⟩
  let w := Z.domainEquiv uZ
  let eZ := F.indexedCoprodIso G BP hF hG P Q Z
  refine ⟨w,rfl,?_⟩
  unfold GammaFiniteRVSchema.indexedCoprodIsoFromRows
  dsimp only
  change ((gammaFiniteIsoTransportSource (S.congrFormula_toGamma hD hR) eZ).equiv u).val = _
  exact gammaFiniteIsoTransportSource_labels (S.congrFormula_toGamma hD hR) eZ uZ u HEq.rfl

theorem gammaIndexedCoprodIso_volume
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (rvValues t)) (hG : ∀ t ∈ T, G.finiteRow (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (S : (F.coprodFormula G).IndexedPresentation BP) (u : S.domain) :
    ((P.coprod Q).volume ((F.indexedCoprodIsoFromRows G BP hF hG P Q S).equiv u)).val =
      (S.volume u).val := by
  let D := fun t => F.rowDomain (rvValues t)
  let E := fun t => G.rowDomain (rvValues t)
  let e := F.indexedCoprodIsoFromRows G BP hF hG P Q S
  obtain ⟨w,hw,hMap⟩ := gammaIndexedCoprodIso_labels F G BP hF hG P Q S u
  have hSource : (S.volume u).val =
      indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (rvValues t)) u.val :=
    ((S.graph_iff u.val (S.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm
  rcases indexedCoprod_cases T D E w with ⟨t,x,he⟩|⟨t,x,he⟩
  · let px := P.domainEquiv.symm ((indexedSigmaEquiv T D).symm ⟨t,x⟩)
    have hu : u.val = (indexedCoprodLeft T D E t x).val := hw.symm.trans (congrArg Subtype.val he)
    have hImage := hMap.trans ((congrArg (fun q => (indexedCoprodEquiv T D E q).val) he).trans
      (indexedCoprodEquiv_left T D E t x))
    have hTarget := P.coprod_value_at_left Q px (e.equiv u) hImage
    calc
      _ = (P.volume px).val := hTarget
      _ = indexedVolume BP.totalVolume (fun t => F.rowValue (rvValues t)) px.val :=
        ((P.graph_iff px.val (P.volume px).val).mp ⟨px,rfl,rfl⟩).2.2.symm
      _ = indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (rvValues t))
          (indexedCoprodLeft T D E t x).val :=
        (indexedCoprodLeft_volume F G T BP.totalVolume t x (hF t.val t.property) (hG t.val t.property)).symm
      _ = indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (rvValues t)) u.val := congrArg _ hu.symm
      _ = (S.volume u).val := hSource.symm
  · let px := Q.domainEquiv.symm ((indexedSigmaEquiv T E).symm ⟨t,x⟩)
    have hu : u.val = (indexedCoprodRight T D E t x).val := hw.symm.trans (congrArg Subtype.val he)
    have hImage := hMap.trans ((congrArg (fun q => (indexedCoprodEquiv T D E q).val) he).trans
      (indexedCoprodEquiv_right T D E t x))
    have hTarget := P.coprod_value_at_right Q px (e.equiv u) hImage
    calc
      _ = (Q.volume px).val := hTarget
      _ = indexedVolume BP.totalVolume (fun t => G.rowValue (rvValues t)) px.val :=
        ((Q.graph_iff px.val (Q.volume px).val).mp ⟨px,rfl,rfl⟩).2.2.symm
      _ = indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (rvValues t))
          (indexedCoprodRight T D E t x).val :=
        (indexedCoprodRight_volume F G T BP.totalVolume t x (hF t.val t.property) (hG t.val t.property)).symm
      _ = indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (rvValues t)) u.val := congrArg _ hu.symm
      _ = (S.volume u).val := hSource.symm

end DiamondIntegral.Section3
