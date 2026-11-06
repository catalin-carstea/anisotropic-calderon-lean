import Calderon.ActualShrinkingRadiusMetricLimit
import Calderon.ActualNormalizedPrincipalH8InitialSmallness
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile CoordinateBootstrapJets NormalizedPrincipalMetric
  ActualNormalizedPrincipalH8InitialSmallness

/-- Compactness turns pointwise half-improvement into an open set of valid
parameters; closedness and connectedness then propagate the initial bound. -/
theorem forall_le_of_compact_half_improvement
    {T E : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [TopologicalSpace E] [CompactSpace E]
    (H : E → ℝ) (r : T → E → ℝ) (eps : ℝ)
    (hH : Continuous H) (hr : Continuous (fun q : T × E => r q.1 q.2))
    (heps : 0 < eps) (hrpos : ∀ t y, 0 < r t y)
    (t0 : T) (hInitial : ∀ y, H y ≤ eps * r t0 y)
    (hImprove : ∀ t, (∀ y, H y ≤ eps * r t y) →
      ∀ y, H y ≤ (eps/2) * r t y) :
    ∀ t y, H y ≤ eps * r t y := by
  let A : Set T := {t | ∀ y, H y ≤ eps * r t y}
  have hClosed : IsClosed A := by
    have hi : IsClosed (⋂ y : E, {t : T | H y ≤ eps * r t y}) := by
      apply isClosed_iInter
      intro y
      exact isClosed_le continuous_const
        (continuous_const.mul (hr.comp (continuous_id.prodMk continuous_const)))
    convert hi using 1
    ext t
    simp [A]
  let B : Set (T × E) := {q | eps * r q.1 q.2 ≤ H q.2}
  have hB : IsClosed B := isClosed_le (continuous_const.mul hr) (hH.comp continuous_snd)
  have hProject : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  have hStrict : IsOpen {t : T | ∀ y, H y < eps * r t y} := by
    convert hProject.isOpen_compl using 1
    ext t
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, Prod.exists, B]
    simp
  have hEq : A = {t : T | ∀ y, H y < eps * r t y} := by
    ext t
    constructor
    · intro ht y
      have hy := hImprove t ht y
      have hp := hrpos t y
      nlinarith
    · intro ht y
      exact (ht y).le
  have hClopen : IsClopen A := ⟨hClosed, hEq ▸ hStrict⟩
  have hAll : A = Set.univ := hClopen.eq_univ ⟨t0,hInitial⟩
  intro t y
  exact (show t ∈ A from hAll ▸ Set.mem_univ t) y

/-- The original compact-set bootstrap propagates over all positive delta
with the fixed actual softplus radius and fixed normalized metric pair. -/
theorem le_referenceRadius_forall_delta_of_compact_half_improvement
    (F : R3 → ℝ) (L R eps : ℝ) (p : ℕ)
    (K : Set R3) (hK : IsCompact K) (hF : ContinuousOn F K)
    (hR : 0 < R) (heps : 0 < eps)
    (hInitial : ∀ x ∈ K,
      F x ≤
        eps * referenceRadius 1 R p L x)
    (hImprove : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      (∀ x ∈ K, F x ≤
        eps * referenceRadius delta R p L x) →
      ∀ x ∈ K, F x ≤
        (eps/2) * referenceRadius delta R p L x) :
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ K,
      F x ≤
        eps * referenceRadius delta R p L x := by
  let T : Type := {delta : ℝ // delta ∈ Ioc (0 : ℝ) 1}
  let E : Type := {x : R3 // x ∈ K}
  letI : CompactSpace E := isCompact_iff_compactSpace.mp hK
  letI : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  let H : E → ℝ := fun x => F x
  let r : T → E → ℝ := fun delta x => referenceRadius delta R p L x
  have hH : Continuous H := continuousOn_iff_continuous_domRestrict.mp hF
  have hd : Continuous (fun q : T × E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun q : T × E => referenceDepth L (q.2 : R3)) :=
    (contDiff_referenceDepth L).continuous.comp
      (continuous_subtype_val.comp continuous_snd)
  have hnonzero : ∀ q : T × E, (q.1 : ℝ) ≠ 0 := fun q => ne_of_gt q.1.property.1
  have hs : Continuous (fun q : T × E => softplus (q.1 : ℝ) (referenceDepth L (q.2 : R3))) := by
    unfold softplus
    have hsum : Continuous (fun q : T × E =>
        1 + Real.exp (referenceDepth L (q.2 : R3) / (q.1 : ℝ))) :=
      continuous_const.add (Real.continuous_exp.comp (ht.div hd hnonzero))
    have hlog : Continuous (fun q : T × E =>
        Real.log (1 + Real.exp (referenceDepth L (q.2 : R3) / (q.1 : ℝ)))) := by
      apply hsum.log
      intro q
      exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (Real.exp_pos _).le)
    exact hd.mul hlog
  have hr : Continuous (fun q : T × E => r q.1 q.2) :=
    continuous_const.mul (hs.pow p)
  have hrpos : ∀ delta : T, ∀ x : E, 0 < r delta x :=
    fun delta x => referenceRadius_pos delta R p L x delta.property.1 hR
  let one : T := ⟨1, by constructor <;> norm_num⟩
  have hInit : ∀ x : E, H x ≤ eps * r one x := fun x => hInitial x x.property
  have hImp : ∀ delta : T, (∀ x : E, H x ≤ eps * r delta x) →
      ∀ x : E, H x ≤ (eps/2) * r delta x := by
    intro delta hb x
    exact hImprove delta delta.property.1 delta.property.2
      (fun y hy => hb ⟨y,hy⟩) x x.property
  have hAll := forall_le_of_compact_half_improvement H r eps hH hr heps hrpos one hInit hImp
  intro delta hd0 hd1 x hx
  exact hAll ⟨delta,hd0,hd1⟩ ⟨x,hx⟩


/-- The original compact-set bootstrap propagates over all positive delta
with the fixed actual softplus radius and fixed normalized metric pair. -/
theorem coordinateH8_le_referenceRadius_forall_delta_of_strict_improvement
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam R eps : ℝ) (p : ℕ) (K : Set R3) (hK : IsCompact K)
    (hR : 0 < R) (heps : 0 < eps)
    (hInitial : ∀ x ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius 1 R p L x)
    (hImprove : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius delta R p L x) →
      ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        (eps/2) * referenceRadius delta R p L x) :
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius delta R p L x := by
  have hContinuous : ContinuousOn
      (fun x : R3 => coordinateH8
        (referenceNormalizedPrincipalDifference g1 g2 L lam) x) K :=
    ((continuous_referenceNormalizedPrincipalDifference_coordinateH8 g1 g2 hg1 hg2 L).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  exact le_referenceRadius_forall_delta_of_compact_half_improvement
    (fun x : R3 => coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x)
    L R eps p K hK hContinuous hR heps hInitial hImprove

/-- Actual local principal vanishing follows once the initial compact bound,
its strict improvement, and the independent off-K all-delta bound are supplied.
This implication does not assert the missing improvement or density estimate. -/
theorem exists_open_principal_vanishing_of_compact_strict_improvement
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam R eps : ℝ) (p : ℕ) (K : Set R3) (hK : IsCompact K)
    (hL : 0 < L) (hR : 0 < R) (heps : 0 < eps) (hp : 1 ≤ p)
    (hInitial : ∀ x ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius 1 R p L x)
    (hImprove : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius delta R p L x) →
      ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        (eps/2) * referenceRadius delta R p L x)
    (hOff : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ cylinder, x ∉ K →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius delta R p L x) :
    ∃ U : Set R3, IsOpen U ∧ (0 : R3) ∈ U ∧ U ⊆ cylinder ∧
      EqOn (referenceNormalizedPrincipalDifference g1 g2 L lam) (fun _ => 0) U := by
  have hOn := coordinateH8_le_referenceRadius_forall_delta_of_strict_improvement
    g1 g2 hg1 hg2 L lam R eps p K hK hR heps hInitial hImprove
  apply exists_open_neighborhood_zero_of_coordinateH8_forall_delta
    (referenceNormalizedPrincipalDifference g1 g2 L lam) L R eps p hL hR.le heps.le hp
  intro delta hd hd1 x hx
  by_cases hmem : x ∈ K
  · exact hOn delta hd hd1 x hmem
  · exact hOff delta hd hd1 x hx hmem

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
