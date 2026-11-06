import MixedKernelProductOpenUCP
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

/-- Both literal operators depend on the germ of the same function. -/
theorem productSolutionOn_congr_open (S : KnownSideSourceData) (L lam : ℝ)
    {Ω : Set (R3 × R3)} (hΩ : IsOpen Ω) {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F Ω) (hEq : EqOn G F Ω) :
    ProductSolutionOn S L lam G Ω := by
  refine ⟨hF.1.congr hEq, ?_, ?_⟩
  · intro z hz
    have hpre : {x : R3 | (x,z.2) ∈ Ω} ∈ 𝓝 z.1 :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hz)
    have hh : (fun x => G (x,z.2)) =ᶠ[𝓝 z.1] (fun x => F (x,z.2)) :=
      Filter.mem_of_superset hpre (fun x hx => hEq hx)
    have hold := hF.2.1 z hz
    rw [coordinateFluxDivergence_metricDivergenceFlux_eq_Lop] at hold ⊢
    exact (UCP.divCoeffGrad_congr (EventuallyEq.refl _ _) hh).trans hold
  · intro z hz
    have hpre : {y : R3 | (z.1,y) ∈ Ω} ∈ 𝓝 z.2 :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hz)
    have hh : (fun y => G (z.1,y)) =ᶠ[𝓝 z.2] (fun y => F (z.1,y)) :=
      Filter.mem_of_superset hpre (fun y hy => hEq hy)
    apply (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam _ z.2).mpr
    exact (UCP.divCoeffGrad_congr (EventuallyEq.refl _ _) hh).trans
      ((normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
        S.g2_admissible L lam _ z.2).mp (hF.2.2 z hz))

/-- Each actual overlap component must meet the common seed. -/
theorem native_product_eq_of_component_seed (S : KnownSideSourceData) (L lam : ℝ)
    {Ω A : Set (R3 × R3)} (hΩ : IsOpen Ω) (hA : IsOpen A) (hAΩ : A ⊆ Ω)
    {F G : R3 × R3 → ℝ} (hF : ProductSolutionOn S L lam F Ω)
    (hG : ProductSolutionOn S L lam G Ω) (heq : EqOn F G A)
    (hmeet : ∀ z ∈ Ω, (connectedComponentIn Ω z ∩ A).Nonempty) : EqOn F G Ω := by
  intro z hz
  let C := connectedComponentIn Ω z
  have hC : IsOpen C := hΩ.connectedComponentIn
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hz
  have hsub : C ⊆ Ω := connectedComponentIn_subset Ω z
  have h := native_product_eq_on_connected_open S L lam hC hCconn
    (productSolutionOn_mono hF hsub) (productSolutionOn_mono hG hsub)
    (hC.inter hA) (hmeet z hz) inter_subset_left
    (fun q hq => heq hq.2)
  exact h (mem_connectedComponentIn hz)

/-- Pairwise equality on the actual overlaps produces one literal product solution. -/
theorem exists_productSolutionOn_iUnion (S : KnownSideSourceData) (L lam : ℝ)
    {ι : Type*} (U : ι → Set (R3 × R3)) (hU : ∀ i, IsOpen (U i))
    (F : ι → R3 × R3 → ℝ) (hF : ∀ i, ProductSolutionOn S L lam (F i) (U i))
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j)) :
    ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H (⋃ i, U i) ∧
      ∀ i, EqOn H (F i) (U i) := by
  let H : R3 × R3 → ℝ := fun z => if h : ∃ i, z ∈ U i then F (Classical.choose h) z else 0
  have heq : ∀ i, EqOn H (F i) (U i) := by
    intro i z hz
    have hex : ∃ j, z ∈ U j := ⟨i,hz⟩
    dsimp only [H]
    rw [dif_pos hex]
    exact hcompat (Classical.choose hex) i ⟨Classical.choose_spec hex,hz⟩
  have hsol : ∀ i, ProductSolutionOn S L lam H (U i) := fun i =>
    productSolutionOn_congr_open S L lam (hU i) (hF i) (heq i)
  refine ⟨H, ⟨?_, ?_, ?_⟩, heq⟩
  · refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨U i, hU i, hi, (hsol i).1.mono inter_subset_right⟩
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact (hsol i).2.1 z hi
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact (hsol i).2.2 z hi

/-- A genuine continuous interval path stays inside the actual overlap component. -/
theorem continuous_interval_endpoint_mem_component {Ω : Set (R3 × R3)} {z : R3 × R3}
    (a b : ℝ) (f : ℝ → R3 × R3) (hf : ContinuousOn f (uIcc a b))
    (hstart : f a = z) (hinside : Set.MapsTo f (uIcc a b) Ω) :
    f b ∈ connectedComponentIn Ω z := by
  have hpre : IsPreconnected (f '' uIcc a b) := isPreconnected_uIcc.image f hf
  have hz : z ∈ f '' uIcc a b := ⟨a,left_mem_uIcc,hstart⟩
  have hsub : f '' uIcc a b ⊆ Ω := by
    rintro q ⟨t,ht,rfl⟩
    exact hinside ht
  exact hpre.subset_connectedComponentIn hz hsub ⟨b,right_mem_uIcc,rfl⟩

/-- Overlapping output boxes centered at the SAME level reach a common height above it. -/
theorem exists_vertical_segment_above_common_level {X : Type*} (B1 B2 : Set X)
    (a d1 d2 : ℝ) (hd1 : 0 < d1) (hd2 : 0 < d2) (z : X × ℝ)
    (hz : z ∈ (B1 ×ˢ Ioo (a-d1) (a+d1)) ∩ (B2 ×ˢ Ioo (a-d2) (a+d2))) :
    ∃ h : ℝ, a < h ∧ ∀ t ∈ uIcc z.2 h,
      (z.1,t) ∈ (B1 ×ˢ Ioo (a-d1) (a+d1)) ∩ (B2 ×ˢ Ioo (a-d2) (a+d2)) := by
  let h := a + min d1 d2 / 2
  have hm : 0 < min d1 d2 := lt_min hd1 hd2
  have hh1 : a-d1 < h ∧ h < a+d1 := by
    dsimp [h]
    constructor <;> linarith [min_le_left d1 d2]
  have hh2 : a-d2 < h ∧ h < a+d2 := by
    dsimp [h]
    constructor <;> linarith [min_le_right d1 d2]
  refine ⟨h, by dsimp [h]; linarith, ?_⟩
  intro t ht
  have hbounds : a-d1 < t ∧ t < a+d1 ∧ a-d2 < t ∧ t < a+d2 := by
    rcases Set.mem_uIcc.mp ht with ⟨hl,hu⟩ | ⟨hl,hu⟩
    · exact ⟨hz.1.2.1.trans_le hl, hu.trans_lt hh1.2,
        hz.2.2.1.trans_le hl, hu.trans_lt hh2.2⟩
    · exact ⟨hh1.1.trans_le hl, hu.trans_lt hz.1.2.2,
        hh2.1.trans_le hl, hu.trans_lt hz.2.2.2⟩
  exact ⟨⟨hz.1.1,hbounds.1,hbounds.2.1⟩,⟨hz.2.1,hbounds.2.2.1,hbounds.2.2.2⟩⟩

/-- Actual continuous reachability into the common open seed discharges the component condition. -/
theorem native_product_eq_of_interval_seed (S : KnownSideSourceData) (L lam : ℝ)
    {Ω A : Set (R3 × R3)} (hΩ : IsOpen Ω) (hA : IsOpen A) (hAΩ : A ⊆ Ω)
    {F G : R3 × R3 → ℝ} (hF : ProductSolutionOn S L lam F Ω)
    (hG : ProductSolutionOn S L lam G Ω) (heq : EqOn F G A)
    (hreach : ∀ z ∈ Ω, ∃ (a b : ℝ) (f : ℝ → R3 × R3),
      ContinuousOn f (uIcc a b) ∧ f a = z ∧ Set.MapsTo f (uIcc a b) Ω ∧ f b ∈ A) :
    EqOn F G Ω := by
  apply native_product_eq_of_component_seed S L lam hΩ hA hAΩ hF hG heq
  intro z hz
  obtain ⟨a,b,f,hf,hstart,hinside,hseed⟩ := hreach z hz
  exact ⟨f b, continuous_interval_endpoint_mem_component a b f hf hstart hinside, hseed⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
