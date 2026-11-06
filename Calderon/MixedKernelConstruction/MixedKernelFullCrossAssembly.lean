import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
import Calderon.MixedKernelConstruction.MixedKernelNativeProductAndBasis
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

/-- Full original lower crosses from the actual product solution and its entire first cross. -/
theorem native_kernel_full_crosses (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (O1 : Set R3) (hO1 : IsOpen O1) (O2 : Set R3) (hO2 : IsOpen O2) (hO2conn : IsConnected O2)
    (S2 : Set R3) (hS2 : IsOpen S2) (hO2S2 : (O2 ∩ S2).Nonempty)
    (hbox : O1 ×ˢ O2 ⊆ dilatedOffDiagonal S lam)
    (p : R3) (hp : p ∈ O1)
    (hmeet : ∀ U : Set R3, IsOpen U → p ∈ U → ∃ x ∈ U, lam • x ∈ S.W)
    (G : R3 × R3 → ℝ) (hG : ProductSolutionOn S L lam G (O1 ×ˢ O2))
    (hfirst : EqOn G (initialKernel S lam) (O1 ×ˢ S2)) :
    (∀ x ∈ O1, lam • x ∈ S.W → ∀ y ∈ O2, G (x,y) = dilatedKernel2 S lam (x,y)) ∧
    (∀ x ∈ connectedComponentIn O1 p, ∀ y ∈ O2, lam • y ∈ S.W →
      G (x,y) = dilatedKernel1 S lam (x,y)) := by
  obtain ⟨-, hSol, hlow1, hlow2⟩ := known_side_initial_cross_product S L lam hlam
  have hWopen : IsOpen {x : R3 | lam • x ∈ S.W} :=
    S.W_open.preimage (continuous_const_smul lam)
  have hcross : ∀ x ∈ O1, ∀ y ∈ O2, (lam • x ∈ S.W ∨ lam • y ∈ S.W) →
      (x,y) ∈ initialCross S lam :=
    fun x hx y hy hW => ⟨hbox ⟨hx,hy⟩, hW⟩
  -- FULL second agreement: every first coordinate in `O1 ∩ scaled W`.
  have hsecond : ∀ x ∈ O1, lam • x ∈ S.W → ∀ y ∈ O2, G (x,y) = initialKernel S lam (x,y) := by
    intro x hx hxW
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hO1.inter hWopen) x ⟨hx, hxW⟩
    have hBsub : Metric.ball x ε ×ˢ O2 ⊆ O1 ×ˢ O2 :=
      prod_mono (fun z hz => (hball hz).1) subset_rfl
    have hFB : ProductSolutionOn S L lam (initialKernel S lam) (Metric.ball x ε ×ˢ O2) :=
      productSolutionOn_mono hSol
        (fun z hz => hcross z.1 (hball hz.1).1 z.2 hz.2 (Or.inl (hball hz.1).2))
    have heq := native_product_eq_of_eq_on_box S L lam Metric.isOpen_ball
      ((convex_ball x ε).isConnected (Metric.nonempty_ball.mpr hε)) hO2 hO2conn
      (productSolutionOn_mono hG hBsub) hFB Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
      subset_rfl (hO2.inter hS2) hO2S2 inter_subset_left
      (fun x' hx' y' hy' => hfirst ⟨(hball hx').1, hy'.2⟩)
    exact heq x (Metric.mem_ball_self hε)
  -- FULL first agreement on the separator component `C` of `O1`.
  have hCo : IsOpen (connectedComponentIn O1 p) := hO1.connectedComponentIn
  have hCc : IsConnected (connectedComponentIn O1 p) :=
    isConnected_connectedComponentIn_iff.mpr hp
  have hCO1 : connectedComponentIn O1 p ⊆ O1 := connectedComponentIn_subset O1 p
  obtain ⟨x0, hx0C, hx0W⟩ := hmeet _ hCo (mem_connectedComponentIn hp)
  have hfirstfull : ∀ x ∈ connectedComponentIn O1 p, ∀ y ∈ O2, lam • y ∈ S.W →
      G (x,y) = initialKernel S lam (x,y) := by
    intro x hx y hy hyW
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hO2.inter hWopen) y ⟨hy, hyW⟩
    have hCsub : connectedComponentIn O1 p ×ˢ Metric.ball y ε ⊆ O1 ×ˢ O2 :=
      prod_mono hCO1 (fun z hz => (hball hz).1)
    have hFC : ProductSolutionOn S L lam (initialKernel S lam)
        (connectedComponentIn O1 p ×ˢ Metric.ball y ε) :=
      productSolutionOn_mono hSol
        (fun z hz => hcross z.1 (hCO1 hz.1) z.2 (hball hz.2).1 (Or.inr (hball hz.2).2))
    have heq := native_product_eq_of_eq_on_box S L lam hCo hCc Metric.isOpen_ball
      ((convex_ball y ε).isConnected (Metric.nonempty_ball.mpr hε))
      (productSolutionOn_mono hG hCsub) hFC (hCo.inter hWopen) ⟨x0, hx0C, hx0W⟩
      inter_subset_left Metric.isOpen_ball (Metric.nonempty_ball.mpr hε) subset_rfl
      (fun x' hx' y' hy' => hsecond x' (hCO1 hx'.1) hx'.2 y' (hball hy').1)
    exact heq x hx y (Metric.mem_ball_self hε)
  refine ⟨fun x hx hxW y hy => ?_, fun x hx y hy hyW => ?_⟩
  · rw [hsecond x hx hxW y hy]
    exact hlow2 (x,y) (hcross x hx y hy (Or.inl hxW)) hxW
  · rw [hfirstfull x hx y hy hyW]
    exact hlow1 (x,y) (hcross x (hCO1 hx) y hy (Or.inr hyW)) hyW


theorem native_lowerCross_solutions_eqOn (S : KnownSideSourceData) (L lam : ℝ)
    {Ω : Set (R3 × R3)} (hΩ : IsOpen Ω) {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F Ω) (hG : ProductSolutionOn S L lam G Ω)
    (hF1 : ∀ v ∈ Ω, lam • v.2 ∈ S.W → F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v ∈ Ω, lam • v.1 ∈ S.W → F v = dilatedKernel2 S lam v)
    (hG1 : ∀ v ∈ Ω, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v)
    (hG2 : ∀ v ∈ Ω, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v)
    (hmeet : ∀ z ∈ Ω, (connectedComponentIn Ω z ∩
      {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}).Nonempty) :
    EqOn F G Ω := by
  have hWo : IsOpen {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W} :=
    (S.W_open.preimage ((continuous_const_smul lam).comp continuous_fst)).union
      (S.W_open.preimage ((continuous_const_smul lam).comp continuous_snd))
  apply native_product_eq_of_component_seed S L lam hΩ (hΩ.inter hWo) inter_subset_left hF hG
  · rintro v ⟨hv, hv1 | hv2⟩
    · rw [hF2 v hv hv1, hG2 v hv hv1]
    · rw [hF1 v hv hv2, hG1 v hv hv2]
  · intro z hz
    obtain ⟨q, hqC, hqW⟩ := hmeet z hz
    exact ⟨q, hqC, connectedComponentIn_subset Ω z hqC, hqW⟩


theorem exists_native_common_lowerCross_kernel (S : KnownSideSourceData) (L lam : ℝ)
    {ι : Type*} (U : ι → Set (R3 × R3)) (hU : ∀ i, IsOpen (U i))
    (F : ι → R3 × R3 → ℝ) (hF : ∀ i, ProductSolutionOn S L lam (F i) (U i))
    (hF1 : ∀ i, ∀ v ∈ U i, lam • v.2 ∈ S.W → F i v = dilatedKernel1 S lam v)
    (hF2 : ∀ i, ∀ v ∈ U i, lam • v.1 ∈ S.W → F i v = dilatedKernel2 S lam v)
    (hmeet : ∀ i j, ∀ z ∈ U i ∩ U j, (connectedComponentIn (U i ∩ U j) z ∩
      {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}).Nonempty) :
    ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H (⋃ i, U i) ∧
      (∀ v ∈ ⋃ i, U i, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ ⋃ i, U i, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
      ∀ i, EqOn H (F i) (U i) := by
  have hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j) := fun i j =>
    native_lowerCross_solutions_eqOn S L lam ((hU i).inter (hU j))
      (productSolutionOn_mono (hF i) inter_subset_left)
      (productSolutionOn_mono (hF j) inter_subset_right)
      (fun v hv => hF1 i v hv.1) (fun v hv => hF2 i v hv.1)
      (fun v hv => hF1 j v hv.2) (fun v hv => hF2 j v hv.2) (hmeet i j)
  obtain ⟨H, hH, heq⟩ := exists_productSolutionOn_iUnion S L lam U hU F hF hcompat
  refine ⟨H, hH, ?_, ?_, heq⟩
  · intro v hv hvW
    obtain ⟨i, hi⟩ := mem_iUnion.mp hv
    rw [heq i hi]
    exact hF1 i v hi hvW
  · intro v hv hvW
    obtain ⟨i, hi⟩ := mem_iUnion.mp hv
    rw [heq i hi]
    exact hF2 i v hi hvW


theorem constructedMixedKernel_of_native_lowerCross_family (S : KnownSideSourceData)
    (L lam delta Rstar bound separation : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    {ι : Type*} (U : ι → Set (R3 × R3)) (hU : ∀ i, IsOpen (U i))
    (hroom : ∀ i, U i ⊆ dilatedOffDiagonal S lam)
    (F : ι → R3 × R3 → ℝ) (hF : ∀ i, ProductSolutionOn S L lam (F i) (U i))
    (hF1 : ∀ i, ∀ v ∈ U i, lam • v.2 ∈ S.W → F i v = dilatedKernel1 S lam v)
    (hF2 : ∀ i, ∀ v ∈ U i, lam • v.1 ∈ S.W → F i v = dilatedKernel2 S lam v)
    (hmeet : ∀ i j, ∀ z ∈ U i ∩ U j, (connectedComponentIn (U i ∩ U j) z ∩
      {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}).Nonempty)
    (hsphere : ∀ k, ∀ y ∈ cylinder ∩ (cover.packet k).centers, ∀ z ∈ sphere (0 : R3) 1,
      (packetEndpoint S L (cover.packet k) lam y (referenceRadius delta Rstar p L y) z, y) ∈
        ⋃ i, U i)
    (hfixed : fixedSeparationSet bound separation ⊆ ⋃ i, U i) :
    Nonempty (ConstructedMixedKernel S L lam delta Rstar bound separation p cover) := by
  obtain ⟨H, hH, h1, h2, -⟩ := exists_native_common_lowerCross_kernel S L lam U hU F hF hF1 hF2 hmeet
  exact ⟨{ domain := ⋃ i, U i
           domain_open := isOpen_iUnion hU
           domain_room := iUnion_subset hroom
           kernel := H
           product_solution := hH
           sphere_cover := hsphere
           fixed_separation_cover := hfixed
           first_lower_cross := h1
           second_lower_cross := h2 }⟩


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
