import Calderon.MixedKernelConstruction.MixedKernelNativeProductAndBasis
import Mathlib.Topology.Connected.Basic
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- Actual product-ball neighbourhoods in the product max metric. -/
theorem exists_product_ball_subset_of_isOpen {Ω : Set (R3 × R3)} (hΩ : IsOpen Ω)
    {p : R3 × R3} (hp : p ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p.1 r ×ˢ Metric.ball p.2 r ⊆ Ω := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ p hp
  refine ⟨r, hr, fun z hz => hsub ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  exact max_lt (Metric.mem_ball.mp hz.1) (Metric.mem_ball.mp hz.2)

/-- Genuine native product UCP on an arbitrary connected open domain. Equality-neighbourhoods
propagate by the checked product-box UCP; no product shape is assumed for the whole domain. -/
theorem native_product_eq_on_connected_open (S : KnownSideSourceData) (L lam : ℝ)
    {Ω A : Set (R3 × R3)} (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    {F G : R3 × R3 → ℝ} (hF : ProductSolutionOn S L lam F Ω)
    (hG : ProductSolutionOn S L lam G Ω)
    (hA : IsOpen A) (hAne : A.Nonempty) (hAΩ : A ⊆ Ω) (hEqA : EqOn F G A) :
    EqOn F G Ω := by
  let N : Set (R3 × R3) := {z | ∃ V : Set (R3 × R3), IsOpen V ∧ z ∈ V ∧
    V ⊆ Ω ∧ EqOn F G V}
  have hNo : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨V, hV, hz, hVΩ, hEqV⟩
    exact Filter.mem_of_superset (hV.mem_nhds hz) fun y hy => ⟨V, hV, hy, hVΩ, hEqV⟩
  have hNne : (Ω ∩ N).Nonempty := by
    obtain ⟨z, hz⟩ := hAne
    exact ⟨z, hAΩ hz, A, hA, hz, hAΩ, hEqA⟩
  have hClosed : closure N ∩ Ω ⊆ N := by
    rintro q ⟨hqN, hqΩ⟩
    obtain ⟨r, hr, hboxΩ⟩ := exists_product_ball_subset_of_isOpen hΩ hqΩ
    let B : Set (R3 × R3) := Metric.ball q.1 r ×ˢ Metric.ball q.2 r
    have hBo : IsOpen B := isOpen_ball.prod isOpen_ball
    have hqB : q ∈ B := ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
    obtain ⟨a, haB, haN⟩ := mem_closure_iff.mp hqN B hBo hqB
    obtain ⟨V, hVo, haV, hVΩ, hEqV⟩ := haN
    obtain ⟨δ, hδ, hsmall⟩ := exists_product_ball_subset_of_isOpen (hVo.inter hBo) ⟨haV,haB⟩
    have hUconn : IsConnected (Metric.ball q.1 r) :=
      (convex_ball q.1 r).isConnected ⟨q.1, Metric.mem_ball_self hr⟩
    have hVconn : IsConnected (Metric.ball q.2 r) :=
      (convex_ball q.2 r).isConnected ⟨q.2, Metric.mem_ball_self hr⟩
    have hA0U : Metric.ball a.1 δ ⊆ Metric.ball q.1 r :=
      by
      intro x hx
      have hxA : (x, a.2) ∈ Metric.ball a.1 δ ×ˢ Metric.ball a.2 δ :=
        ⟨hx, Metric.mem_ball_self hδ⟩
      have hh : (x, a.2) ∈ V ∩ B := hsmall hxA
      exact hh.2.1
    have hB0V : Metric.ball a.2 δ ⊆ Metric.ball q.2 r :=
      by
      intro y hy
      have hyA : (a.1, y) ∈ Metric.ball a.1 δ ×ˢ Metric.ball a.2 δ :=
        ⟨Metric.mem_ball_self hδ, hy⟩
      have hh : (a.1, y) ∈ V ∩ B := hsmall hyA
      exact hh.2.2
    have hEqB := native_product_eq_of_eq_on_box S L lam isOpen_ball hUconn isOpen_ball hVconn
      (productSolutionOn_mono hF hboxΩ) (productSolutionOn_mono hG hboxΩ)
      isOpen_ball ⟨a.1,Metric.mem_ball_self hδ⟩ hA0U
      isOpen_ball ⟨a.2,Metric.mem_ball_self hδ⟩ hB0V
      (by
        intro x hx y hy
        have hxy : (x,y) ∈ Metric.ball a.1 δ ×ˢ Metric.ball a.2 δ := ⟨hx,hy⟩
        have hh : (x,y) ∈ V ∩ B := hsmall hxy
        exact hEqV hh.1)
    exact ⟨B, hBo, hqB, hboxΩ, fun z hz => hEqB z.1 hz.1 z.2 hz.2⟩
  have hΩN : Ω ⊆ N := hconn.isPreconnected.subset_of_closure_inter_subset hNo hNne hClosed
  intro z hz
  obtain ⟨V, hV, hzV, hVΩ, hEqV⟩ := hΩN hz
  exact hEqV hzV

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
