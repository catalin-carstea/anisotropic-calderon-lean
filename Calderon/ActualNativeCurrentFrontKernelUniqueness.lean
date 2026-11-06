import Calderon.MixedKernelConstruction.MixedKernelProductOpenUCP
import Calderon.MixedKernelConstruction.MixedKernelNativeCompactFront
import Calderon.MixedKernelConstruction.MixedKernelUniformLowerSide
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError ConformalDepth ActualScalarPrincipalAdjoint

theorem native_product_eventuallyEq_on_preconnected_subset (S : KnownSideSourceData) (L lam : ℝ)
    {Ω A Fset : Set (R3 × R3)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Fset)
    (hFset : Fset ⊆ Ω)
    {F G : R3 × R3 → ℝ} (hF : ProductSolutionOn S L lam F Ω)
    (hG : ProductSolutionOn S L lam G Ω)
    (hA : IsOpen A) (hAne : (Fset ∩ A).Nonempty) (hAΩ : A ⊆ Ω) (hEqA : EqOn F G A) :
    ∀ q ∈ Fset, F =ᶠ[𝓝 q] G := by
  let N : Set (R3 × R3) := {z | ∃ V : Set (R3 × R3), IsOpen V ∧ z ∈ V ∧
    V ⊆ Ω ∧ EqOn F G V}
  have hNo : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨V, hV, hz, hVΩ, hEqV⟩
    exact Filter.mem_of_superset (hV.mem_nhds hz) fun y hy => ⟨V, hV, hy, hVΩ, hEqV⟩
  have hNne : (Fset ∩ N).Nonempty := by
    obtain ⟨z, hzF, hz⟩ := hAne
    exact ⟨z, hzF, A, hA, hz, hAΩ, hEqA⟩
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
  have hFN : Fset ⊆ N := hconn.subset_of_closure_inter_subset hNo hNne
    (fun q hq => hClosed ⟨hq.1,hFset hq.2⟩)
  intro q hq
  obtain ⟨V,hVo,hqV,hVΩ,hEqV⟩ := hFN hq
  filter_upwards [hVo.mem_nhds hqV] with t ht
  exact hEqV ht

theorem convex_native_center_cylinder : Convex ℝ cylinder := by
  intro x hx y hy a b ha hb hab
  change (a*x 0+b*y 0)^2+(a*x 1+b*y 1)^2 ≤ 1 ∧
    (-1:ℝ) ≤ a*x 2+b*y 2 ∧ a*x 2+b*y 2 ≤ 1
  have hDisk : a*(x 0^2+x 1^2)+b*(y 0^2+y 1^2)-
      ((a*x 0+b*y 0)^2+(a*x 1+b*y 1)^2) =
      a*b*((x 0-y 0)^2+(x 1-y 1)^2) := by
    rw [show b=1-a by linarith only [hab]]
    ring
  have hNonneg : 0 ≤ a*b*((x 0-y 0)^2+(x 1-y 1)^2) :=
    mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hxDisk := mul_le_mul_of_nonneg_left hx.1 ha
  have hyDisk := mul_le_mul_of_nonneg_left hy.1 hb
  have hxLo := mul_le_mul_of_nonneg_left hx.2.1 ha
  have hyLo := mul_le_mul_of_nonneg_left hy.2.1 hb
  have hxHi := mul_le_mul_of_nonneg_left hx.2.2 ha
  have hyHi := mul_le_mul_of_nonneg_left hy.2.2 hb
  exact ⟨by nlinarith only [hDisk,hNonneg,hxDisk,hyDisk,hab],
    by nlinarith only [hxLo,hyLo,hab],by nlinarith only [hxHi,hyHi,hab]⟩

def nativeFixedDirectionCurrentFront
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam delta Rstar : ℝ) (p : ℕ) (z : R3) : Set (R3 × R3) :=
  (fun y : R3 => (nativeCoverEndpoint S L C lam ((y,referenceRadius delta Rstar p L y),z),y)) '' cylinder

theorem isPreconnected_nativeFixedDirectionCurrentFront
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0:ℝ) C.dilationCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (hroom : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < C.radiusCeiling)
    (z : R3) (hz : z ∈ sphere (0:R3) 1) :
    IsPreconnected (nativeFixedDirectionCurrentFront S L C lam delta Rstar p z) := by
  apply convex_native_center_cylinder.isPreconnected.image
  intro y hy
  obtain ⟨i,hi⟩ := C.covers_cylinder y hy
  have hzNorm : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz
  have hGraph : ContinuousAt (fun y : R3 => ((y,referenceRadius delta Rstar p L y),z)) y :=
    (continuousAt_id.prodMk ((contDiff_referenceRadius_actual delta Rstar p L hd hR).continuous.continuousAt)).prodMk continuousAt_const
  have hNative := (contDiffAt_nativeCoverEndpoint S L C lam hlam i y hi
    (referenceRadius delta Rstar p L y) (referenceRadius_pos delta Rstar p L y hd hR)
    (hroom y hy) z (by rw [hzNorm];norm_num)).continuousAt
  have hEnd : ContinuousAt (fun c : R3 =>
      nativeCoverEndpoint S L C lam ((c,referenceRadius delta Rstar p L c),z)) y :=
    hNative.comp (f := fun c : R3 => ((c,referenceRadius delta Rstar p L c),z)) hGraph
  exact (hEnd.prodMk continuousAt_id).continuousWithinAt

theorem exists_uniform_constructedMixedKernel_sphere_germ_uniqueness (S : KnownSideSourceData) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ (L : ℝ) (C : NativeNormalCover S L)
      (lam delta Rstar bound separation : ℝ) (p : ℕ)
      (K1 K2 : ConstructedMixedKernel S L lam delta Rstar bound separation p C),
      0 < lam → lam ≤ lam0 → lam ≤ C.dilationCeiling → 0 < delta → 0 < Rstar →
      (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < C.radiusCeiling) →
      ∀ i : Fin C.count, ∀ y ∈ cylinder ∩ (C.packet i).centers,
      ∀ z ∈ sphere (0:R3) 1,
      K1.kernel =ᶠ[𝓝 (packetEndpoint S L (C.packet i) lam y (referenceRadius delta Rstar p L y) z,y)] K2.kernel := by
  classical
  obtain ⟨lam0,hlam0,hLower⟩ := exists_uniform_scaled_lower_strip S 2 (1/4) (by norm_num) (by norm_num)
  refine ⟨lam0,hlam0,?_⟩
  intro L C lam delta Rstar bound separation p K1 K2 hlam hlam0 hlamC hdelta hRstar hRadius i y hy z hz
  have hLam : lam ∈ Icc (0:ℝ) C.dilationCeiling := ⟨hlam.le,hlamC⟩
  let Fset := nativeFixedDirectionCurrentFront S L C lam delta Rstar p z
  have hFconn : IsPreconnected Fset := isPreconnected_nativeFixedDirectionCurrentFront
    S L C lam hLam delta Rstar p hdelta hRstar hRadius z hz
  have hz2 : z ∈ closedBall (0:R3) 2 :=
    closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall hz)
  let Ω := K1.domain ∩ K2.domain
  have hΩ : IsOpen Ω := K1.domain_open.inter K2.domain_open
  have hFΩ : Fset ⊆ Ω := by
    rintro q ⟨c,hc,rfl⟩
    obtain ⟨j,hj⟩ := C.covers_cylinder c hc
    have hEq := nativeCoverEndpoint_eq_packet S L C lam hLam j c hj
      (referenceRadius delta Rstar p L c) (referenceRadius_pos delta Rstar p L c hdelta hRstar)
      (hRadius c hc) z hz2
    change (nativeCoverEndpoint S L C lam ((c,referenceRadius delta Rstar p L c),z),c) ∈ Ω
    rw [hEq]
    exact ⟨K1.sphere_cover j c ⟨hc,hj⟩ z hz,K2.sphere_cover j c ⟨hc,hj⟩ z hz⟩
  let yb : R3 := EuclideanSpace.single (2:Fin 3) (-1/2:ℝ)
  have hyb : yb ∈ cylinder := by norm_num [yb,cylinder,PiLp.single_apply]
  have hybLower : lam • yb ∈ S.W :=
    hLower lam hlam hlam0 yb (norm_le_two_of_mem_cylinder yb hyb)
      (by norm_num [yb,PiLp.single_apply])
  let qb : R3 × R3 := (nativeCoverEndpoint S L C lam ((yb,referenceRadius delta Rstar p L yb),z),yb)
  have hqb : qb ∈ Fset := ⟨yb,hyb,rfl⟩
  let A : Set (R3 × R3) := Ω ∩ (fun q : R3 × R3 => lam • q.2) ⁻¹' S.W
  have hKnownContinuous : Continuous (fun q : R3 × R3 => lam • q.2) := by
    fun_prop
  have hA : IsOpen A := hΩ.inter (S.W_open.preimage hKnownContinuous)
  have hAne : (Fset ∩ A).Nonempty := ⟨qb,hqb,hFΩ hqb,hybLower⟩
  have hAΩ : A ⊆ Ω := inter_subset_left
  have hEqA : EqOn K1.kernel K2.kernel A := by
    intro q hq
    exact (K1.first_lower_cross q hq.1.1 hq.2).trans (K2.first_lower_cross q hq.1.2 hq.2).symm
  have hGerms := native_product_eventuallyEq_on_preconnected_subset S L lam hΩ hFconn hFΩ
    (productSolutionOn_mono K1.product_solution inter_subset_left)
    (productSolutionOn_mono K2.product_solution inter_subset_right) hA hAne hAΩ hEqA
  have hEq := nativeCoverEndpoint_eq_packet S L C lam hLam i y hy.2
    (referenceRadius delta Rstar p L y) (referenceRadius_pos delta Rstar p L y hdelta hRstar)
    (hRadius y hy.1) z hz2
  have hPoint : (packetEndpoint S L (C.packet i) lam y (referenceRadius delta Rstar p L y) z,y) ∈ Fset :=
    ⟨y,hy.1,congrArg (fun X : R3 => (X,y)) hEq⟩
  exact hGerms _ hPoint

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
