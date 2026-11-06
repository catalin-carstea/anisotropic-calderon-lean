import MixedKernelMonotoneCurrentPair
import MixedKernelPositiveChartAgreement
import MixedKernelObservedOutputRooms
import MixedKernelCurrentCommonPair
import MixedKernelProductOpenUCP
import MixedKernelCenteredRooms
import MixedKernelFiniteInterpolation
import MixedKernelKnownSideNearOne
import MixedKernelAnnulusGeometry
import MixedKernelKnownSideCompactBuffer
import MixedKernelActualSeparatorAnchors
import MixedKernelKnownSideNeighborhood
import MixedKernelCompatibleGluing
import MixedKernelFullCrossAssembly
import MixedKernelAnchoredKernelConstruction
import Calderon.CollaboratorUCPCarlemanOct17
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry


/-- The actual source dictionary with its two metrics/kernels interchanged; every field is
an existing field of `S`, with `metrics_match`/`kernels_match` reversed. -/
def swappedKnownSideSourceData (S : KnownSideSourceData) : KnownSideSourceData where
  hreg := S.hreg
  hcalc := S.hcalc
  original1 := S.original2
  original2 := S.original1
  original1_admissible := S.original2_admissible
  original2_admissible := S.original1_admissible
  K1 := S.K2
  K2 := S.K1
  G1 := S.G2
  G2 := S.G1
  kernel1 := S.kernel2
  kernel2 := S.kernel1
  coordinateRoom := S.coordinateRoom
  coordinateRoom_open := S.coordinateRoom_open
  origin_mem := S.origin_mem
  Xi1 := S.Xi2
  Xi2 := S.Xi1
  Xi1_smooth := S.Xi2_smooth
  Xi2_smooth := S.Xi1_smooth
  Xi1_injective := S.Xi2_injective
  Xi2_injective := S.Xi1_injective
  Xi1_jacobian := S.Xi2_jacobian
  Xi2_jacobian := S.Xi1_jacobian
  Xi1_room := S.Xi2_room
  Xi2_room := S.Xi1_room
  g1 := S.g2
  g2 := S.g1
  g1_admissible := S.g2_admissible
  g2_admissible := S.g1_admissible
  carrier1 := S.carrier2
  carrier2 := S.carrier1
  g1_origin := S.g2_origin
  g2_origin := S.g1_origin
  harmonic_coordinates1 := S.harmonic_coordinates2
  harmonic_coordinates2 := S.harmonic_coordinates1
  W := S.W
  W_open := S.W_open
  W_room := S.W_room
  metrics_match := S.metrics_match.symm
  kernels_match := fun x hx y hy hne => (S.kernels_match x hx y hy hne).symm
  separating_function := S.separating_function
  separating_function_smooth := S.separating_function_smooth
  separating_function_zero := S.separating_function_zero
  separating_function_normal := S.separating_function_normal
  one_sided_room := S.one_sided_room

/-- Interchanging the original data twice restores the same source. -/
theorem swappedKnownSideSourceData_involutive (S : KnownSideSourceData) :
    swappedKnownSideSourceData (swappedKnownSideSourceData S) = S := by
  cases S; rfl

/-- The same coordinate-room off-diagonal is retained. -/
theorem swapped_dilatedOffDiagonal (S : KnownSideSourceData) (lam : ℝ) :
    dilatedOffDiagonal (swappedKnownSideSourceData S) lam = dilatedOffDiagonal S lam := rfl

/-- The original known cross does not change when the metric names are exchanged. -/
theorem swapped_initialCross (S : KnownSideSourceData) (lam : ℝ) :
    initialCross (swappedKnownSideSourceData S) lam = initialCross S lam := rfl

theorem swapped_dilatedKernel1 (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3) :
    dilatedKernel1 (swappedKnownSideSourceData S) lam v = dilatedKernel2 S lam v := rfl

theorem swapped_dilatedKernel2 (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3) :
    dilatedKernel2 (swappedKnownSideSourceData S) lam v = dilatedKernel1 S lam v := rfl

/-- Actual original Green symmetry `S.kernel1.1.2`, through the SAME branch and dilation. -/
theorem dilatedKernel1_swap (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3)
    (hv : v ∈ dilatedOffDiagonal S lam) :
    dilatedKernel1 S lam (v.2,v.1) = dilatedKernel1 S lam v := by
  have hv' : lam • v.1 ∈ S.coordinateRoom ∧ lam • v.2 ∈ S.coordinateRoom ∧ v.1 ≠ v.2 := hv
  have hx : lam • v.1 ∈ S.coordinateRoom := hv'.1
  have hy : lam • v.2 ∈ S.coordinateRoom := hv'.2.1
  have hh := S.kernel1.1.2
    ⟨S.Xi1 (lam • v.1),S.Xi1_room _ hx⟩ ⟨S.Xi1 (lam • v.2),S.Xi1_room _ hy⟩
  simp only [dilatedKernel1,coordinateKernel1,dif_pos hx,dif_pos hy]
  exact congrArg (fun t : ℝ => lam*t) hh

/-- Actual original Green symmetry `S.kernel2.1.2`, through the SAME branch and dilation. -/
theorem dilatedKernel2_swap (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3)
    (hv : v ∈ dilatedOffDiagonal S lam) :
    dilatedKernel2 S lam (v.2,v.1) = dilatedKernel2 S lam v := by
  have hv' : lam • v.1 ∈ S.coordinateRoom ∧ lam • v.2 ∈ S.coordinateRoom ∧ v.1 ≠ v.2 := hv
  have hx : lam • v.1 ∈ S.coordinateRoom := hv'.1
  have hy : lam • v.2 ∈ S.coordinateRoom := hv'.2.1
  have hh := S.kernel2.1.2
    ⟨S.Xi2 (lam • v.1),S.Xi2_room _ hx⟩ ⟨S.Xi2 (lam • v.2),S.Xi2_room _ hy⟩
  simp only [dilatedKernel2,coordinateKernel2,dif_pos hx,dif_pos hy]
  exact congrArg (fun t : ℝ => lam*t) hh

/-- Transpose an actual literal two-equation solution of the swapped source, retaining
`L` and `lam`; each zero passes through the checked native flux/beta identities. -/
theorem productSolutionOn_of_swapped_source (S : KnownSideSourceData) (L lam : ℝ)
    {F : R3 × R3 → ℝ} {U : Set (R3 × R3)}
    (hF : ProductSolutionOn (swappedKnownSideSourceData S) L lam F U) :
    ProductSolutionOn S L lam (fun v : R3 × R3 => F (v.2,v.1)) (Prod.swap ⁻¹' U) := by
  have hc : ContDiffOn ℝ ∞ (fun v : R3 × R3 => F (v.2,v.1)) (Prod.swap ⁻¹' U) :=
    hF.1.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun v hv => hv)
  refine ⟨hc,?_,?_⟩
  · intro v hv
    have hv' : (v.2,v.1) ∈ U := hv
    rw [coordinateFluxDivergence_metricDivergenceFlux_eq_Lop]
    exact (normalizedSecondLaplacian_eq_zero_iff S.g2 S.g1 S.g2_admissible S.g1_admissible
      L lam (fun x => F (v.2,x)) v.1).mp (hF.2.2 (v.2,v.1) hv')
  · intro v hv
    have hv' : (v.2,v.1) ∈ U := hv
    apply (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible S.g2_admissible
      L lam (fun y => F (y,v.1)) v.2).mpr
    have hh := hF.2.1 (v.2,v.1) hv'
    rw [coordinateFluxDivergence_metricDivergenceFlux_eq_Lop] at hh
    exact hh

/-- Both FULL original lower-cross identities survive transposition of a swapped solution. -/
theorem full_lower_crosses_of_swapped_source (S : KnownSideSourceData) (lam : ℝ)
    {F : R3 × R3 → ℝ} {U : Set (R3 × R3)}
    (hroom : U ⊆ dilatedOffDiagonal (swappedKnownSideSourceData S) lam)
    (hF1 : ∀ v ∈ U, lam • v.2 ∈ S.W →
      F v = dilatedKernel1 (swappedKnownSideSourceData S) lam v)
    (hF2 : ∀ v ∈ U, lam • v.1 ∈ S.W →
      F v = dilatedKernel2 (swappedKnownSideSourceData S) lam v) :
    (∀ v ∈ Prod.swap ⁻¹' U, lam • v.2 ∈ S.W → F (v.2,v.1) = dilatedKernel1 S lam v) ∧
    (∀ v ∈ Prod.swap ⁻¹' U, lam • v.1 ∈ S.W → F (v.2,v.1) = dilatedKernel2 S lam v) := by
  have hroom' (v : R3 × R3) (hv : v ∈ Prod.swap ⁻¹' U) : v ∈ dilatedOffDiagonal S lam := by
    have hv' : (v.2,v.1) ∈ U := hv
    have hh : lam • v.2 ∈ S.coordinateRoom ∧ lam • v.1 ∈ S.coordinateRoom ∧ v.2 ≠ v.1 :=
      hroom hv'
    exact ⟨hh.2.1,hh.1,fun h => hh.2.2 h.symm⟩
  constructor
  · intro v hv hvW
    have hv' : (v.2,v.1) ∈ U := hv
    rw [hF2 (v.2,v.1) hv' hvW,swapped_dilatedKernel2]
    exact dilatedKernel1_swap S lam v (hroom' v hv)
  · intro v hv hvW
    have hv' : (v.2,v.1) ∈ U := hv
    rw [hF1 (v.2,v.1) hv' hvW,swapped_dilatedKernel1]
    exact dilatedKernel2_swap S lam v (hroom' v hv)

/-- Pointwise path-UCP: equality at one point whose ACTUAL interval path inside the open
domain ends in the open agreement seed; only that point's component is used. -/
theorem native_product_eq_at_of_path (S : KnownSideSourceData) (L lam : ℝ)
    {Ω A : Set (R3 × R3)} (hΩ : IsOpen Ω) (hA : IsOpen A)
    {F G : R3 × R3 → ℝ} (hF : ProductSolutionOn S L lam F Ω)
    (hG : ProductSolutionOn S L lam G Ω) (heq : EqOn F G A) {z : R3 × R3} (hz : z ∈ Ω)
    (a b : ℝ) (f : ℝ → R3 × R3) (hf : ContinuousOn f (uIcc a b))
    (hstart : f a = z) (hinside : Set.MapsTo f (uIcc a b) Ω) (hend : f b ∈ A) :
    F z = G z := by
  let C := connectedComponentIn Ω z
  have hC : IsOpen C := hΩ.connectedComponentIn
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hz
  have hsub : C ⊆ Ω := connectedComponentIn_subset Ω z
  have hb : f b ∈ C := continuous_interval_endpoint_mem_component a b f hf hstart hinside
  have h := native_product_eq_on_connected_open S L lam hC hCconn
    (productSolutionOn_mono hF hsub) (productSolutionOn_mono hG hsub)
    (hC.inter hA) ⟨f b,hb,hend⟩ inter_subset_left
    (fun q hq => heq hq.2)
  exact h (mem_connectedComponentIn hz)

/-- Larger native comparison product around an actual anchor. -/
def overlapLarge (p : R3) (R s : ℝ) : Set (R3 × R3) :=
  ball p R ×ˢ {y | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}

/-- Retained narrower product, compared inside `overlapLarge`. -/
def overlapRetained (p : R3) (r s : ℝ) : Set (R3 × R3) :=
  ball p r ×ˢ {y | 19*s/20 < ‖y-p‖ ∧ ‖y-p‖ < 21*s/20}

theorem isOpen_overlapLarge (p : R3) (R s : ℝ) : IsOpen (overlapLarge p R s) := by
  have h1 : IsOpen {y : R3 | 4*s/5 < ‖y-p‖} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {y : R3 | ‖y-p‖ < 6*s/5} := isOpen_lt (by fun_prop) continuous_const
  exact isOpen_ball.prod (h1.inter h2)

/-- A downward vertical shift of height at most `6r` stays in the larger first ball. -/
theorem vertical_shift_mem_ball {p x : R3} {r R h t : ℝ} (hx : x ∈ ball p r) (hh0 : 0 ≤ h)
    (hh : h ≤ 6*r) (hR : 20*r ≤ R) (ht : t ∈ uIcc (0:ℝ) 1) :
    x - (t*h) • EuclideanSpace.single (2:Fin 3) (1:ℝ) ∈ ball p R := by
  rw [uIcc_of_le zero_le_one] at ht
  rw [mem_ball] at hx ⊢
  have hr : 0 ≤ r := le_trans dist_nonneg hx.le
  have hn : ‖(t*h) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ = t*h := by
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (mul_nonneg ht.1 hh0)]
  have hth : t*h ≤ h := mul_le_of_le_one_left hh0 ht.2
  rw [dist_eq_norm] at hx ⊢
  have hle : ‖x - (t*h) • EuclideanSpace.single (2:Fin 3) (1:ℝ) - p‖ ≤
      ‖x - p‖ + ‖(t*h) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ := by
    rw [sub_right_comm]; exact norm_sub_le _ _
  linarith

/-- The retained annulus lies in the larger comparison annulus with strict margins. -/
theorem retained_annulus_mem_large {p y : R3} {s : ℝ}
    (hy : 19*s/20 < ‖y-p‖ ∧ ‖y-p‖ < 21*s/20) : 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5 := by
  have hs : 0 < s := by linarith [hy.1, hy.2]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- Same orientation: lowering ONLY the first factor by `6 min(r_i,r_j)` keeps the whole
path in BOTH larger comparison products. -/
theorem same_orientation_path_mem {pi pj : R3} {Ri Rj ri rj si sj : ℝ}
    (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj) {v : R3 × R3}
    (hvi : v ∈ overlapRetained pi ri si) (hvj : v ∈ overlapRetained pj rj sj)
    {t : ℝ} (ht : t ∈ uIcc (0:ℝ) 1) :
    (v.1 - (t*(6*min ri rj)) • EuclideanSpace.single (2:Fin 3) (1:ℝ), v.2) ∈
      overlapLarge pi Ri si ∩ overlapLarge pj Rj sj := by
  have hvi' : v.1 ∈ ball pi ri ∧ (19*si/20 < ‖v.2-pi‖ ∧ ‖v.2-pi‖ < 21*si/20) := hvi
  have hvj' : v.1 ∈ ball pj rj ∧ (19*sj/20 < ‖v.2-pj‖ ∧ ‖v.2-pj‖ < 21*sj/20) := hvj
  have hri : 0 ≤ ri := le_trans dist_nonneg (mem_ball.mp hvi'.1).le
  have hrj : 0 ≤ rj := le_trans dist_nonneg (mem_ball.mp hvj'.1).le
  have hm : 0 ≤ 6*min ri rj := by have := le_min hri hrj; linarith
  exact ⟨⟨vertical_shift_mem_ball hvi'.1 hm (by linarith [min_le_left ri rj]) hRi ht,
      retained_annulus_mem_large hvi'.2⟩,
    ⟨vertical_shift_mem_ball hvj'.1 hm (by linarith [min_le_right ri rj]) hRj ht,
      retained_annulus_mem_large hvj'.2⟩⟩

/-- Same-orientation retained contact: two actual product solutions on the larger products,
each with the FULL original second lower-cross identity, agree at every retained-overlap
point whose actual lowered endpoint lies in the ORIGINAL `W`. -/
theorem retained_same_orientation_eq (S : KnownSideSourceData) (L lam : ℝ)
    {pi pj : R3} {Ri Rj ri rj si sj : ℝ} (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj)
    {Fi Fj : R3 × R3 → ℝ}
    (hFi : ProductSolutionOn S L lam Fi (overlapLarge pi Ri si))
    (hFj : ProductSolutionOn S L lam Fj (overlapLarge pj Rj sj))
    (hFi2 : ∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w)
    (hFj2 : ∀ w ∈ overlapLarge pj Rj sj, lam • w.1 ∈ S.W → Fj w = dilatedKernel2 S lam w)
    {v : R3 × R3} (hvi : v ∈ overlapRetained pi ri si) (hvj : v ∈ overlapRetained pj rj sj)
    (hW : lam • (v.1 - (6*min ri rj) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ S.W) :
    Fi v = Fj v := by
  have hΩ : IsOpen (overlapLarge pi Ri si ∩ overlapLarge pj Rj sj) :=
    (isOpen_overlapLarge pi Ri si).inter (isOpen_overlapLarge pj Rj sj)
  have hcW : Continuous fun w : R3 × R3 => lam • w.1 := continuous_fst.const_smul lam
  have hWo : IsOpen {w : R3 × R3 | lam • w.1 ∈ S.W} := S.W_open.preimage hcW
  let f : ℝ → R3 × R3 := fun t =>
    (v.1 - (t*(6*min ri rj)) • EuclideanSpace.single (2:Fin 3) (1:ℝ), v.2)
  have hf : Continuous f :=
    (continuous_const.sub ((continuous_id.mul continuous_const).smul continuous_const)).prodMk
      continuous_const
  have hinside : Set.MapsTo f (uIcc 0 1) (overlapLarge pi Ri si ∩ overlapLarge pj Rj sj) :=
    fun t ht => same_orientation_path_mem hRi hRj hvi hvj ht
  have h0 : f 0 = v := by
    show (v.1 - ((0:ℝ)*(6*min ri rj)) • EuclideanSpace.single (2:Fin 3) (1:ℝ), v.2) = v
    simp
  have hz : v ∈ overlapLarge pi Ri si ∩ overlapLarge pj Rj sj := by
    rw [← h0]; exact hinside left_mem_uIcc
  have hend : f 1 ∈ (overlapLarge pi Ri si ∩ overlapLarge pj Rj sj) ∩
      {w : R3 × R3 | lam • w.1 ∈ S.W} := by
    refine ⟨hinside right_mem_uIcc, ?_⟩
    show lam • (v.1 - ((1:ℝ)*(6*min ri rj)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ S.W
    rw [one_mul]; exact hW
  exact native_product_eq_at_of_path S L lam hΩ (hΩ.inter hWo)
    (productSolutionOn_mono hFi inter_subset_left) (productSolutionOn_mono hFj inter_subset_right)
    (fun w hw => (hFi2 w hw.1.1 hw.2).trans (hFj2 w hw.1.2 hw.2).symm) hz 0 1 f
    hf.continuousOn h0 hinside hend

/-- Opposite orientation: lowering ONLY the first factor by `6 r_i` keeps the whole path in
the larger `i` product and in the factor-swapped larger `j` product. -/
theorem opposite_orientation_path_mem {pi pj : R3} {Ri Rj ri rj si sj : ℝ}
    (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj) (hri1 : ri ≤ si/1000) (hrj1 : rj ≤ sj/1000)
    {v : R3 × R3} (hvi : v ∈ overlapRetained pi ri si)
    (hvj : Prod.swap v ∈ overlapRetained pj rj sj) {t : ℝ} (ht : t ∈ uIcc (0:ℝ) 1) :
    (v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ), v.2) ∈
      overlapLarge pi Ri si ∩ Prod.swap ⁻¹' overlapLarge pj Rj sj := by
  have hvi' : v.1 ∈ ball pi ri ∧ (19*si/20 < ‖v.2-pi‖ ∧ ‖v.2-pi‖ < 21*si/20) := hvi
  have hvj' : v.2 ∈ ball pj rj ∧ (19*sj/20 < ‖v.1-pj‖ ∧ ‖v.1-pj‖ < 21*sj/20) := hvj
  have ha : ‖v.1 - pi‖ < ri := by rw [← dist_eq_norm]; exact mem_ball.mp hvi'.1
  have hc : ‖v.2 - pj‖ < rj := by rw [← dist_eq_norm]; exact mem_ball.mp hvj'.1
  have hri : 0 ≤ ri := le_trans (norm_nonneg _) ha.le
  have hrj : 0 ≤ rj := le_trans (norm_nonneg _) hc.le
  have T1 : ‖v.2 - pi‖ ≤ ‖v.1 - pi‖ + ‖v.1 - v.2‖ := by
    have h := norm_sub_le (v.1 - pi) (v.1 - v.2)
    rwa [sub_sub_sub_cancel_left] at h
  have T2 : ‖v.1 - v.2‖ ≤ ‖v.1 - pj‖ + ‖v.2 - pj‖ := by
    have h := norm_sub_le (v.1 - pj) (v.2 - pj)
    rwa [sub_sub_sub_cancel_right] at h
  have hA : v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ) ∈ ball pi Ri :=
    vertical_shift_mem_ball hvi'.1 (by linarith) le_rfl hRi ht
  rw [uIcc_of_le zero_le_one] at ht
  have hn : ‖(t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ = t*(6*ri) := by
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (mul_nonneg ht.1 (by linarith))]
  have hth : t*(6*ri) ≤ 6*ri := mul_le_of_le_one_left (by linarith) ht.2
  have heq : v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ) - pj =
      (v.1 - pj) - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ) := sub_right_comm _ _ _
  have T3 : ‖(v.1 - pj) - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ ≤
      ‖v.1 - pj‖ + ‖(t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ := norm_sub_le _ _
  have T4 : ‖v.1 - pj‖ ≤ ‖(v.1 - pj) - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ +
      ‖(t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ := by
    have h := norm_add_le ((v.1 - pj) - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ))
      ((t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ))
    rwa [sub_add_cancel] at h
  have hB : v.2 ∈ ball pj Rj := mem_ball.mpr (by rw [dist_eq_norm]; linarith)
  have hC : 4*sj/5 < ‖v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ) - pj‖ ∧
      ‖v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ) - pj‖ < 6*sj/5 := by
    rw [heq]
    have hsi := hvi'.2.1
    have hsj := hvj'.2
    constructor <;> linarith
  have hJ : (v.2, v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈
      overlapLarge pj Rj sj := ⟨hB,hC⟩
  exact ⟨⟨hA,retained_annulus_mem_large hvi'.2⟩,hJ⟩

/-- Opposite-orientation retained contact for two actual literal `S`-solutions, the second
on the factor-swapped larger product, both with the FULL original second identity. -/
theorem retained_opposite_orientation_eq (S : KnownSideSourceData) (L lam : ℝ)
    {pi pj : R3} {Ri Rj ri rj si sj : ℝ} (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj)
    (hri1 : ri ≤ si/1000) (hrj1 : rj ≤ sj/1000) {Fi Gj : R3 × R3 → ℝ}
    (hFi : ProductSolutionOn S L lam Fi (overlapLarge pi Ri si))
    (hGj : ProductSolutionOn S L lam Gj (Prod.swap ⁻¹' overlapLarge pj Rj sj))
    (hFi2 : ∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w)
    (hGj2 : ∀ w ∈ Prod.swap ⁻¹' overlapLarge pj Rj sj, lam • w.1 ∈ S.W →
      Gj w = dilatedKernel2 S lam w)
    {v : R3 × R3} (hvi : v ∈ overlapRetained pi ri si)
    (hvj : Prod.swap v ∈ overlapRetained pj rj sj)
    (hW : lam • (v.1 - (6*ri) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ S.W) :
    Fi v = Gj v := by
  have hΩ : IsOpen (overlapLarge pi Ri si ∩ Prod.swap ⁻¹' overlapLarge pj Rj sj) :=
    (isOpen_overlapLarge pi Ri si).inter ((isOpen_overlapLarge pj Rj sj).preimage continuous_swap)
  have hcW : Continuous fun w : R3 × R3 => lam • w.1 := continuous_fst.const_smul lam
  have hWo : IsOpen {w : R3 × R3 | lam • w.1 ∈ S.W} := S.W_open.preimage hcW
  let f : ℝ → R3 × R3 := fun t =>
    (v.1 - (t*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ), v.2)
  have hf : Continuous f :=
    (continuous_const.sub ((continuous_id.mul continuous_const).smul continuous_const)).prodMk
      continuous_const
  have hinside : Set.MapsTo f (uIcc 0 1)
      (overlapLarge pi Ri si ∩ Prod.swap ⁻¹' overlapLarge pj Rj sj) :=
    fun t ht => opposite_orientation_path_mem hRi hRj hri1 hrj1 hvi hvj ht
  have h0 : f 0 = v := by
    show (v.1 - ((0:ℝ)*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ), v.2) = v
    simp
  have hz : v ∈ overlapLarge pi Ri si ∩ Prod.swap ⁻¹' overlapLarge pj Rj sj := by
    rw [← h0]; exact hinside left_mem_uIcc
  have hend : f 1 ∈ (overlapLarge pi Ri si ∩ Prod.swap ⁻¹' overlapLarge pj Rj sj) ∩
      {w : R3 × R3 | lam • w.1 ∈ S.W} := by
    refine ⟨hinside right_mem_uIcc, ?_⟩
    show lam • (v.1 - ((1:ℝ)*(6*ri)) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ S.W
    rw [one_mul]; exact hW
  exact native_product_eq_at_of_path S L lam hΩ (hΩ.inter hWo)
    (productSolutionOn_mono hFi inter_subset_left) (productSolutionOn_mono hGj inter_subset_right)
    (fun w hw => (hFi2 w hw.1.1 hw.2).trans (hGj2 w hw.1.2 hw.2).symm) hz 0 1 f
    hf.continuousOn h0 hinside hend

/-- Opposite orientation with an ACTUAL swapped-source solution: its transpose is compared
through the original Green symmetry, not an assumed kernel symmetry. -/
theorem retained_opposite_orientation_eq_swapped (S : KnownSideSourceData) (L lam : ℝ)
    {pi pj : R3} {Ri Rj ri rj si sj : ℝ} (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj)
    (hri1 : ri ≤ si/1000) (hrj1 : rj ≤ sj/1000) {Fi Fj : R3 × R3 → ℝ}
    (hFi : ProductSolutionOn S L lam Fi (overlapLarge pi Ri si))
    (hFi2 : ∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w)
    (hFj : ProductSolutionOn (swappedKnownSideSourceData S) L lam Fj (overlapLarge pj Rj sj))
    (hroom : overlapLarge pj Rj sj ⊆ dilatedOffDiagonal (swappedKnownSideSourceData S) lam)
    (hFj1 : ∀ w ∈ overlapLarge pj Rj sj, lam • w.2 ∈ S.W →
      Fj w = dilatedKernel1 (swappedKnownSideSourceData S) lam w)
    (hFj2 : ∀ w ∈ overlapLarge pj Rj sj, lam • w.1 ∈ S.W →
      Fj w = dilatedKernel2 (swappedKnownSideSourceData S) lam w)
    {v : R3 × R3} (hvi : v ∈ overlapRetained pi ri si)
    (hvj : Prod.swap v ∈ overlapRetained pj rj sj)
    (hW : lam • (v.1 - (6*ri) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ S.W) :
    Fi v = Fj (v.2,v.1) :=
  retained_opposite_orientation_eq S L lam hRi hRj hri1 hrj1 hFi
    (productSolutionOn_of_swapped_source S L lam hFj) hFi2
    (full_lower_crosses_of_swapped_source S lam hroom hFj1 hFj2).2 hvi hvj hW

/-- Scale-free mean-value control of the ACTUAL separator on one small original ball. -/
theorem exists_separator_descent_ball (S : KnownSideSourceData) :
    ∃ a : ℝ, 0 < a ∧ ball (0 : R3) a ⊆ S.coordinateRoom ∧
      {z ∈ ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W ∧
      ∀ z0 ∈ ball (0 : R3) a, ∀ z1 ∈ ball (0 : R3) a,
        S.separating_function z1 ≤ S.separating_function z0 + (z1 - z0) 2 + (1/4) * ‖z1 - z0‖ := by
  obtain ⟨a1, ha1, hroom, hW, -⟩ := separating_noncritical_ball S
  have hcd : ContDiffAt ℝ ∞ S.separating_function 0 :=
    S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hcont : ContinuousAt (fderiv ℝ S.separating_function) 0 :=
    hcd.continuousAt_fderiv (by simp)
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.mp hcont (1/4) (by norm_num)
  have hsub : ball (0 : R3) (min a1 δ) ⊆ ball (0 : R3) a1 := ball_subset_ball (min_le_left _ _)
  refine ⟨min a1 δ, lt_min ha1 hδ, hsub.trans hroom,
    fun z hz => hW ⟨hsub hz.1, hz.2⟩, fun z0 hz0 z1 hz1 => ?_⟩
  have hdiff : ∀ z ∈ ball (0 : R3) (min a1 δ), DifferentiableAt ℝ S.separating_function z :=
    fun z hz => (S.separating_function_smooth.contDiffAt
      (S.coordinateRoom_open.mem_nhds (hroom (hsub hz)))).differentiableAt (by simp)
  have hb : ∀ z ∈ ball (0 : R3) (min a1 δ),
      ‖fderiv ℝ S.separating_function z - fderiv ℝ S.separating_function 0‖ ≤ 1/4 := by
    intro z hz
    rw [← dist_eq_norm]
    exact (H (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))).le
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le' hdiff hb (convex_ball _ _) hz0 hz1
  rw [Real.norm_eq_abs, S.separating_function_normal] at key
  have habs := le_abs_self
    (S.separating_function z1 - S.separating_function z0 - (z1 - z0) 2)
  linarith

/-- A lowered point near an ACTUAL separator anchor lies in the ORIGINAL known side. -/
theorem lowered_mem_W_of_anchor (S : KnownSideSourceData) {a : ℝ}
    (hroomW : {z ∈ ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W)
    (hmv : ∀ z0 ∈ ball (0 : R3) a, ∀ z1 ∈ ball (0 : R3) a,
      S.separating_function z1 ≤ S.separating_function z0 + (z1 - z0) 2 + (1/4) * ‖z1 - z0‖)
    {lam r h : ℝ} (hlam : 0 < lam) {p x : R3} (hp0 : S.separating_function (lam • p) = 0)
    (hxp : ‖x - p‖ < r) (hh : 5*r/3 ≤ h) (hpa : lam • p ∈ ball (0 : R3) a)
    (hxa : lam • (x - h • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ ball (0 : R3) a) :
    lam • (x - h • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ S.W := by
  have hh0 : 0 ≤ h := by linarith [norm_nonneg (x - p)]
  have h1 := hmv _ hpa _ hxa
  have hd : lam • (x - h • EuclideanSpace.single (2:Fin 3) (1:ℝ)) - lam • p =
      lam • ((x - p) - h • EuclideanSpace.single (2:Fin 3) (1:ℝ)) := by
    rw [← smul_sub, sub_right_comm]
  rw [hd, hp0] at h1
  have hcomp : (x - p) 2 ≤ ‖x - p‖ := by
    have hi := real_inner_le_norm (x - p) (EuclideanSpace.single (2:Fin 3) (1:ℝ))
    rw [EuclideanSpace.inner_single_right] at hi
    simpa using hi
  have hc : (lam • ((x - p) - h • EuclideanSpace.single (2:Fin 3) (1:ℝ))) 2 =
      lam * ((x - p) 2 - h) := by
    simp
  have hn : ‖lam • ((x - p) - h • EuclideanSpace.single (2:Fin 3) (1:ℝ))‖ ≤
      lam * (‖x - p‖ + h) := by
    rw [norm_smul, Real.norm_of_nonneg hlam.le]
    apply mul_le_mul_of_nonneg_left _ hlam.le
    calc ‖(x - p) - h • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖
        ≤ ‖x - p‖ + ‖h • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ := norm_sub_le _ _
      _ = ‖x - p‖ + h := by
        rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_of_nonneg hh0]
  rw [hc] at h1
  have e1 : lam * ((x - p) 2 - h) ≤ lam * (‖x - p‖ - h) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam.le
  have e2 : lam * (‖x - p‖ - h) + 1/4 * (lam * (‖x - p‖ + h)) =
      lam * (5*‖x - p‖ - 3*h) / 4 := by ring
  have e3 : lam * (5*‖x - p‖ - 3*h) < 0 := mul_neg_of_pos_of_neg hlam (by linarith)
  exact hroomW ⟨hxa, by linarith⟩

/-- Same-orientation retained contact with the endpoint obligation DISCHARGED from the
actual anchors and the scale-free separator descent. -/
theorem retained_same_orientation_eq_of_anchors (S : KnownSideSourceData) (L lam : ℝ)
    (hlam : 0 < lam) {a : ℝ}
    (hroomW : {z ∈ ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W)
    (hmv : ∀ z0 ∈ ball (0 : R3) a, ∀ z1 ∈ ball (0 : R3) a,
      S.separating_function z1 ≤ S.separating_function z0 + (z1 - z0) 2 + (1/4) * ‖z1 - z0‖)
    {pi pj : R3} {Ri Rj ri rj si sj : ℝ} (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj)
    (hpi0 : S.separating_function (lam • pi) = 0) (hpj0 : S.separating_function (lam • pj) = 0)
    (hpia : lam • pi ∈ ball (0 : R3) a) (hpja : lam • pj ∈ ball (0 : R3) a)
    {Fi Fj : R3 × R3 → ℝ}
    (hFi : ProductSolutionOn S L lam Fi (overlapLarge pi Ri si))
    (hFj : ProductSolutionOn S L lam Fj (overlapLarge pj Rj sj))
    (hFi2 : ∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w)
    (hFj2 : ∀ w ∈ overlapLarge pj Rj sj, lam • w.1 ∈ S.W → Fj w = dilatedKernel2 S lam w)
    {v : R3 × R3} (hvi : v ∈ overlapRetained pi ri si) (hvj : v ∈ overlapRetained pj rj sj)
    (hxa : lam • (v.1 - (6*min ri rj) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈
      ball (0 : R3) a) :
    Fi v = Fj v := by
  have hvi' : v.1 ∈ ball pi ri ∧ (19*si/20 < ‖v.2-pi‖ ∧ ‖v.2-pi‖ < 21*si/20) := hvi
  have hvj' : v.1 ∈ ball pj rj ∧ (19*sj/20 < ‖v.2-pj‖ ∧ ‖v.2-pj‖ < 21*sj/20) := hvj
  have hai : ‖v.1 - pi‖ < ri := by rw [← dist_eq_norm]; exact mem_ball.mp hvi'.1
  have haj : ‖v.1 - pj‖ < rj := by rw [← dist_eq_norm]; exact mem_ball.mp hvj'.1
  have hri : 0 ≤ ri := le_trans (norm_nonneg _) hai.le
  have hrj : 0 ≤ rj := le_trans (norm_nonneg _) haj.le
  refine retained_same_orientation_eq S L lam hRi hRj hFi hFj hFi2 hFj2 hvi hvj ?_
  rcases le_total ri rj with hle | hle
  · rw [min_eq_left hle] at hxa ⊢
    exact lowered_mem_W_of_anchor S hroomW hmv hlam hpi0 hai (by linarith) hpia hxa
  · rw [min_eq_right hle] at hxa ⊢
    exact lowered_mem_W_of_anchor S hroomW hmv hlam hpj0 haj (by linarith) hpja hxa

/-- Opposite-orientation retained contact with an ACTUAL swapped-source solution, the endpoint
obligation DISCHARGED from the actual anchor `p_i` and the scale-free separator descent. -/
theorem retained_opposite_orientation_eq_of_anchor (S : KnownSideSourceData) (L lam : ℝ)
    (hlam : 0 < lam) {a : ℝ}
    (hroomW : {z ∈ ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W)
    (hmv : ∀ z0 ∈ ball (0 : R3) a, ∀ z1 ∈ ball (0 : R3) a,
      S.separating_function z1 ≤ S.separating_function z0 + (z1 - z0) 2 + (1/4) * ‖z1 - z0‖)
    {pi pj : R3} {Ri Rj ri rj si sj : ℝ} (hRi : 20*ri ≤ Ri) (hRj : 20*rj ≤ Rj)
    (hri1 : ri ≤ si/1000) (hrj1 : rj ≤ sj/1000)
    (hpi0 : S.separating_function (lam • pi) = 0) (hpia : lam • pi ∈ ball (0 : R3) a)
    {Fi Fj : R3 × R3 → ℝ}
    (hFi : ProductSolutionOn S L lam Fi (overlapLarge pi Ri si))
    (hFi2 : ∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w)
    (hFj : ProductSolutionOn (swappedKnownSideSourceData S) L lam Fj (overlapLarge pj Rj sj))
    (hroom : overlapLarge pj Rj sj ⊆ dilatedOffDiagonal (swappedKnownSideSourceData S) lam)
    (hFj1 : ∀ w ∈ overlapLarge pj Rj sj, lam • w.2 ∈ S.W →
      Fj w = dilatedKernel1 (swappedKnownSideSourceData S) lam w)
    (hFj2 : ∀ w ∈ overlapLarge pj Rj sj, lam • w.1 ∈ S.W →
      Fj w = dilatedKernel2 (swappedKnownSideSourceData S) lam w)
    {v : R3 × R3} (hvi : v ∈ overlapRetained pi ri si)
    (hvj : Prod.swap v ∈ overlapRetained pj rj sj)
    (hxa : lam • (v.1 - (6*ri) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ ball (0 : R3) a) :
    Fi v = Fj (v.2,v.1) := by
  have hvi' : v.1 ∈ ball pi ri ∧ (19*si/20 < ‖v.2-pi‖ ∧ ‖v.2-pi‖ < 21*si/20) := hvi
  have hai : ‖v.1 - pi‖ < ri := by rw [← dist_eq_norm]; exact mem_ball.mp hvi'.1
  have hri : 0 ≤ ri := le_trans (norm_nonneg _) hai.le
  exact retained_opposite_orientation_eq_swapped S L lam hRi hRj hri1 hrj1 hFi hFi2 hFj hroom
    hFj1 hFj2 hvi hvj
    (lowered_mem_W_of_anchor S hroomW hmv hlam hpi0 hai (by linarith) hpia hxa)

/-- One `lam0`, chosen before the points, scales every bounded point into `ball 0 a`. -/
theorem exists_uniform_scaled_ball {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ z : R3, ‖z‖ ≤ B → lam • z ∈ ball (0 : R3) a := by
  refine ⟨a/(2*B), by positivity, fun lam hlam hle z hz => ?_⟩
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hlam.le]
  have h1 : lam * ‖z‖ ≤ a/(2*B) * B := mul_le_mul hle hz (norm_nonneg _) (by positivity)
  have h2 : a/(2*B) * B = a/2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hB.ne']
  linarith

/-- From an actual open annular seed around an anchor, extract the larger comparison product
and the retained radius used by the overlap-contact theorems. -/
theorem retained_product_of_open_seed (S : KnownSideSourceData) (L lam : ℝ) {C : Set R3}
    (hC : IsOpen C) {q : R3} (hq : q ∈ C) {s : ℝ} (hs : 0 < s) {K : R3 × R3 → ℝ}
    (hroom : C ×ˢ {y : R3 | 4*s/5 < ‖y-q‖ ∧ ‖y-q‖ < 6*s/5} ⊆ dilatedOffDiagonal S lam)
    (hK : ProductSolutionOn S L lam K (C ×ˢ {y : R3 | 4*s/5 < ‖y-q‖ ∧ ‖y-q‖ < 6*s/5}))
    (hK1 : ∀ v ∈ C ×ˢ {y : R3 | 4*s/5 < ‖y-q‖ ∧ ‖y-q‖ < 6*s/5},
      lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v)
    (hK2 : ∀ v ∈ C ×ˢ {y : R3 | 4*s/5 < ‖y-q‖ ∧ ‖y-q‖ < 6*s/5},
      lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ 20*r ≤ R ∧ r ≤ s/1000 ∧
      overlapLarge q R s ⊆ dilatedOffDiagonal S lam ∧
      ProductSolutionOn S L lam K (overlapLarge q R s) ∧
      (∀ v ∈ overlapLarge q R s, lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ overlapLarge q R s, lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hC q hq
  have hsub : overlapLarge q R s ⊆ C ×ˢ {y : R3 | 4*s/5 < ‖y-q‖ ∧ ‖y-q‖ < 6*s/5} :=
    Set.prod_mono hball subset_rfl
  have hmin := min_le_left (R/20) (s/1000)
  refine ⟨R, min (R/20) (s/1000), hR, lt_min (by positivity) (by positivity), by linarith,
    min_le_right _ _, hsub.trans hroom, productSolutionOn_mono hK hsub,
    fun v hv => hK1 v (hsub hv), fun v hv => hK2 v (hsub hv)⟩

/-- A kernel with BOTH full original lower-cross identities equals the original initial
kernel on the original known cross. -/
theorem retained_eq_initialKernel (S : KnownSideSourceData) (lam : ℝ) {U : Set (R3 × R3)}
    {K : R3 × R3 → ℝ}
    (hK1 : ∀ v ∈ U, lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v)
    (hK2 : ∀ v ∈ U, lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) :
    EqOn K (initialKernel S lam) (U ∩ initialCross S lam) := by
  intro v hv
  have hc : lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W := hv.2.2
  by_cases h2 : lam • v.2 ∈ S.W
  · rw [hK1 v hv.1 h2]
    unfold initialKernel
    rw [if_pos h2]
  · rw [hK2 v hv.1 (hc.resolve_right h2)]
    unfold initialKernel
    rw [if_neg h2]

/-- ACTUAL retained products at ACTUAL separator anchors from the checked anchored kernel,
with one `lam0` chosen before `L`, `lam`, `p`, `s`. -/
theorem initial_retained_kernel_anchor (S : KnownSideSourceData) (B s0 s1 : ℝ) (hB : 0 < B)
    (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 →
      ∀ s ∈ Set.Icc s0 s1, ∃ t ∈ Set.Ioo (-(s0/4)) (s0/4),
        S.separating_function (lam • (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 ∧
      ∃ (R r : ℝ) (K : R3 × R3 → ℝ), 0 < R ∧ 0 < r ∧ 20*r ≤ R ∧ r ≤ s/1000 ∧
        overlapLarge (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) R s ⊆
          dilatedOffDiagonal S lam ∧
        ProductSolutionOn S L lam K
          (overlapLarge (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) R s) ∧
        (∀ v ∈ overlapLarge (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) R s,
          lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ overlapLarge (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) R s,
          lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) := by
  obtain ⟨lam0, hlam0, H⟩ := initial_full_cross_kernel_anchor S B s0 s1 hB hs0 hss
  refine ⟨lam0, hlam0, fun L lam hlam hle p hp hp2 s hs => ?_⟩
  obtain ⟨t, ht, hsep, C, K, hCo, -, hq, -, hroom, hK, hK1, hK2⟩ :=
    H L lam hlam hle p hp hp2 s hs
  obtain ⟨R, r, hR, hr, h20, hrs, hroom', hK', hK1', hK2'⟩ :=
    retained_product_of_open_seed S L lam hCo hq (hs0.trans_le hs.1) hroom hK hK1 hK2
  exact ⟨t, ht, hsep, R, r, K, hR, hr, h20, hrs, hroom', hK', hK1', hK2'⟩

/-- The scale-free descent ball of the ORIGINAL separator together with one `lam0`, chosen
before `lam` and all points, scaling every point of norm at most `B` into it. -/
theorem exists_uniform_descent_room (S : KnownSideSourceData) (B : ℝ) (hB : 0 < B) :
    ∃ a lam0 : ℝ, 0 < a ∧ 0 < lam0 ∧
      {z ∈ ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W ∧
      (∀ z0 ∈ ball (0 : R3) a, ∀ z1 ∈ ball (0 : R3) a,
        S.separating_function z1 ≤ S.separating_function z0 + (z1 - z0) 2 + (1/4) * ‖z1 - z0‖) ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ z : R3, ‖z‖ ≤ B → lam • z ∈ ball (0 : R3) a := by
  obtain ⟨a, ha, -, hW, hmv⟩ := exists_separator_descent_ball S
  obtain ⟨lam0, hl, H⟩ := exists_uniform_scaled_ball ha hB
  exact ⟨a, lam0, ha, hl, hW, hmv, H⟩

/-- Same-orientation retained contact with ONE `lam0` chosen before `L`, `lam`, the actual
anchors, radii and kernels: equality on the ENTIRE retained overlap. -/
theorem uniform_retained_same_orientation_contact (S : KnownSideSourceData) (B s1 : ℝ)
    (hB : 0 < B) (hs1 : 0 < s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ (pi pj : R3) (Ri Rj ri rj si sj : ℝ), ‖pi‖ ≤ B → ‖pj‖ ≤ B →
      S.separating_function (lam • pi) = 0 → S.separating_function (lam • pj) = 0 →
      20*ri ≤ Ri → 20*rj ≤ Rj → ri ≤ s1 → rj ≤ s1 →
      ∀ Fi Fj : R3 × R3 → ℝ,
      ProductSolutionOn S L lam Fi (overlapLarge pi Ri si) →
      ProductSolutionOn S L lam Fj (overlapLarge pj Rj sj) →
      (∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w) →
      (∀ w ∈ overlapLarge pj Rj sj, lam • w.1 ∈ S.W → Fj w = dilatedKernel2 S lam w) →
      EqOn Fi Fj (overlapRetained pi ri si ∩ overlapRetained pj rj sj) := by
  obtain ⟨a, lam0, ha, hl, hW, hmv, H⟩ := exists_uniform_descent_room S (B + 7*s1) (by positivity)
  refine ⟨lam0, hl, fun L lam hlam hle pi pj Ri Rj ri rj si sj hpi hpj hpi0 hpj0 hRi hRj
    hri1 hrj1 Fi Fj hFi hFj hFi2 hFj2 v hv => ?_⟩
  have hvi' : v.1 ∈ ball pi ri ∧ (19*si/20 < ‖v.2-pi‖ ∧ ‖v.2-pi‖ < 21*si/20) := hv.1
  have hai : ‖v.1 - pi‖ < ri := by rw [← dist_eq_norm]; exact mem_ball.mp hvi'.1
  have hri : 0 ≤ ri := le_trans (norm_nonneg _) hai.le
  have hv1 : ‖v.1‖ ≤ ‖v.1 - pi‖ + ‖pi‖ := by
    have h := norm_add_le (v.1 - pi) pi
    rwa [sub_add_cancel] at h
  have hm0 : 0 ≤ 6*min ri rj := by
    have hrj : 0 ≤ rj := by
      have hvj' : v.1 ∈ ball pj rj ∧ (19*sj/20 < ‖v.2-pj‖ ∧ ‖v.2-pj‖ < 21*sj/20) := hv.2
      exact le_trans dist_nonneg (mem_ball.mp hvj'.1).le
    have := le_min hri hrj
    linarith
  have hm6 : 6*min ri rj ≤ 6*ri := by linarith [min_le_left ri rj]
  have hlow : ‖v.1 - (6*min ri rj) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ ≤ B + 7*s1 := by
    have h1 := norm_sub_le v.1 ((6*min ri rj) • EuclideanSpace.single (2:Fin 3) (1:ℝ))
    have h2 : ‖(6*min ri rj) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ = 6*min ri rj := by
      rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_of_nonneg hm0]
    linarith
  exact retained_same_orientation_eq_of_anchors S L lam hlam hW hmv hRi hRj hpi0 hpj0
    (H lam hlam hle pi (by linarith)) (H lam hlam hle pj (by linarith))
    hFi hFj hFi2 hFj2 hv.1 hv.2 (H lam hlam hle _ hlow)

/-- Opposite-orientation retained contact with ONE `lam0` chosen before `L`, `lam`, the actual
anchor, radii and kernels, against an ACTUAL swapped-source solution. -/
theorem uniform_retained_opposite_orientation_contact (S : KnownSideSourceData) (B s1 : ℝ)
    (hB : 0 < B) (hs1 : 0 < s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ (pi pj : R3) (Ri Rj ri rj si sj : ℝ), ‖pi‖ ≤ B →
      S.separating_function (lam • pi) = 0 →
      20*ri ≤ Ri → 20*rj ≤ Rj → ri ≤ si/1000 → rj ≤ sj/1000 → ri ≤ s1 →
      ∀ Fi Fj : R3 × R3 → ℝ,
      ProductSolutionOn S L lam Fi (overlapLarge pi Ri si) →
      (∀ w ∈ overlapLarge pi Ri si, lam • w.1 ∈ S.W → Fi w = dilatedKernel2 S lam w) →
      ProductSolutionOn (swappedKnownSideSourceData S) L lam Fj (overlapLarge pj Rj sj) →
      overlapLarge pj Rj sj ⊆ dilatedOffDiagonal (swappedKnownSideSourceData S) lam →
      (∀ w ∈ overlapLarge pj Rj sj, lam • w.2 ∈ S.W →
        Fj w = dilatedKernel1 (swappedKnownSideSourceData S) lam w) →
      (∀ w ∈ overlapLarge pj Rj sj, lam • w.1 ∈ S.W →
        Fj w = dilatedKernel2 (swappedKnownSideSourceData S) lam w) →
      ∀ v : R3 × R3, v ∈ overlapRetained pi ri si → Prod.swap v ∈ overlapRetained pj rj sj →
        Fi v = Fj (v.2,v.1) := by
  obtain ⟨a, lam0, ha, hl, hW, hmv, H⟩ := exists_uniform_descent_room S (B + 7*s1) (by positivity)
  refine ⟨lam0, hl, fun L lam hlam hle pi pj Ri Rj ri rj si sj hpi hpi0 hRi hRj hri1 hrj1
    hris1 Fi Fj hFi hFi2 hFj hroom hFj1 hFj2 v hvi hvj => ?_⟩
  have hvi' : v.1 ∈ ball pi ri ∧ (19*si/20 < ‖v.2-pi‖ ∧ ‖v.2-pi‖ < 21*si/20) := hvi
  have hai : ‖v.1 - pi‖ < ri := by rw [← dist_eq_norm]; exact mem_ball.mp hvi'.1
  have hri : 0 ≤ ri := le_trans (norm_nonneg _) hai.le
  have hv1 : ‖v.1‖ ≤ ‖v.1 - pi‖ + ‖pi‖ := by
    have h := norm_add_le (v.1 - pi) pi
    rwa [sub_add_cancel] at h
  have hlow : ‖v.1 - (6*ri) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ ≤ B + 7*s1 := by
    have h1 := norm_sub_le v.1 ((6*ri) • EuclideanSpace.single (2:Fin 3) (1:ℝ))
    have h2 : ‖(6*ri) • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ = 6*ri := by
      rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
        Real.norm_of_nonneg (by linarith)]
    linarith
  exact retained_opposite_orientation_eq_of_anchor S L lam hlam hW hmv hRi hRj hri1 hrj1 hpi0
    (H lam hlam hle pi (by linarith)) hFi hFi2 hFj hroom hFj1 hFj2 hvi hvj
    (H lam hlam hle _ hlow)

/-- ACTUAL retained initial kernels at ACTUAL anchors agree with every bounded-anchor retained
solution on the entire same-orientation retained overlap; one `lam0` before `L,lam,p,s`. -/
theorem actual_retained_same_orientation_pairwise (S : KnownSideSourceData) (B s0 s1 : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 → ∀ s ∈ Set.Icc s0 s1,
      ∃ (q : R3) (R r : ℝ) (K : R3 × R3 → ℝ),
        S.separating_function (lam • q) = 0 ∧ ‖q - p‖ < s0/4 ∧ 0 < r ∧ 20*r ≤ R ∧
        r ≤ s/1000 ∧ ProductSolutionOn S L lam K (overlapLarge q R s) ∧
        (∀ v ∈ overlapLarge q R s, lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ overlapLarge q R s, lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) ∧
        ∀ (q' : R3) (R' r' s' : ℝ) (K' : R3 × R3 → ℝ), ‖q'‖ ≤ B + s0 →
          S.separating_function (lam • q') = 0 → 20*r' ≤ R' → r' ≤ s1 →
          ProductSolutionOn S L lam K' (overlapLarge q' R' s') →
          (∀ w ∈ overlapLarge q' R' s', lam • w.1 ∈ S.W → K' w = dilatedKernel2 S lam w) →
          EqOn K K' (overlapRetained q r s ∩ overlapRetained q' r' s') := by
  obtain ⟨lamI, hlI, HI⟩ := initial_retained_kernel_anchor S B s0 s1 hB hs0 hss
  obtain ⟨lamC, hlC, HC⟩ :=
    uniform_retained_same_orientation_contact S (B + s0) s1 (by positivity) (hs0.trans_le hss)
  refine ⟨min lamI lamC, lt_min hlI hlC, fun L lam hlam hle p hp hp2 s hs => ?_⟩
  obtain ⟨t, ht, hsep, R, r, K, hR, hr, h20, hrs, hroom, hK, hK1, hK2⟩ :=
    HI L lam hlam (hle.trans (min_le_left _ _)) p hp hp2 s hs
  have hq : ‖(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - p‖ < s0/4 := by
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_lt]
    exact ht
  have hqn : ‖p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B + s0 := by
    have h := norm_sub_norm_le (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p
    linarith
  have hrs1 : r ≤ s1 := by linarith [hs.1, hs.2]
  refine ⟨p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ), R, r, K, hsep, hq, hr, h20, hrs,
    hK, hK1, hK2, fun q' R' r' s' K' hq' hsep' h20' hr' hK' hK2' => ?_⟩
  exact HC L lam hlam (hle.trans (min_le_right _ _)) _ q' R R' r r' s s' hqn hq' hsep hsep'
    h20 h20' hrs1 hr' K K' hK hK' hK2 hK2'

/-- ACTUAL retained initial kernels agree with the transpose of every actual swapped-source
retained solution on the entire opposite-orientation retained overlap. -/
theorem actual_retained_opposite_orientation_pairwise (S : KnownSideSourceData) (B s0 s1 : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 → ∀ s ∈ Set.Icc s0 s1,
      ∃ (q : R3) (R r : ℝ) (K : R3 × R3 → ℝ),
        S.separating_function (lam • q) = 0 ∧ ‖q - p‖ < s0/4 ∧ 0 < r ∧ 20*r ≤ R ∧
        r ≤ s/1000 ∧ ProductSolutionOn S L lam K (overlapLarge q R s) ∧
        (∀ v ∈ overlapLarge q R s, lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ overlapLarge q R s, lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) ∧
        ∀ (q' : R3) (R' r' s' : ℝ) (K' : R3 × R3 → ℝ), 20*r' ≤ R' → r' ≤ s'/1000 →
          ProductSolutionOn (swappedKnownSideSourceData S) L lam K' (overlapLarge q' R' s') →
          overlapLarge q' R' s' ⊆ dilatedOffDiagonal (swappedKnownSideSourceData S) lam →
          (∀ w ∈ overlapLarge q' R' s', lam • w.2 ∈ S.W →
            K' w = dilatedKernel1 (swappedKnownSideSourceData S) lam w) →
          (∀ w ∈ overlapLarge q' R' s', lam • w.1 ∈ S.W →
            K' w = dilatedKernel2 (swappedKnownSideSourceData S) lam w) →
          ∀ v : R3 × R3, v ∈ overlapRetained q r s → Prod.swap v ∈ overlapRetained q' r' s' →
            K v = K' (v.2,v.1) := by
  obtain ⟨lamI, hlI, HI⟩ := initial_retained_kernel_anchor S B s0 s1 hB hs0 hss
  obtain ⟨lamC, hlC, HC⟩ :=
    uniform_retained_opposite_orientation_contact S (B + s0) s1 (by positivity)
      (hs0.trans_le hss)
  refine ⟨min lamI lamC, lt_min hlI hlC, fun L lam hlam hle p hp hp2 s hs => ?_⟩
  obtain ⟨t, ht, hsep, R, r, K, hR, hr, h20, hrs, hroom, hK, hK1, hK2⟩ :=
    HI L lam hlam (hle.trans (min_le_left _ _)) p hp hp2 s hs
  have hq : ‖(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - p‖ < s0/4 := by
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_lt]
    exact ht
  have hqn : ‖p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B + s0 := by
    have h := norm_sub_norm_le (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p
    linarith
  have hrs1 : r ≤ s1 := by linarith [hs.1, hs.2]
  refine ⟨p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ), R, r, K, hsep, hq, hr, h20, hrs,
    hK, hK1, hK2, fun q' R' r' s' K' h20' hr' hK' hroom' hK1' hK2' v hvi hvj => ?_⟩
  exact HC L lam hlam (hle.trans (min_le_right _ _)) _ q' R R' r r' s s' hqn hsep h20 h20'
    hrs hr' hrs1 K K' hK hK2 hK' hroom' hK1' hK2' v hvi hvj

theorem isOpen_overlapRetained (p : R3) (r s : ℝ) : IsOpen (overlapRetained p r s) := by
  have h1 : IsOpen {y : R3 | 19*s/20 < ‖y-p‖} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {y : R3 | ‖y-p‖ < 21*s/20} := isOpen_lt (by fun_prop) continuous_const
  exact isOpen_ball.prod (h1.inter h2)

theorem overlapRetained_subset_large {p : R3} {r R s : ℝ} (hrR : r ≤ R) :
    overlapRetained p r s ⊆ overlapLarge p R s :=
  fun _ hv => ⟨ball_subset_ball hrR hv.1, retained_annulus_mem_large hv.2⟩

/-- Glue the ORIGINAL initial cross with a family of actual retained products through the
EXISTING checked `exists_productSolutionOn_iUnion` (index `Option ι`, `none` = initial cross). -/
theorem glued_initialCross_retained (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    {ι : Type*} (q : ι → R3) (R r s : ι → ℝ) (K : ι → R3 × R3 → ℝ)
    (hrR : ∀ i, r i ≤ R i)
    (hroom : ∀ i, overlapLarge (q i) (R i) (s i) ⊆ dilatedOffDiagonal S lam)
    (hK : ∀ i, ProductSolutionOn S L lam (K i) (overlapLarge (q i) (R i) (s i)))
    (hK1 : ∀ i, ∀ v ∈ overlapLarge (q i) (R i) (s i), lam • v.2 ∈ S.W →
      K i v = dilatedKernel1 S lam v)
    (hK2 : ∀ i, ∀ v ∈ overlapLarge (q i) (R i) (s i), lam • v.1 ∈ S.W →
      K i v = dilatedKernel2 S lam v)
    (hcompat : ∀ i j, EqOn (K i) (K j)
      (overlapRetained (q i) (r i) (s i) ∩ overlapRetained (q j) (r j) (s j))) :
    ∃ H : R3 × R3 → ℝ,
      IsOpen (initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i)) ∧
      initialCross S lam ∪ (⋃ i, overlapRetained (q i) (r i) (s i)) ⊆ dilatedOffDiagonal S lam ∧
      ProductSolutionOn S L lam H (initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i)) ∧
      EqOn H (initialKernel S lam) (initialCross S lam) ∧
      (∀ i, EqOn H (K i) (overlapRetained (q i) (r i) (s i))) ∧
      (∀ v ∈ initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i),
        lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i),
        lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) := by
  obtain ⟨hIo, hIsol, hI1, hI2⟩ := v021_initial_cross_product S L lam hlam
  let U : Option ι → Set (R3 × R3) := fun o => o.elim (initialCross S lam)
    (fun i => overlapRetained (q i) (r i) (s i))
  let F : Option ι → R3 × R3 → ℝ := fun o => o.elim (initialKernel S lam) K
  have hsub : ∀ i, overlapRetained (q i) (r i) (s i) ⊆ overlapLarge (q i) (R i) (s i) :=
    fun i => overlapRetained_subset_large (hrR i)
  have hUo : ∀ o, IsOpen (U o) := by
    rintro (_ | i)
    · exact hIo
    · exact isOpen_overlapRetained _ _ _
  have hF : ∀ o, ProductSolutionOn S L lam (F o) (U o) := by
    rintro (_ | i)
    · exact hIsol
    · exact productSolutionOn_mono (hK i) (hsub i)
  have hIK : ∀ i, EqOn (K i) (initialKernel S lam)
      (overlapRetained (q i) (r i) (s i) ∩ initialCross S lam) :=
    fun i v hv => retained_eq_initialKernel S lam (hK1 i) (hK2 i) ⟨hsub i hv.1, hv.2⟩
  have hcomp : ∀ o o', EqOn (F o) (F o') (U o ∩ U o') := by
    rintro (_ | i) (_ | j) v hv
    · rfl
    · exact (hIK j ⟨hv.2, hv.1⟩).symm
    · exact hIK i hv
    · exact hcompat i j hv
  obtain ⟨H, hH, hHe⟩ := exists_productSolutionOn_iUnion S L lam U hUo F hF hcomp
  have hUeq : (⋃ o, U o) = initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i) := by
    ext v
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨_ | i, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨i, hv⟩
    · rintro (hv | ⟨i, hv⟩)
      · exact ⟨none, hv⟩
      · exact ⟨some i, hv⟩
  have hHI : EqOn H (initialKernel S lam) (initialCross S lam) := hHe none
  have hHK : ∀ i, EqOn H (K i) (overlapRetained (q i) (r i) (s i)) := fun i => hHe (some i)
  refine ⟨H, hIo.union (isOpen_iUnion fun i => isOpen_overlapRetained _ _ _), ?_,
    by rw [← hUeq]; exact hH, hHI, hHK, ?_, ?_⟩
  · rintro v (hv | hv)
    · exact hv.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      exact hroom i (hsub i hi)
  · rintro v (hv | hv) hW
    · rw [hHI hv]; exact hI1 v hv hW
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rw [hHK i hi]; exact hK1 i v (hsub i hi) hW
  · rintro v (hv | hv) hW
    · rw [hHI hv]; exact hI2 v hv hW
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rw [hHK i hi]; exact hK2 i v (hsub i hi) hW

/-- Gluing with pairwise compatibility DISCHARGED by the actual same-orientation contact, one
`lam0` chosen before `L`, `lam`, the index family, anchors, radii and kernels. -/
theorem uniform_glued_initialCross_retained (S : KnownSideSourceData) (B s1 : ℝ)
    (hB : 0 < B) (hs1 : 0 < s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ (ι : Type) (q : ι → R3) (R r s : ι → ℝ) (K : ι → R3 × R3 → ℝ),
      (∀ i, ‖q i‖ ≤ B) → (∀ i, S.separating_function (lam • q i) = 0) →
      (∀ i, 0 < r i) → (∀ i, 20 * r i ≤ R i) → (∀ i, r i ≤ s1) →
      (∀ i, overlapLarge (q i) (R i) (s i) ⊆ dilatedOffDiagonal S lam) →
      (∀ i, ProductSolutionOn S L lam (K i) (overlapLarge (q i) (R i) (s i))) →
      (∀ i, ∀ v ∈ overlapLarge (q i) (R i) (s i), lam • v.2 ∈ S.W →
        K i v = dilatedKernel1 S lam v) →
      (∀ i, ∀ v ∈ overlapLarge (q i) (R i) (s i), lam • v.1 ∈ S.W →
        K i v = dilatedKernel2 S lam v) →
      ∃ H : R3 × R3 → ℝ,
        IsOpen (initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i)) ∧
        initialCross S lam ∪ (⋃ i, overlapRetained (q i) (r i) (s i)) ⊆
          dilatedOffDiagonal S lam ∧
        ProductSolutionOn S L lam H
          (initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i)) ∧
        EqOn H (initialKernel S lam) (initialCross S lam) ∧
        (∀ i, EqOn H (K i) (overlapRetained (q i) (r i) (s i))) ∧
        (∀ v ∈ initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i),
          lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ initialCross S lam ∪ ⋃ i, overlapRetained (q i) (r i) (s i),
          lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) := by
  obtain ⟨lam0, hl, HC⟩ := uniform_retained_same_orientation_contact S B s1 hB hs1
  refine ⟨lam0, hl, fun L lam hlam hle ι q R r s K hq hsep hr h20 hrs hroom hK hK1 hK2 => ?_⟩
  exact glued_initialCross_retained S L lam hlam q R r s K
    (fun i => by linarith [hr i, h20 i]) hroom hK hK1 hK2
    (fun i j => HC L lam hlam hle (q i) (q j) (R i) (R j) (r i) (r j) (s i) (s j) (hq i) (hq j)
      (hsep i) (hsep j) (h20 i) (h20 j) (hrs i) (hrs j) (K i) (K j) (hK i) (hK j)
      (hK2 i) (hK2 j))

/-- Index of the actual anchored initializer: bounded base points on the plane and
separations in `[s0,s1]`. -/
abbrev anchorIndex (B s0 s1 : ℝ) : Type :=
  {ps : R3 × ℝ // ‖ps.1‖ ≤ B ∧ ps.1 2 = 0 ∧ ps.2 ∈ Set.Icc s0 s1}

/-- ACTUAL union seed: the original initial cross glued with the ACTUAL retained kernels chosen
from the native anchored initializer at EVERY bounded base point and separation; one `lam0`
before `L`, `lam`. Each actual anchor's retained annular product lies in the seed domain. -/
theorem actual_initial_retained_union_kernel (S : KnownSideSourceData) (B s0 s1 : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧ initialCross S lam ⊆ U ∧
        U ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam H U ∧
        EqOn H (initialKernel S lam) (initialCross S lam) ∧
        (∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
        ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 → ∀ s ∈ Set.Icc s0 s1, ∃ (q : R3) (r : ℝ),
          S.separating_function (lam • q) = 0 ∧ ‖q - p‖ < s0/4 ∧ 0 < r ∧ r ≤ s/1000 ∧
          overlapRetained q r s ⊆ U := by
  obtain ⟨lamI, hlI, HI⟩ := initial_retained_kernel_anchor S B s0 s1 hB hs0 hss
  obtain ⟨lamC, hlC, HC⟩ :=
    uniform_glued_initialCross_retained S (B + s0) s1 (by positivity) (hs0.trans_le hss)
  refine ⟨min lamI lamC, lt_min hlI hlC, fun L lam hlam hle => ?_⟩
  have hex := fun i : anchorIndex B s0 s1 =>
    HI L lam hlam (hle.trans (min_le_left _ _)) i.1.1 i.2.1 i.2.2.1 i.1.2 i.2.2.2
  choose t ht hsep R r K hR hr h20 hrs hroom hK hK1 hK2 using hex
  let q : anchorIndex B s0 s1 → R3 := fun i =>
    i.1.1 + t i • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hqp : ∀ i, ‖q i - i.1.1‖ < s0/4 := fun i => by
    show ‖(i.1.1 + t i • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - i.1.1‖ < s0/4
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_lt]
    exact ht i
  have hqn : ∀ i, ‖q i‖ ≤ B + s0 := fun i => by
    have h := norm_sub_norm_le (q i) i.1.1
    linarith [hqp i, i.2.1]
  have hrs1 : ∀ i, r i ≤ s1 := fun i => by
    linarith [hrs i, i.2.2.2.1, i.2.2.2.2]
  obtain ⟨H, hUo, hUroom, hHsol, hHI, -, hH1, hH2⟩ :=
    HC L lam hlam (hle.trans (min_le_right _ _)) (anchorIndex B s0 s1) q R r
      (fun i => i.1.2) K hqn hsep hr h20 hrs1 hroom hK hK1 hK2
  refine ⟨_, H, hUo, subset_union_left, hUroom, hHsol, hHI, hH1, hH2,
    fun p hp hp2 s hs => ?_⟩
  let i : anchorIndex B s0 s1 := ⟨(p, s), hp, hp2, hs⟩
  exact ⟨q i, r i, hsep i, hqp i, hr i, hrs i, fun v hv => Or.inr (mem_iUnion.mpr ⟨i, hv⟩)⟩

/-- ACTUAL two-orientation common seed: the original initial cross glued, through the EXISTING
`exists_productSolutionOn_iUnion`, with the actual retained kernels of BOTH `S` and the swapped
source (transposed), one `lam0` before `L`, `lam`; the exact family and agreements retained. -/
theorem actual_two_orientation_union_kernel (S : KnownSideSourceData) (B s0 s1 : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (q q' : anchorIndex B s0 s1 → R3) (R r R' r' : anchorIndex B s0 s1 → ℝ)
        (K K' : anchorIndex B s0 s1 → R3 × R3 → ℝ) (U : Set (R3 × R3)) (H : R3 × R3 → ℝ),
        (∀ i, S.separating_function (lam • q i) = 0 ∧ ‖q i - i.1.1‖ < s0/4 ∧ 0 < r i ∧
          20 * r i ≤ R i ∧ r i ≤ i.1.2/1000 ∧
          overlapLarge (q i) (R i) i.1.2 ⊆ dilatedOffDiagonal S lam ∧
          ProductSolutionOn S L lam (K i) (overlapLarge (q i) (R i) i.1.2) ∧
          ∃ c ∈ Set.Ioo (-(s0/4)) (s0/4),
            q i = i.1.1 + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) ∧
        (∀ j, S.separating_function (lam • q' j) = 0 ∧ ‖q' j - j.1.1‖ < s0/4 ∧ 0 < r' j ∧
          20 * r' j ≤ R' j ∧ r' j ≤ j.1.2/1000 ∧
          overlapLarge (q' j) (R' j) j.1.2 ⊆ dilatedOffDiagonal S lam ∧
          ProductSolutionOn (swappedKnownSideSourceData S) L lam (K' j)
            (overlapLarge (q' j) (R' j) j.1.2) ∧
          ∃ c ∈ Set.Ioo (-(s0/4)) (s0/4),
            q' j = j.1.1 + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) ∧
        U = initialCross S lam ∪ ((⋃ i, overlapRetained (q i) (r i) i.1.2) ∪
          ⋃ j, Prod.swap ⁻¹' overlapRetained (q' j) (r' j) j.1.2) ∧
        IsOpen U ∧ U ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam H U ∧
        EqOn H (initialKernel S lam) (initialCross S lam) ∧
        (∀ i, EqOn H (K i) (overlapRetained (q i) (r i) i.1.2)) ∧
        (∀ j, EqOn H (fun v => K' j (v.2,v.1))
          (Prod.swap ⁻¹' overlapRetained (q' j) (r' j) j.1.2)) ∧
        (∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) := by
  obtain ⟨lamI, hlI, HI⟩ := initial_retained_kernel_anchor S B s0 s1 hB hs0 hss
  obtain ⟨lamJ, hlJ, HJ⟩ :=
    initial_retained_kernel_anchor (swappedKnownSideSourceData S) B s0 s1 hB hs0 hss
  obtain ⟨lamA, hlA, HA⟩ :=
    uniform_retained_same_orientation_contact S (B + s0) s1 (by positivity) (hs0.trans_le hss)
  obtain ⟨lamB, hlB, HB⟩ := uniform_retained_same_orientation_contact
    (swappedKnownSideSourceData S) (B + s0) s1 (by positivity) (hs0.trans_le hss)
  obtain ⟨lamC, hlC, HC⟩ :=
    uniform_retained_opposite_orientation_contact S (B + s0) s1 (by positivity)
      (hs0.trans_le hss)
  refine ⟨min (min lamI lamJ) (min lamA (min lamB lamC)),
    lt_min (lt_min hlI hlJ) (lt_min hlA (lt_min hlB hlC)), fun L lam hlam hle => ?_⟩
  have hI : lam ≤ lamI := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hJ : lam ≤ lamJ := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hA : lam ≤ lamA := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB' : lam ≤ lamB :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hC : lam ≤ lamC :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hIo, hIsol, hI1, hI2⟩ := v021_initial_cross_product S L lam hlam
  have hex := fun i : anchorIndex B s0 s1 =>
    HI L lam hlam hI i.1.1 i.2.1 i.2.2.1 i.1.2 i.2.2.2
  choose t ht hsep R r K hR hr h20 hrs hroom hK hK1 hK2 using hex
  have hex' := fun j : anchorIndex B s0 s1 =>
    HJ L lam hlam hJ j.1.1 j.2.1 j.2.2.1 j.1.2 j.2.2.2
  choose t' ht' hsep' R' r' K' hR' hr' h20' hrs' hroom' hK' hK1' hK2' using hex'
  let q : anchorIndex B s0 s1 → R3 := fun i =>
    i.1.1 + t i • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let q' : anchorIndex B s0 s1 → R3 := fun j =>
    j.1.1 + t' j • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hqp : ∀ i, ‖q i - i.1.1‖ < s0/4 := fun i => by
    show ‖(i.1.1 + t i • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - i.1.1‖ < s0/4
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_lt]
    exact ht i
  have hqp' : ∀ j, ‖q' j - j.1.1‖ < s0/4 := fun j => by
    show ‖(j.1.1 + t' j • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - j.1.1‖ < s0/4
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_lt]
    exact ht' j
  have hqn : ∀ i, ‖q i‖ ≤ B + s0 := fun i => by
    have h := norm_sub_norm_le (q i) i.1.1
    linarith [hqp i, i.2.1]
  have hqn' : ∀ j, ‖q' j‖ ≤ B + s0 := fun j => by
    have h := norm_sub_norm_le (q' j) j.1.1
    linarith [hqp' j, j.2.1]
  have hrs1 : ∀ i, r i ≤ s1 := fun i => by
    linarith [hrs i, i.2.2.2.1, i.2.2.2.2]
  have hrs1' : ∀ j, r' j ≤ s1 := fun j => by
    linarith [hrs' j, j.2.2.2.1, j.2.2.2.2]
  have hsub : ∀ i, overlapRetained (q i) (r i) i.1.2 ⊆ overlapLarge (q i) (R i) i.1.2 :=
    fun i => overlapRetained_subset_large (by linarith [hr i, h20 i])
  have hsub' : ∀ j, overlapRetained (q' j) (r' j) j.1.2 ⊆ overlapLarge (q' j) (R' j) j.1.2 :=
    fun j => overlapRetained_subset_large (by linarith [hr' j, h20' j])
  have hT := fun j => full_lower_crosses_of_swapped_source S lam (hroom' j) (hK1' j) (hK2' j)
  have hroomT : ∀ j, ∀ v ∈ Prod.swap ⁻¹' overlapLarge (q' j) (R' j) j.1.2,
      v ∈ dilatedOffDiagonal S lam := fun j v hv => by
    have hh : lam • v.2 ∈ S.coordinateRoom ∧ lam • v.1 ∈ S.coordinateRoom ∧ v.2 ≠ v.1 :=
      hroom' j hv
    exact ⟨hh.2.1, hh.1, fun h => hh.2.2 h.symm⟩
  let A := anchorIndex B s0 s1
  let Uf : Option (A ⊕ A) → Set (R3 × R3) := fun o => o.elim (initialCross S lam)
    (Sum.elim (fun i => overlapRetained (q i) (r i) i.1.2)
      (fun j => Prod.swap ⁻¹' overlapRetained (q' j) (r' j) j.1.2))
  let F : Option (A ⊕ A) → R3 × R3 → ℝ := fun o => o.elim (initialKernel S lam)
    (Sum.elim K (fun j v => K' j (v.2,v.1)))
  have hUo : ∀ o, IsOpen (Uf o) := by
    rintro (_ | i | j)
    · exact hIo
    · exact isOpen_overlapRetained _ _ _
    · exact (isOpen_overlapRetained _ _ _).preimage continuous_swap
  have hF : ∀ o, ProductSolutionOn S L lam (F o) (Uf o) := by
    rintro (_ | i | j)
    · exact hIsol
    · exact productSolutionOn_mono (hK i) (hsub i)
    · exact productSolutionOn_of_swapped_source S L lam
        (productSolutionOn_mono (hK' j) (hsub' j))
  have hIK : ∀ i, EqOn (K i) (initialKernel S lam)
      (overlapRetained (q i) (r i) i.1.2 ∩ initialCross S lam) :=
    fun i v hv => retained_eq_initialKernel S lam (hK1 i) (hK2 i) ⟨hsub i hv.1, hv.2⟩
  have hIK' : ∀ j, EqOn (fun v : R3 × R3 => K' j (v.2,v.1)) (initialKernel S lam)
      (Prod.swap ⁻¹' overlapRetained (q' j) (r' j) j.1.2 ∩ initialCross S lam) :=
    fun j v hv => retained_eq_initialKernel S lam (hT j).1 (hT j).2 ⟨hsub' j hv.1, hv.2⟩
  have hSS : ∀ i i', EqOn (K i) (K i')
      (overlapRetained (q i) (r i) i.1.2 ∩ overlapRetained (q i') (r i') i'.1.2) :=
    fun i i' => HA L lam hlam hA (q i) (q i') (R i) (R i') (r i) (r i') i.1.2 i'.1.2
      (hqn i) (hqn i') (hsep i) (hsep i') (h20 i) (h20 i') (hrs1 i) (hrs1 i') (K i) (K i')
      (hK i) (hK i') (hK2 i) (hK2 i')
  have hTT : ∀ j j', EqOn (K' j) (K' j')
      (overlapRetained (q' j) (r' j) j.1.2 ∩ overlapRetained (q' j') (r' j') j'.1.2) :=
    fun j j' => HB L lam hlam hB' (q' j) (q' j') (R' j) (R' j') (r' j) (r' j') j.1.2 j'.1.2
      (hqn' j) (hqn' j') (hsep' j) (hsep' j') (h20' j) (h20' j') (hrs1' j) (hrs1' j')
      (K' j) (K' j') (hK' j) (hK' j') (hK2' j) (hK2' j')
  have hST : ∀ i j, ∀ v : R3 × R3, v ∈ overlapRetained (q i) (r i) i.1.2 →
      Prod.swap v ∈ overlapRetained (q' j) (r' j) j.1.2 → K i v = K' j (v.2,v.1) :=
    fun i j => HC L lam hlam hC (q i) (q' j) (R i) (R' j) (r i) (r' j) i.1.2 j.1.2 (hqn i)
      (hsep i) (h20 i) (h20' j) (hrs i) (hrs' j) (hrs1 i) (K i) (K' j) (hK i) (hK2 i)
      (hK' j) (hroom' j) (hK1' j) (hK2' j)
  have hcomp : ∀ o o', EqOn (F o) (F o') (Uf o ∩ Uf o') := by
    rintro (_ | i | j) (_ | i' | j') v hv
    · rfl
    · exact (hIK i' ⟨hv.2, hv.1⟩).symm
    · exact (hIK' j' ⟨hv.2, hv.1⟩).symm
    · exact hIK i hv
    · exact hSS i i' hv
    · exact hST i j' v hv.1 hv.2
    · exact hIK' j hv
    · exact (hST i' j v hv.2 hv.1).symm
    · exact hTT j j' hv
  obtain ⟨H, hH, hHe⟩ := exists_productSolutionOn_iUnion S L lam Uf hUo F hF hcomp
  have hUeq : (⋃ o, Uf o) = initialCross S lam ∪ ((⋃ i, overlapRetained (q i) (r i) i.1.2) ∪
      ⋃ j, Prod.swap ⁻¹' overlapRetained (q' j) (r' j) j.1.2) := by
    ext v
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨_ | i | j, hv⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl ⟨i, hv⟩)
      · exact Or.inr (Or.inr ⟨j, hv⟩)
    · rintro (hv | ⟨i, hv⟩ | ⟨j, hv⟩)
      · exact ⟨none, hv⟩
      · exact ⟨some (Sum.inl i), hv⟩
      · exact ⟨some (Sum.inr j), hv⟩
  have hHI : EqOn H (initialKernel S lam) (initialCross S lam) := hHe none
  have hHK : ∀ i, EqOn H (K i) (overlapRetained (q i) (r i) i.1.2) :=
    fun i => hHe (some (Sum.inl i))
  have hHK' : ∀ j, EqOn H (fun v => K' j (v.2,v.1))
      (Prod.swap ⁻¹' overlapRetained (q' j) (r' j) j.1.2) := fun j => hHe (some (Sum.inr j))
  refine ⟨q, q', R, r, R', r', K, K', _, H,
    fun i => ⟨hsep i, hqp i, hr i, h20 i, hrs i, hroom i, hK i, t i, ht i, rfl⟩,
    fun j => ⟨hsep' j, hqp' j, hr' j, h20' j, hrs' j, hroom' j, hK' j, t' j, ht' j, rfl⟩, rfl,
    hIo.union ((isOpen_iUnion fun i => isOpen_overlapRetained _ _ _).union
      (isOpen_iUnion fun j => (isOpen_overlapRetained _ _ _).preimage continuous_swap)),
    ?_, by rw [← hUeq]; exact hH, hHI, hHK, hHK', ?_, ?_⟩
  · rintro v (hv | hv | hv)
    · exact hv.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      exact hroom i (hsub i hi)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      exact hroomT j v (hsub' j hj)
  · rintro v (hv | hv | hv) hW
    · rw [hHI hv]; exact hI1 v hv hW
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rw [hHK i hi]; exact hK1 i v (hsub i hi) hW
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      rw [hHK' j hj]; exact (hT j).1 v (hsub' j hj) hW
  · rintro v (hv | hv | hv) hW
    · rw [hHI hv]; exact hI2 v hv hW
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rw [hHK i hi]; exact hK2 i v (hsub i hi) hW
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      rw [hHK' j hj]; exact (hT j).2 v (hsub' j hj) hW

/-- Uniqueness of the ACTUAL separator zero on a vertical line inside the checked descent ball
(positive vertical derivative up to `1/4`). -/
theorem separator_vertical_zero_unique (S : KnownSideSourceData) {a : ℝ}
    (hmv : ∀ z0 ∈ ball (0 : R3) a, ∀ z1 ∈ ball (0 : R3) a,
      S.separating_function z1 ≤ S.separating_function z0 + (z1 - z0) 2 + (1/4) * ‖z1 - z0‖)
    {lam t c : ℝ} (hlam : 0 < lam) {p : R3}
    (ht : lam • (p + t • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ ball (0 : R3) a)
    (hc : lam • (p + c • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ∈ ball (0 : R3) a)
    (ht0 : S.separating_function (lam • (p + t • EuclideanSpace.single (2:Fin 3) (1:ℝ))) = 0)
    (hc0 : S.separating_function (lam • (p + c • EuclideanSpace.single (2:Fin 3) (1:ℝ))) = 0) :
    t = c := by
  have hd : ∀ u w : ℝ, lam • (p + u • EuclideanSpace.single (2:Fin 3) (1:ℝ)) -
      lam • (p + w • EuclideanSpace.single (2:Fin 3) (1:ℝ)) =
      (lam * (u - w)) • EuclideanSpace.single (2:Fin 3) (1:ℝ) := fun u w => by
    rw [← smul_sub, add_sub_add_left_eq_sub, ← sub_smul, smul_smul]
  have hcomp : ∀ u : ℝ, (u • EuclideanSpace.single (2:Fin 3) (1:ℝ)) 2 = u := fun u => by simp
  have hnorm : ∀ u : ℝ, ‖u • EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ = |u| := fun u => by
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  have e1 := hmv _ ht _ hc
  have e2 := hmv _ hc _ ht
  rw [hd, hcomp, hnorm, ht0, hc0] at e1
  rw [hd, hcomp, hnorm, ht0, hc0] at e2
  have hneg : lam * (t - c) = -(lam * (c - t)) := by ring
  rw [hneg, abs_neg] at e2
  have hz : lam * (c - t) = 0 := by
    rcases lt_trichotomy (lam * (c - t)) 0 with h | h | h
    · rw [abs_of_neg h] at e1; linarith
    · exact h
    · rw [abs_of_pos h] at e2; linarith
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hlam.ne'
  · linarith

/-- The two-orientation common seed contains retained products of BOTH orientations around
EVERY actual bounded separator zero `p + c e2` (`|c| < s0/4`); one `lam0` before `L`, `lam`.
The radii depend on `lam`: this is not a uniform coarse opening. -/
theorem actual_two_orientation_seed_covers_zeros (S : KnownSideSourceData) (B s0 s1 : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧ initialCross S lam ⊆ U ∧
        U ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam H U ∧
        EqOn H (initialKernel S lam) (initialCross S lam) ∧
        (∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
        ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 → ∀ s ∈ Set.Icc s0 s1,
        ∀ c ∈ Set.Ioo (-(s0/4)) (s0/4),
          S.separating_function (lam • (p + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 →
          ∃ r r' : ℝ, 0 < r ∧ r ≤ s/1000 ∧ 0 < r' ∧ r' ≤ s/1000 ∧
            overlapRetained (p + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) r s ⊆ U ∧
            Prod.swap ⁻¹' overlapRetained (p + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
              r' s ⊆ U := by
  obtain ⟨lamP, hlP, HP⟩ := actual_two_orientation_union_kernel S B s0 s1 hB hs0 hss
  obtain ⟨a, lamD, ha, hlD, -, hmv, HD⟩ := exists_uniform_descent_room S (B + s0) (by positivity)
  refine ⟨min lamP lamD, lt_min hlP hlD, fun L lam hlam hle => ?_⟩
  obtain ⟨q, q', R, r, R', r', K, K', U, H, hq, hq', hU, hUo, hUroom, hHsol, hHI, -, -,
    hH1, hH2⟩ := HP L lam hlam (hle.trans (min_le_left _ _))
  subst hU
  have hD := fun z hz => HD lam hlam (hle.trans (min_le_right _ _)) z hz
  refine ⟨_, H, hUo, subset_union_left, hUroom, hHsol, hHI, hH1, hH2,
    fun p hp hp2 s hs c hc hsep => ?_⟩
  have hbd : ∀ u ∈ Set.Ioo (-(s0/4)) (s0/4),
      ‖p + u • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B + s0 := fun u hu => by
    have h1 := norm_add_le p (u • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs] at h1
    have h2 : |u| < s0/4 := abs_lt.mpr hu
    linarith
  let i : anchorIndex B s0 s1 := ⟨(p, s), hp, hp2, hs⟩
  obtain ⟨hs1, -, hr, -, hrs, -, -, t, ht, hqt⟩ := hq i
  obtain ⟨hs1', -, hr', -, hrs', -, -, t', ht', hqt'⟩ := hq' i
  have hqt2 : q i = p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := hqt
  have hqt2' : q' i = p + t' • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := hqt'
  rw [hqt2] at hs1
  rw [hqt2'] at hs1'
  have htc : t = c := separator_vertical_zero_unique S hmv hlam (hD _ (hbd t ht))
    (hD _ (hbd c hc)) hs1 hsep
  have htc' : t' = c := separator_vertical_zero_unique S hmv hlam (hD _ (hbd t' ht'))
    (hD _ (hbd c hc)) hs1' hsep
  have hqc : q i = p + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by rw [hqt2, htc]
  have hqc' : q' i = p + c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by rw [hqt2', htc']
  refine ⟨r i, r' i, hr, hrs, hr', hrs', fun v hv => ?_, fun v hv => ?_⟩
  · refine Or.inr (Or.inl (mem_iUnion.mpr ⟨i, ?_⟩))
    rw [hqc]
    exact hv
  · refine Or.inr (Or.inr (mem_iUnion.mpr ⟨i, ?_⟩))
    show Prod.swap v ∈ overlapRetained (q' i) (r' i) i.1.2
    rw [hqc']
    exact hv

/-- FIXED-`lam` positive seed buffer around the compact actual bounded zero set, in BOTH
orientations. The buffer `δ` depends on `lam`: NOT a uniform coarse opening. -/
theorem actual_two_orientation_seed_buffer (S : KnownSideSourceData) (B s0 s1 : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧ initialCross S lam ⊆ U ∧
        U ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam H U ∧
        EqOn H (initialKernel S lam) (initialCross S lam) ∧
        (∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
          ‖z - z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B → |z 2| ≤ s0/8 →
          S.separating_function (lam • z) = 0 → ∀ s ∈ Set.Icc s0 s1,
          ∀ x y : R3, ‖x - z‖ < δ → |‖y - z‖ - s| < δ → (x, y) ∈ U ∧ (y, x) ∈ U := by
  obtain ⟨lamP, hlP, HP⟩ := actual_two_orientation_seed_covers_zeros S B s0 s1 hB hs0 hss
  obtain ⟨a, ha, hroomA, -, -⟩ := exists_separator_descent_ball S
  obtain ⟨lamD, hlD, HD⟩ := exists_uniform_scaled_ball ha (show 0 < B + s0 by positivity)
  refine ⟨min lamP lamD, lt_min hlP hlD, fun L lam hlam hle => ?_⟩
  obtain ⟨U, H, hUo, hIU, hUroom, hHsol, hHI, hH1, hH2, hcov⟩ :=
    HP L lam hlam (hle.trans (min_le_left _ _))
  have hD := HD lam hlam (hle.trans (min_le_right _ _))
  refine ⟨U, H, hUo, hIU, hUroom, hHsol, hHI, hH1, hH2, ?_⟩
  have hzn : ∀ z : R3, ‖z - z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B →
      |z 2| ≤ s0/8 → ‖z‖ ≤ B + s0 := fun z h1 h2 => by
    have h := norm_add_le (z - z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      (z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [sub_add_cancel, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs] at h
    linarith
  let A : Set (R3 × ℝ) := {w | ‖w.1‖ ≤ B + s0 ∧
    (‖w.1 - w.1 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B ∧
    (|w.1 2| ≤ s0/8 ∧ (s0 ≤ w.2 ∧ w.2 ≤ s1)))}
  have hc2 : Continuous fun w : R3 × ℝ => w.1 2 := by fun_prop
  have hA : IsClosed A := by
    have c1 : IsClosed {w : R3 × ℝ | ‖w.1‖ ≤ B + s0} :=
      isClosed_le continuous_fst.norm continuous_const
    have c2 : IsClosed
        {w : R3 × ℝ | ‖w.1 - w.1 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B} :=
      isClosed_le (continuous_fst.sub (hc2.smul continuous_const)).norm continuous_const
    have c3 : IsClosed {w : R3 × ℝ | |w.1 2| ≤ s0/8} :=
      isClosed_le hc2.abs continuous_const
    have c4 : IsClosed {w : R3 × ℝ | s0 ≤ w.2} := isClosed_le continuous_const continuous_snd
    have c5 : IsClosed {w : R3 × ℝ | w.2 ≤ s1} := isClosed_le continuous_snd continuous_const
    exact c1.inter (c2.inter (c3.inter (c4.inter c5)))
  have hsepc : ContinuousOn (fun w : R3 × ℝ => S.separating_function (lam • w.1)) A :=
    S.separating_function_smooth.continuousOn.comp
      (by fun_prop : Continuous fun w : R3 × ℝ => lam • w.1).continuousOn
      (fun w hw => hroomA (hD w.1 hw.1))
  let K : Set (R3 × ℝ) := A ∩ (fun w : R3 × ℝ => S.separating_function (lam • w.1)) ⁻¹' {0}
  have hKc : IsCompact K := by
    refine ((isCompact_closedBall (0 : R3) (B + s0)).prod (isCompact_Icc : IsCompact (Set.Icc s0 s1))).of_isClosed_subset
      (hsepc.preimage_isClosed_of_isClosed hA isClosed_singleton) ?_
    intro w hw
    exact ⟨mem_closedBall_zero_iff.mpr hw.1.1, hw.1.2.2.2⟩
  have hex : ∀ w : K, ∃ r r' : ℝ, 0 < r ∧ r ≤ w.1.2/1000 ∧ 0 < r' ∧ r' ≤ w.1.2/1000 ∧
      overlapRetained w.1.1 r w.1.2 ⊆ U ∧
      Prod.swap ⁻¹' overlapRetained w.1.1 r' w.1.2 ⊆ U := by
    rintro ⟨⟨z, s⟩, ⟨hz1, hz2, hz3, hs1, hs2⟩, hz0⟩
    have hp2 : (z - z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = 0 := by simp
    have hc : z 2 ∈ Set.Ioo (-(s0/4)) (s0/4) := by
      rw [abs_le] at hz3
      constructor <;> linarith
    have hsep : S.separating_function (lam • ((z - z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
        + z 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 := by
      rw [sub_add_cancel]; exact hz0
    have h := hcov _ hz2 hp2 s ⟨hs1, hs2⟩ (z 2) hc hsep
    rw [sub_add_cancel] at h
    exact h
  choose r r' hr hrs hr' hrs' hU1 hU2 using hex
  have hcover : K ⊆ ⋃ w : K, ball w.1.1 (min (r w) (r' w) / 2) ×ˢ
      Set.Ioo (w.1.2 * (99/100)) (w.1.2 * (101/100)) := by
    intro w hw
    refine mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (by
      have := lt_min (hr ⟨w, hw⟩) (hr' ⟨w, hw⟩); linarith), ?_, ?_⟩
    · have : 0 < w.2 := hs0.trans_le hw.1.2.2.2.1
      show w.2 * (99/100) < w.2
      linarith
    · have : 0 < w.2 := hs0.trans_le hw.1.2.2.2.1
      show w.2 < w.2 * (101/100)
      linarith
  obtain ⟨δ, hδ, Hδ⟩ := lebesgue_number_lemma_of_metric hKc
    (fun w : K => isOpen_ball.prod isOpen_Ioo) hcover
  refine ⟨min δ (s0/100), lt_min hδ (by positivity),
    fun z hz1 hz3 hz0 s hs x y hx hy => ?_⟩
  have hwK : (z, s) ∈ K := ⟨⟨hzn z hz1 hz3, hz1, hz3, hs.1, hs.2⟩, hz0⟩
  obtain ⟨i, hi⟩ := Hδ (z, s) hwK
  have hxm : (x, s) ∈ ball (z, s) δ := by
    rw [mem_ball, Prod.dist_eq, dist_self, dist_eq_norm]
    exact max_lt (lt_of_lt_of_le hx (min_le_left _ _)) hδ
  have hzm : (z, s) ∈ ball (z, s) δ := mem_ball_self hδ
  obtain ⟨hxi, hsi1, hsi2⟩ := hi hxm
  obtain ⟨hzi, -, -⟩ := hi hzm
  have hsi0 : s0 ≤ i.1.2 := i.2.1.2.2.2.1
  have hxi' : ‖x - i.1.1‖ < min (r i) (r' i) / 2 := by rw [← dist_eq_norm]; exact hxi
  have hzi' : ‖z - i.1.1‖ < min (r i) (r' i) / 2 := by rw [← dist_eq_norm]; exact hzi
  have hm : min (r i) (r' i) ≤ i.1.2/1000 := (min_le_left _ _).trans (hrs i)
  have hy' := abs_lt.mp hy
  have hδs : min δ (s0/100) ≤ s0/100 := min_le_right _ _
  have hup := norm_sub_le_norm_sub_add_norm_sub y z i.1.1
  have hlo := norm_sub_le_norm_sub_add_norm_sub y i.1.1 z
  rw [norm_sub_rev i.1.1 z] at hlo
  have hsi1' : i.1.2 * (99/100) < s := hsi1
  have hsi2' : s < i.1.2 * (101/100) := hsi2
  have hann : 19 * i.1.2 / 20 < ‖y - i.1.1‖ ∧ ‖y - i.1.1‖ < 21 * i.1.2 / 20 := by
    constructor <;> nlinarith [norm_nonneg (z - i.1.1)]
  have hmem : ∀ ρ : ℝ, min (r i) (r' i) ≤ ρ → (x, y) ∈ overlapRetained i.1.1 ρ i.1.2 :=
    fun ρ hρ => ⟨by
      rw [mem_ball, dist_eq_norm]
      have := lt_min (hr i) (hr' i)
      linarith, hann⟩
  exact ⟨hU1 i (hmem _ (min_le_left _ _)), hU2 i (hmem _ (min_le_right _ _))⟩
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v046: uniform radial Carleman estimate (U1, U2 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

/-- U1a: family-form bounds consumer of the collaborator's convexified Carleman identity.
`Lam`, `kappa` are explicit functions of the uniform bounds; the `Rf` bound is requested only
after they are fixed; `tau0` is explicit. -/
theorem carleman_family_of_bounds {ι : Type*} (a : ι → Fin 3 → Fin 3 → R3 → ℝ)
    (ψ : ι → R3 → ℝ) (K : ι → Set R3)
    (ha : ∀ P i k, ContDiff ℝ ∞ (a P i k)) (hsymm : ∀ P i k, a P i k = a P k i)
    (hψ : ∀ P, ContDiff ℝ ∞ (ψ P)) (hK : ∀ P, IsCompact (K P))
    {α C₁ n₀ N₁ C₂ Ψ : ℝ} (hα : 0 < α) (hn₀ : 0 < n₀)
    (hQ : ∀ P, ∀ x ∈ K P, ∀ ξ : Fin 3 → ℝ, α * ‖ξ‖ ^ 2 ≤ quad (a P) x ξ)
    (hE : ∀ P, ∀ x ∈ K P, ∀ ξ : Fin 3 → ℝ, |E1 (a P) (ψ P) x ξ| ≤ C₁ * ‖ξ‖ ^ 2)
    (hN0 : ∀ P, ∀ x ∈ K P, n₀ ≤ Nf (a P) (ψ P) x)
    (hN1 : ∀ P, ∀ x ∈ K P, |Nf (a P) (ψ P) x| ≤ N₁)
    (hP : ∀ P, ∀ x ∈ K P, |Pf (a P) (ψ P) x| ≤ C₂)
    (hΨ : ∀ P, ∀ x ∈ K P, |ψ P x| ≤ Ψ)
    (hR : ∀ Λ κ : ℝ, ∃ D : ℝ, ∀ P, ∀ x ∈ K P, |Rf (a P) (ψ P) Λ κ x| ≤ D) :
    ∃ Λ τ0 : ℝ, 0 < Λ ∧ ∀ P, ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ K P →
      (∫ x, Real.exp (2 * τ * phi (ψ P) Λ x) * w x ^ 2) ≤
        ∫ x, Real.exp (2 * τ * phi (ψ P) Λ x) * Lop (a P) w x ^ 2 := by
  set M := max N₁ 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  set κ := min 1 (n₀ ^ 2 / M) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκN : ∀ P, ∀ x ∈ K P, κ * Nf (a P) (ψ P) x ≤ n₀ ^ 2 := by
    intro P x hx
    have hN : Nf (a P) (ψ P) x ≤ M :=
      (le_abs_self _).trans ((hN1 P x hx).trans (le_max_left _ _))
    have h1 : κ * Nf (a P) (ψ P) x ≤ n₀ ^ 2 / M * M :=
      mul_le_mul (min_le_right _ _) hN (hn₀.le.trans (hN0 P x hx)) (by positivity)
    rwa [div_mul_cancel₀ _ (by positivity)] at h1
  set Λ := max 1 (max (C₁ / (2 * κ * α)) ((C₂ + n₀ ^ 2) / n₀ ^ 2)) with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛC₁ : C₁ ≤ 2 * κ * Λ * α := by
    have h : C₁ / (2 * κ * α) ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
    have := (div_le_iff₀ (by positivity)).1 h
    linarith
  have hΛC₂ : (C₂ + n₀ ^ 2) / n₀ ^ 2 ≤ Λ := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨D, hD⟩ := hR Λ κ
  set φ₀ := Real.exp (-(Λ * Ψ)) with hφ₀def
  set φ₁ := Real.exp (Λ * Ψ) with hφ₁def
  have hφ₀ : 0 < φ₀ := Real.exp_pos _
  have hφK : ∀ P, ∀ x ∈ K P, φ₀ ≤ phi (ψ P) Λ x ∧ phi (ψ P) Λ x ≤ φ₁ := by
    intro P x hx
    have h := abs_le.mp (hΨ P x hx)
    have hΛ0 : 0 ≤ Λ := by linarith
    show Real.exp (-(Λ * Ψ)) ≤ Real.exp (Λ * ψ P x) ∧ Real.exp (Λ * ψ P x) ≤ Real.exp (Λ * Ψ)
    refine ⟨Real.exp_le_exp.mpr ?_, Real.exp_le_exp.mpr ?_⟩
    · have := mul_le_mul_of_nonneg_left h.1 hΛ0
      linarith
    · exact mul_le_mul_of_nonneg_left h.2 hΛ0
  refine ⟨Λ, max 1 ((κ * Λ ^ 4 * φ₁ ^ 2 + |D| + 1) / (2 * n₀ ^ 2 * Λ ^ 3 * φ₀ ^ 3)),
    by linarith, ?_⟩
  intro P τ hτ w hw hws
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτ' : κ * Λ ^ 4 * φ₁ ^ 2 + |D| + 1 ≤ τ * (2 * n₀ ^ 2 * Λ ^ 3 * φ₀ ^ 3) := by
    have h := (le_max_right _ _).trans hτ
    have := (div_le_iff₀ (by positivity)).1 h
    linarith
  exact carleman_of_pointwise (ha P) (hsymm P) (hψ P) Λ τ κ hκ0.le hκ1 (hK P)
    (fun x hx ξ => by
      rw [grad_coeff (ha P) (hsymm P) (hψ P) Λ τ κ x ξ]
      exact grad_part_nonneg (by linarith) (by linarith) (Real.exp_pos _).le (hE P x hx ξ)
        (hQ P x hx ξ) hκ0.le hΛC₁ (by positivity))
    (fun x hx => by
      rw [zero_coeff (ha P) (hψ P) Λ τ κ x]
      exact zero_part_ge_one hn₀
        (B_ge hn₀ (hN0 P x hx) (hκN P x hx) (hP P x hx) hΛC₂ (by linarith))
        hΛ1 hφ₀ (hφK P x hx).1 (hφK P x hx).2 hκ0.le
        ((le_abs_self _).trans ((hD P x hx).trans (le_abs_self _))) (abs_nonneg _) hτ1 hτ')
    hw hws

/-- Joint smoothness of a parametric family of scalar functions on `R3`. -/
abbrev JointSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → R3 → ℝ) :
    Prop :=
  ContDiff ℝ ∞ (fun q : E × R3 => F q.1 q.2)

section JointSmoothClosure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- U2a: the coordinate derivative of a jointly smooth family is jointly smooth. -/
theorem jointSmooth_pd {F : E → R3 → ℝ} (hF : JointSmooth F) (k : Fin 3) :
    JointSmooth (fun q => pd k (F q)) := by
  have hu : ContDiff ℝ ∞ (Function.uncurry fun (q : E × R3) (y : R3) => F q.1 y) :=
    hF.comp (by fun_prop : ContDiff ℝ ∞ (fun p : (E × R3) × R3 => (p.1.1, p.2)))
  show ContDiff ℝ ∞ (fun q : E × R3 => fderiv ℝ (F q.1) q.2 (EuclideanSpace.single k 1))
  exact hu.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem jointSmooth_add {F G : E → R3 → ℝ} (hF : JointSmooth F) (hG : JointSmooth G) :
    JointSmooth (fun q y => F q y + G q y) := ContDiff.add hF hG

theorem jointSmooth_mul {F G : E → R3 → ℝ} (hF : JointSmooth F) (hG : JointSmooth G) :
    JointSmooth (fun q y => F q y * G q y) := ContDiff.mul hF hG

theorem jointSmooth_const_mul (c : ℝ) {F : E → R3 → ℝ} (hF : JointSmooth F) :
    JointSmooth (fun q y => c * F q y) := ContDiff.mul contDiff_const hF

theorem jointSmooth_exp {F : E → R3 → ℝ} (hF : JointSmooth F) :
    JointSmooth (fun q y => Real.exp (F q y)) := ContDiff.exp hF

theorem jointSmooth_sum {F : Fin 3 → E → R3 → ℝ} (hF : ∀ k, JointSmooth (F k)) :
    JointSmooth (fun q y => ∑ k, F k q y) := ContDiff.sum fun k _ => hF k

variable {a : E → Fin 3 → Fin 3 → R3 → ℝ} {ψ : E → R3 → ℝ}

theorem jointSmooth_bv (ha : ∀ i k, JointSmooth fun q => a q i k) (hψ : JointSmooth ψ)
    (j : Fin 3) : JointSmooth fun q => bv (a q) (ψ q) j :=
  jointSmooth_sum (F := fun k q y => a q j k y * pd k (ψ q) y)
    (fun k => jointSmooth_mul (ha j k) (jointSmooth_pd hψ k))

theorem jointSmooth_Nf (ha : ∀ i k, JointSmooth fun q => a q i k) (hψ : JointSmooth ψ) :
    JointSmooth fun q => Nf (a q) (ψ q) :=
  jointSmooth_sum (F := fun j q y => bv (a q) (ψ q) j y * pd j (ψ q) y)
    (fun j => jointSmooth_mul (jointSmooth_bv ha hψ j) (jointSmooth_pd hψ j))

theorem jointSmooth_Pf (ha : ∀ i k, JointSmooth fun q => a q i k) (hψ : JointSmooth ψ) :
    JointSmooth fun q => Pf (a q) (ψ q) :=
  jointSmooth_sum (F := fun j q y => bv (a q) (ψ q) j y * pd j (Nf (a q) (ψ q)) y)
    (fun j => jointSmooth_mul (jointSmooth_bv ha hψ j)
      (jointSmooth_pd (F := fun q => Nf (a q) (ψ q)) (jointSmooth_Nf ha hψ) j))

theorem jointSmooth_phi (hψ : JointSmooth ψ) (Λ : ℝ) : JointSmooth fun q => phi (ψ q) Λ :=
  jointSmooth_exp (F := fun q y => Λ * ψ q y) (jointSmooth_const_mul Λ hψ)

theorem jointSmooth_Xs (ha : ∀ i k, JointSmooth fun q => a q i k) (hψ : JointSmooth ψ)
    (Λ : ℝ) (j : Fin 3) : JointSmooth fun q => Xs (a q) (ψ q) Λ j :=
  jointSmooth_mul (F := fun q y => Λ * phi (ψ q) Λ y) (G := fun q => bv (a q) (ψ q) j)
    (jointSmooth_const_mul Λ (jointSmooth_phi hψ Λ)) (jointSmooth_bv ha hψ j)

theorem jointSmooth_thetas (hψ : JointSmooth ψ) (Λ : ℝ) : JointSmooth fun q => θs (ψ q) Λ :=
  jointSmooth_const_mul (F := fun q => phi (ψ q) Λ) (Λ ^ 2) (jointSmooth_phi hψ Λ)

theorem jointSmooth_divV {X : E → Fin 3 → R3 → ℝ} (hX : ∀ j, JointSmooth fun q => X q j) :
    JointSmooth fun q => divV (X q) :=
  jointSmooth_sum (F := fun j q y => pd j (X q j) y)
    (fun j => jointSmooth_pd (F := fun q => X q j) (hX j) j)

theorem jointSmooth_Lop (ha : ∀ i k, JointSmooth fun q => a q i k) {f : E → R3 → ℝ}
    (hf : JointSmooth f) : JointSmooth fun q => Lop (a q) (f q) :=
  jointSmooth_sum (F := fun i q y => pd i (fun z => ∑ k, a q i k z * pd k (f q) z) y)
    (fun i => jointSmooth_pd (F := fun q z => ∑ k, a q i k z * pd k (f q) z)
      (jointSmooth_sum (F := fun k q z => a q i k z * pd k (f q) z)
        (fun k => jointSmooth_mul (ha i k) (jointSmooth_pd hf k))) i)

theorem jointSmooth_Rf (ha : ∀ i k, JointSmooth fun q => a q i k) (hψ : JointSmooth ψ)
    (Λ κ : ℝ) : JointSmooth fun q => Rf (a q) (ψ q) Λ κ :=
  jointSmooth_add (F := fun q => Lop (a q) (divV (Xs (a q) (ψ q) Λ)))
    (G := fun q y => κ * Lop (a q) (θs (ψ q) Λ) y)
    (jointSmooth_Lop ha (f := fun q => divV (Xs (a q) (ψ q) Λ))
      (jointSmooth_divV (X := fun q => Xs (a q) (ψ q) Λ) (fun j => jointSmooth_Xs ha hψ Λ j)))
    (jointSmooth_const_mul (F := fun q => Lop (a q) (θs (ψ q) Λ)) κ
      (jointSmooth_Lop ha (f := fun q => θs (ψ q) Λ) (jointSmooth_thetas hψ Λ)))

end JointSmoothClosure

theorem continuous_quad_form {X : Type*} [TopologicalSpace X] {A : X → Fin 3 → Fin 3 → ℝ}
    (hA : Continuous A) :
    Continuous (fun p : X × (Fin 3 → ℝ) => ∑ i, ∑ k, A p.1 i k * p.2 i * p.2 k) := by
  simp only [Fin.sum_univ_three]
  fun_prop

theorem continuous_E1_form {X : Type*} [TopologicalSpace X] {A : X → Fin 3 → Fin 3 → ℝ}
    {dB : X → Fin 3 → Fin 3 → ℝ} {dA : X → Fin 3 → Fin 3 → Fin 3 → ℝ} {b : X → Fin 3 → ℝ}
    (hA : Continuous A) (hdB : Continuous dB) (hdA : Continuous dA) (hb : Continuous b) :
    Continuous (fun p : X × (Fin 3 → ℝ) =>
      4 * ∑ i, ∑ j, ∑ l, A p.1 i l * p.2 l * dB p.1 i j * p.2 j -
        2 * ∑ j, b p.1 j * ∑ i, ∑ k, dA p.1 j i k * p.2 i * p.2 k) := by
  simp only [Fin.sum_univ_three]
  fun_prop

/-- Parametric copy of the collaborator `quad_lower` (compact parameter set). -/
theorem quad_lower_param {X : Type*} [TopologicalSpace X] {G : Set X} (hG : IsCompact G)
    (Q : X → (Fin 3 → ℝ) → ℝ) (hQ : Continuous (fun p : X × (Fin 3 → ℝ) => Q p.1 p.2))
    (hhom : ∀ x (t : ℝ) ξ, Q x (t • ξ) = t ^ 2 * Q x ξ)
    (hpos : ∀ x ∈ G, ∀ ξ, ξ ≠ 0 → 0 < Q x ξ) :
    ∃ α > 0, ∀ x ∈ G, ∀ ξ, α * ‖ξ‖ ^ 2 ≤ Q x ξ := by
  obtain ⟨α, hα, hαS⟩ := exists_pos_lower_of_compact
    (hG.prod (isCompact_sphere (0 : Fin 3 → ℝ) 1)) hQ.continuousOn (by
      rintro ⟨x, u⟩ ⟨hx, hu⟩
      refine hpos x hx u ?_
      rintro rfl
      simp at hu)
  refine ⟨α, hα, fun x hx ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 := hhom x 0 0
    simp at h0
    simp [h0]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    have hu : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin 3 → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hEq : Q x ξ = ‖ξ‖ ^ 2 * Q x (‖ξ‖⁻¹ • ξ) := by
      rw [← hhom, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h1 := hαS (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hu⟩
    rw [hEq, mul_comm α]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Parametric copy of the collaborator `quad_upper` (compact parameter set). -/
theorem quad_upper_param {X : Type*} [TopologicalSpace X] {G : Set X} (hG : IsCompact G)
    (Q : X → (Fin 3 → ℝ) → ℝ) (hQ : Continuous (fun p : X × (Fin 3 → ℝ) => Q p.1 p.2))
    (hhom : ∀ x (t : ℝ) ξ, Q x (t • ξ) = t ^ 2 * Q x ξ) :
    ∃ C, ∀ x ∈ G, ∀ ξ, |Q x ξ| ≤ C * ‖ξ‖ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_upper_of_compact (hG.prod (isCompact_sphere (0 : Fin 3 → ℝ) 1))
    hQ.continuousOn
  refine ⟨C, fun x hx ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 := hhom x 0 0
    simp at h0
    simp [h0]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    have hu : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin 3 → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hEq : Q x ξ = ‖ξ‖ ^ 2 * Q x (‖ξ‖⁻¹ • ξ) := by
      rw [← hhom, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h1 := hC (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hu⟩
    rw [hEq, abs_mul, abs_of_nonneg (by positivity), mul_comm C]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The literal coefficient family `principalCoefficient g (lam • y)`, `q = (lam, c, u)`. -/
def radialCoeff (g : MatrixField) (q : ℝ × R3 × ℝ) : Fin 3 → Fin 3 → R3 → ℝ :=
  fun i k y => EnergyBridge.principalCoefficient g (q.1 • y) i k

/-- The radial weight `-‖y - c‖² u²` (`= -‖y - c‖²/s²` for `u = 1/s`), `q = (lam, c, u)`. -/
def radialWeight (q : ℝ × R3 × ℝ) (y : R3) : ℝ := -(‖y - q.2.1‖ ^ 2 * q.2.2 ^ 2)

theorem jointSmooth_radialCoeff (g : MatrixField) (hg : IsAdmissibleMetric g) (i k : Fin 3) :
    JointSmooth fun q : ℝ × R3 × ℝ => radialCoeff g q i k :=
  (EnergyBridge.contDiff_principalCoefficient_entry g hg i k).comp
    (contDiff_fst.fst.smul contDiff_snd)

theorem jointSmooth_radialWeight : JointSmooth radialWeight :=
  ((ContDiff.norm_sq ℝ (contDiff_snd.sub contDiff_fst.snd.fst)).mul
    (contDiff_fst.snd.snd.pow 2)).neg

theorem radialCoeff_quad_pos (g : MatrixField) (hg : IsAdmissibleMetric g) (q : ℝ × R3 × ℝ)
    (y : R3) {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) : 0 < quad (radialCoeff g q) y ξ := by
  have := (EnergyBridge.principalCoefficient_posDef g hg (q.1 • y)).dotProduct_mulVec_pos hξ
  convert this using 1
  simp [quad, radialCoeff, dotProduct, Matrix.mulVec, Fin.sum_univ_three] <;> ring

theorem fderiv_radialWeight_ne_zero {q : ℝ × R3 × ℝ} {y : R3} (hu : q.2.2 ≠ 0)
    (hy : y ≠ q.2.1) : fderiv ℝ (radialWeight q) y ≠ 0 := by
  intro h0
  have h1 := (((hasFDerivAt_id y).sub_const q.2.1).norm_sq.mul_const (q.2.2 ^ 2)).neg
  have h2 : fderiv ℝ (radialWeight q) y = _ := h1.fderiv
  have h3 := congrArg (fun L : R3 →L[ℝ] ℝ => L (y - q.2.1)) (h2.symm.trans h0)
  simp [hu, sub_eq_zero] at h3
  rw [← sub_eq_zero, ← inner_sub_left, inner_self_eq_zero, sub_eq_zero] at h3
  exact hy h3

theorem grad_ne_zero_of_fderiv_ne {f : R3 → ℝ} {x : R3} (h : fderiv ℝ f x ≠ 0) :
    grad f x ≠ 0 := by
  intro hg
  apply h
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro i
  have := congrFun hg i
  simpa [grad, pd] using this

/-- The compact parameter set `[0, lam1] × closedBall 0 B × [1/s1, 1/s0]` (`u = 1/s`). -/
def radialParams (lam1 B s0 s1 : ℝ) : Set (ℝ × R3 × ℝ) :=
  {P | 0 ≤ P.1 ∧ P.1 ≤ lam1 ∧ ‖P.2.1‖ ≤ B ∧ 1 / s1 ≤ P.2.2 ∧ P.2.2 ≤ 1 / s0}

/-- The annulus `ρ1 ≤ u ‖y - c‖ ≤ ρ2` of the parameter `P = (lam, c, u)`. -/
def radialAnnulus (ρ1 ρ2 : ℝ) (P : ℝ × R3 × ℝ) : Set R3 :=
  {y | ρ1 ≤ P.2.2 * ‖y - P.2.1‖ ∧ P.2.2 * ‖y - P.2.1‖ ≤ ρ2}

/-- The joint compact set `G = {(P, y) | P ∈ radialParams, y ∈ radialAnnulus P}`. -/
def radialSet (lam1 B s0 s1 ρ1 ρ2 : ℝ) : Set ((ℝ × R3 × ℝ) × R3) :=
  {q | q.1 ∈ radialParams lam1 B s0 s1 ∧ q.2 ∈ radialAnnulus ρ1 ρ2 q.1}

theorem radialSet_dist {lam1 B s0 s1 ρ1 ρ2 : ℝ} (hs1 : 0 < s1)
    {q : (ℝ × R3 × ℝ) × R3} (hq : q ∈ radialSet lam1 B s0 s1 ρ1 ρ2) :
    ‖q.2 - q.1.2.1‖ ≤ ρ2 * s1 := by
  obtain ⟨⟨-, -, -, hu, -⟩, -, h2⟩ := hq
  have h := mul_le_mul_of_nonneg_right hu (norm_nonneg (q.2 - q.1.2.1))
  have h' : 1 / s1 * ‖q.2 - q.1.2.1‖ ≤ ρ2 := h.trans h2
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs1] at h'
  exact h'

theorem radialSet_ne {lam1 B s0 s1 ρ1 ρ2 : ℝ} (hs1 : 0 < s1) (hρ1 : 0 < ρ1)
    {q : (ℝ × R3 × ℝ) × R3} (hq : q ∈ radialSet lam1 B s0 s1 ρ1 ρ2) :
    q.1.2.2 ≠ 0 ∧ q.2 ≠ q.1.2.1 := by
  obtain ⟨⟨-, -, -, hu, -⟩, hr, -⟩ := hq
  have hu1 : 0 < 1 / s1 := by positivity
  refine ⟨(hu1.trans_le hu).ne', fun h => ?_⟩
  rw [h, sub_self, norm_zero, mul_zero] at hr
  linarith

theorem isCompact_radialSet (lam1 B s0 s1 ρ1 ρ2 : ℝ) (hs1 : 0 < s1) :
    IsCompact (radialSet lam1 B s0 s1 ρ1 ρ2) := by
  have c1 : Continuous fun q : (ℝ × R3 × ℝ) × R3 => q.1.1 := by fun_prop
  have c2 : Continuous fun q : (ℝ × R3 × ℝ) × R3 => ‖q.1.2.1‖ := by fun_prop
  have c3 : Continuous fun q : (ℝ × R3 × ℝ) × R3 => q.1.2.2 := by fun_prop
  have c4 : Continuous fun q : (ℝ × R3 × ℝ) × R3 => q.1.2.2 * ‖q.2 - q.1.2.1‖ := by fun_prop
  have hcl : IsClosed (radialSet lam1 B s0 s1 ρ1 ρ2) :=
    ((isClosed_le continuous_const c1).inter ((isClosed_le c1 continuous_const).inter
      ((isClosed_le c2 continuous_const).inter ((isClosed_le continuous_const c3).inter
      (isClosed_le c3 continuous_const))))).inter
      ((isClosed_le continuous_const c4).inter (isClosed_le c4 continuous_const))
  refine (((isCompact_Icc (a := (0 : ℝ)) (b := lam1)).prod
    ((isCompact_closedBall (0 : R3) B).prod (isCompact_Icc (a := 1 / s1) (b := 1 / s0)))).prod
    (isCompact_closedBall (0 : R3) (B + ρ2 * s1))).of_isClosed_subset hcl ?_
  intro q hq
  have hd := radialSet_dist hs1 hq
  obtain ⟨⟨h0, hl, hc, hu, hu'⟩, -, -⟩ := hq
  have hy : ‖q.2‖ ≤ B + ρ2 * s1 := by
    have := norm_le_norm_add_norm_sub' q.2 q.1.2.1
    linarith
  exact ⟨⟨⟨h0, hl⟩, mem_closedBall_zero_iff.mpr hc, ⟨hu, hu'⟩⟩,
    mem_closedBall_zero_iff.mpr hy⟩

theorem isCompact_radialAnnulus (ρ1 ρ2 s1 : ℝ) (P : ℝ × R3 × ℝ)
    (hd : ∀ y ∈ radialAnnulus ρ1 ρ2 P, ‖y - P.2.1‖ ≤ ρ2 * s1) :
    IsCompact (radialAnnulus ρ1 ρ2 P) := by
  have hc : Continuous fun y : R3 => P.2.2 * ‖y - P.2.1‖ := by fun_prop
  refine (isCompact_closedBall P.2.1 (ρ2 * s1)).of_isClosed_subset
    ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)) ?_
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  exact hd y hy

theorem continuous_radial_quad (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (fun p : ((ℝ × R3 × ℝ) × R3) × (Fin 3 → ℝ) =>
      quad (radialCoeff g p.1.1) p.1.2 p.2) := by
  have hA : Continuous (fun q : (ℝ × R3 × ℝ) × R3 => fun i k => radialCoeff g q.1 i k q.2) :=
    continuous_pi fun i => continuous_pi fun k => (jointSmooth_radialCoeff g hg i k).continuous
  exact continuous_quad_form hA

theorem continuous_radial_E1 (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (fun p : ((ℝ × R3 × ℝ) × R3) × (Fin 3 → ℝ) =>
      E1 (radialCoeff g p.1.1) (radialWeight p.1.1) p.1.2 p.2) := by
  have haJ := jointSmooth_radialCoeff g hg
  have hψJ := jointSmooth_radialWeight
  have hA : Continuous (fun q : (ℝ × R3 × ℝ) × R3 => fun i k => radialCoeff g q.1 i k q.2) :=
    continuous_pi fun i => continuous_pi fun k => (haJ i k).continuous
  have hdB : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      fun i j => pd i (bv (radialCoeff g q.1) (radialWeight q.1) j) q.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      (jointSmooth_pd (F := fun q => bv (radialCoeff g q) (radialWeight q) j)
        (jointSmooth_bv haJ hψJ j) i).continuous
  have hdA : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      fun j i k => pd j (radialCoeff g q.1 i k) q.2) :=
    continuous_pi fun j => continuous_pi fun i => continuous_pi fun k =>
      (jointSmooth_pd (F := fun q => radialCoeff g q i k) (haJ i k) j).continuous
  have hb : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      fun j => bv (radialCoeff g q.1) (radialWeight q.1) j q.2) :=
    continuous_pi fun j => (jointSmooth_bv haJ hψJ j).continuous
  have h := continuous_E1_form hA hdB hdA hb
  exact h

theorem radialCoeff_quad_hom (g : MatrixField) (x : (ℝ × R3 × ℝ) × R3) (t : ℝ)
    (ξ : Fin 3 → ℝ) :
    quad (radialCoeff g x.1) x.2 (t • ξ) = t ^ 2 * quad (radialCoeff g x.1) x.2 ξ := by
  simp only [quad, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem radial_E1_hom (g : MatrixField) (x : (ℝ × R3 × ℝ) × R3) (t : ℝ) (ξ : Fin 3 → ℝ) :
    E1 (radialCoeff g x.1) (radialWeight x.1) x.2 (t • ξ) =
      t ^ 2 * E1 (radialCoeff g x.1) (radialWeight x.1) x.2 ξ := by
  simp only [E1, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem radial_Nf_pos (g : MatrixField) (hg : IsAdmissibleMetric g) {q : (ℝ × R3 × ℝ) × R3}
    (hu : q.1.2.2 ≠ 0) (hy : q.2 ≠ q.1.2.1) :
    0 < Nf (radialCoeff g q.1) (radialWeight q.1) q.2 := by
  have hne := grad_ne_zero_of_fderiv_ne (fderiv_radialWeight_ne_zero hu hy)
  have := radialCoeff_quad_pos g hg q.1 q.2 hne
  convert this using 1
  simp only [Nf_apply, bv_apply, quad, grad, Fin.sum_univ_three]
  ring

theorem radialCoeff_symm (g : MatrixField) (hg : IsAdmissibleMetric g) (P : ℝ × R3 × ℝ)
    (i k : Fin 3) : radialCoeff g P i k = radialCoeff g P k i := by
  funext y
  have := (EnergyBridge.principalCoefficient_posDef g hg (P.1 • y)).1.apply i k
  simpa [radialCoeff] using this.symm

section RadialBounds
variable (g : MatrixField) (hg : IsAdmissibleMetric g) (lam1 B s0 s1 ρ1 ρ2 : ℝ)
include hg

theorem radial_quad_lower (hs1 : 0 < s1) : ∃ α > 0, ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2,
    ∀ ξ : Fin 3 → ℝ, α * ‖ξ‖ ^ 2 ≤ quad (radialCoeff g q.1) q.2 ξ :=
  quad_lower_param (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1)
    (fun q ξ => quad (radialCoeff g q.1) q.2 ξ) (continuous_radial_quad g hg)
    (radialCoeff_quad_hom g) (fun q _ ξ hξ => radialCoeff_quad_pos g hg q.1 q.2 hξ)

theorem radial_E1_upper (hs1 : 0 < s1) : ∃ C, ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2,
    ∀ ξ : Fin 3 → ℝ, |E1 (radialCoeff g q.1) (radialWeight q.1) q.2 ξ| ≤ C * ‖ξ‖ ^ 2 :=
  quad_upper_param (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1)
    (fun q ξ => E1 (radialCoeff g q.1) (radialWeight q.1) q.2 ξ)
    (continuous_radial_E1 g hg) (radial_E1_hom g)

theorem radial_Nf_lower (hs1 : 0 < s1) (hρ1 : 0 < ρ1) : ∃ n > 0,
    ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2, n ≤ Nf (radialCoeff g q.1) (radialWeight q.1) q.2 := by
  have hNc : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      Nf (radialCoeff g q.1) (radialWeight q.1) q.2) :=
    (jointSmooth_Nf (jointSmooth_radialCoeff g hg) jointSmooth_radialWeight).continuous
  exact exists_pos_lower_of_compact (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1)
    hNc.continuousOn (fun q hq =>
      radial_Nf_pos g hg (radialSet_ne hs1 hρ1 hq).1 (radialSet_ne hs1 hρ1 hq).2)

theorem radial_Nf_upper (hs1 : 0 < s1) : ∃ C, ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2,
    |Nf (radialCoeff g q.1) (radialWeight q.1) q.2| ≤ C := by
  have hNc : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      Nf (radialCoeff g q.1) (radialWeight q.1) q.2) :=
    (jointSmooth_Nf (jointSmooth_radialCoeff g hg) jointSmooth_radialWeight).continuous
  exact exists_upper_of_compact (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1) hNc.continuousOn

theorem radial_Pf_upper (hs1 : 0 < s1) : ∃ C, ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2,
    |Pf (radialCoeff g q.1) (radialWeight q.1) q.2| ≤ C := by
  have hc : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      Pf (radialCoeff g q.1) (radialWeight q.1) q.2) :=
    (jointSmooth_Pf (jointSmooth_radialCoeff g hg) jointSmooth_radialWeight).continuous
  exact exists_upper_of_compact (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1) hc.continuousOn

theorem radial_Rf_upper (hs1 : 0 < s1) : ∀ Λ κ : ℝ, ∃ C, ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2,
    |Rf (radialCoeff g q.1) (radialWeight q.1) Λ κ q.2| ≤ C := by
  intro Λ κ
  have hc : Continuous (fun q : (ℝ × R3 × ℝ) × R3 =>
      Rf (radialCoeff g q.1) (radialWeight q.1) Λ κ q.2) :=
    (jointSmooth_Rf (jointSmooth_radialCoeff g hg) jointSmooth_radialWeight Λ κ).continuous
  exact exists_upper_of_compact (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1) hc.continuousOn

end RadialBounds

theorem radial_weight_upper (lam1 B s0 s1 ρ1 ρ2 : ℝ) (hs1 : 0 < s1) :
    ∃ C, ∀ q ∈ radialSet lam1 B s0 s1 ρ1 ρ2, |radialWeight q.1 q.2| ≤ C := by
  have hc : Continuous (fun q : (ℝ × R3 × ℝ) × R3 => radialWeight q.1 q.2) :=
    jointSmooth_radialWeight.continuous
  exact exists_upper_of_compact (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1) hc.continuousOn

theorem radialCoeff_contDiff (g : MatrixField) (hg : IsAdmissibleMetric g) (P : ℝ × R3 × ℝ)
    (i k : Fin 3) : ContDiff ℝ ∞ (radialCoeff g P i k) := by
  have h1 : ContDiff ℝ ∞ (fun x : R3 => EnergyBridge.principalCoefficient g x i k) :=
    EnergyBridge.contDiff_principalCoefficient_entry g hg i k
  have h2 : ContDiff ℝ ∞ (fun y : R3 => P.1 • y) := by fun_prop
  have h := h1.comp h2
  exact h

theorem radialWeight_contDiff (P : ℝ × R3 × ℝ) : ContDiff ℝ ∞ (radialWeight P) := by
  have hJ : ContDiff ℝ ∞ (fun q : (ℝ × R3 × ℝ) × R3 => radialWeight q.1 q.2) :=
    jointSmooth_radialWeight
  have hi : ContDiff ℝ ∞ (fun y : R3 => ((P, y) : (ℝ × R3 × ℝ) × R3)) := by fun_prop
  have h := hJ.comp hi
  exact h

/-- The `P`-slice `{y | (P, y) ∈ G}` (empty unless `P` is an admissible parameter). -/
def radialSlice (lam1 B s0 s1 ρ1 ρ2 : ℝ) (P : ℝ × R3 × ℝ) : Set R3 :=
  {y | ((P, y) : (ℝ × R3 × ℝ) × R3) ∈ radialSet lam1 B s0 s1 ρ1 ρ2}

theorem isCompact_radialSlice (lam1 B s0 s1 ρ1 ρ2 : ℝ) (hs1 : 0 < s1) (P : ℝ × R3 × ℝ) :
    IsCompact (radialSlice lam1 B s0 s1 ρ1 ρ2 P) := by
  have hcl : IsClosed (radialSlice lam1 B s0 s1 ρ1 ρ2 P) :=
    (isCompact_radialSet lam1 B s0 s1 ρ1 ρ2 hs1).isClosed.preimage
      (by fun_prop : Continuous fun y : R3 => ((P, y) : (ℝ × R3 × ℝ) × R3))
  refine (isCompact_closedBall P.2.1 (ρ2 * s1)).of_isClosed_subset hcl ?_
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  exact radialSet_dist (q := (P, y)) hs1 hy

/-- U2: the uniform estimate on the `u`-parametrized compact family. -/
theorem radial_carleman_param (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 ρ1 ρ2 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) (hρ1 : 0 < ρ1) :
    ∃ Λ τ0 : ℝ, 0 < Λ ∧ ∀ P ∈ radialParams lam1 B s0 s1, ∀ τ : ℝ, τ0 ≤ τ →
      ∀ w : R3 → ℝ, ContDiff ℝ ∞ w → tsupport w ⊆ radialAnnulus ρ1 ρ2 P →
      (∫ x, Real.exp (2 * τ * phi (radialWeight P) Λ x) * w x ^ 2) ≤
        ∫ x, Real.exp (2 * τ * phi (radialWeight P) Λ x) * Lop (radialCoeff g P) w x ^ 2 := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨α, hα, hαG⟩ := radial_quad_lower g hg lam1 B s0 s1 ρ1 ρ2 hs1
  obtain ⟨C₁, hC₁⟩ := radial_E1_upper g hg lam1 B s0 s1 ρ1 ρ2 hs1
  obtain ⟨n₀, hn₀, hn₀G⟩ := radial_Nf_lower g hg lam1 B s0 s1 ρ1 ρ2 hs1 hρ1
  obtain ⟨N₁, hN₁⟩ := radial_Nf_upper g hg lam1 B s0 s1 ρ1 ρ2 hs1
  obtain ⟨C₂, hC₂⟩ := radial_Pf_upper g hg lam1 B s0 s1 ρ1 ρ2 hs1
  obtain ⟨Ψ, hΨ⟩ := radial_weight_upper lam1 B s0 s1 ρ1 ρ2 hs1
  have hR := radial_Rf_upper g hg lam1 B s0 s1 ρ1 ρ2 hs1
  have hK : ∀ P : ℝ × R3 × ℝ, IsCompact (radialSlice lam1 B s0 s1 ρ1 ρ2 P) :=
    isCompact_radialSlice lam1 B s0 s1 ρ1 ρ2 hs1
  obtain ⟨Λ, τ0, hΛ, H⟩ := carleman_family_of_bounds (radialCoeff g) radialWeight
    (radialSlice lam1 B s0 s1 ρ1 ρ2) (radialCoeff_contDiff g hg) (radialCoeff_symm g hg)
    radialWeight_contDiff hK hα hn₀
    (fun P y hy ξ => hαG (P, y) hy ξ) (fun P y hy ξ => hC₁ (P, y) hy ξ)
    (fun P y hy => hn₀G (P, y) hy) (fun P y hy => hN₁ (P, y) hy)
    (fun P y hy => hC₂ (P, y) hy) (fun P y hy => hΨ (P, y) hy)
    (fun Λ κ => by
      obtain ⟨D, hD⟩ := hR Λ κ
      exact ⟨D, fun P y hy => hD (P, y) hy⟩)
  refine ⟨Λ, τ0, hΛ, fun P hP τ hτ w hw hsub => ?_⟩
  have hsub' : tsupport w ⊆ radialSlice lam1 B s0 s1 ρ1 ρ2 P := fun y hy => ⟨hP, hsub hy⟩
  have h := H P τ hτ w hw hsub'
  exact h

/-- U2b: ONE convexification `Λ` and ONE `τ0` for the actual coefficient family
`principalCoefficient g (lam • y)`, `lam ∈ [0, lam1]`, every center `‖c‖ ≤ B`, every scale
`s ∈ [s0, s1]`, with the radial weight `-‖y - c‖²/s²` and the annular support
`ρ1 s ≤ ‖y - c‖ ≤ ρ2 s`. All constants are compact bounds of actual jointly smooth functions. -/
theorem uniform_radial_carleman (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 ρ1 ρ2 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) (hρ1 : 0 < ρ1) :
    ∃ Λ τ0 : ℝ, 0 < Λ ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B →
      ∀ s ∈ Icc s0 s1, ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ {y | ρ1 * s ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ ρ2 * s} →
      (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) * w y ^ 2) ≤
        ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y ^ 2 := by
  obtain ⟨Λ, τ0, hΛ, H⟩ := radial_carleman_param g hg lam1 B s0 s1 ρ1 ρ2 hs0 hss hρ1
  refine ⟨Λ, τ0, hΛ, fun lam hlam c hc s hs τ hτ w hw hsupp => ?_⟩
  have hs0' : 0 < s := hs0.trans_le hs.1
  have hP : ((lam, c, 1 / s) : ℝ × R3 × ℝ) ∈ radialParams lam1 B s0 s1 :=
    ⟨hlam.1, hlam.2, hc, one_div_le_one_div_of_le hs0' hs.2, one_div_le_one_div_of_le hs0 hs.1⟩
  have hsub : tsupport w ⊆ radialAnnulus ρ1 ρ2 (lam, c, 1 / s) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsupp hy
    show ρ1 ≤ 1 / s * ‖y - c‖ ∧ 1 / s * ‖y - c‖ ≤ ρ2
    rw [one_div_mul_eq_div]
    exact ⟨(le_div_iff₀ hs0').mpr h1, (div_le_iff₀ hs0').mpr h2⟩
  have key := H _ hP τ hτ w hw hsub
  have e : ∀ y : R3, Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2)) =
      phi (radialWeight (lam, c, 1 / s)) Λ y := by
    intro y
    show Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2)) = Real.exp (Λ * -(‖y - c‖ ^ 2 * (1 / s) ^ 2))
    rw [div_pow, one_pow, mul_one_div]
  simp only [e]
  exact key

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v048: uniform cutoff residual, Caccioppoli and three-ball (V1-V4 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

/-- V1: one fixed annular cutoff profile on the squared radius. -/
def cutProfile (a b c d t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a ^ 2) / (b ^ 2 - a ^ 2)) *
    (1 - Real.smoothTransition ((t - c ^ 2) / (d ^ 2 - c ^ 2)))

/-- V1: one fixed plateau profile on the squared radius. -/
def plateauProfile (k m t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - k ^ 2) / (m ^ 2 - k ^ 2))

theorem contDiff_cutProfile (a b c d : ℝ) : ContDiff ℝ ∞ (cutProfile a b c d) := by
  unfold cutProfile
  fun_prop

theorem contDiff_plateauProfile (k m : ℝ) : ContDiff ℝ ∞ (plateauProfile k m) := by
  unfold plateauProfile
  fun_prop

theorem cutProfile_eq_zero_of_le {a b c d t : ℝ} (hab : a ^ 2 < b ^ 2) (ht : t ≤ a ^ 2) :
    cutProfile a b c d t = 0 := by
  have hw : 0 < b ^ 2 - a ^ 2 := by linarith
  unfold cutProfile
  rw [Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hw]; linarith), zero_mul]

theorem cutProfile_eq_zero_of_ge {a b c d t : ℝ} (hcd : c ^ 2 < d ^ 2) (ht : d ^ 2 ≤ t) :
    cutProfile a b c d t = 0 := by
  have hw : 0 < d ^ 2 - c ^ 2 := by linarith
  have hA : Real.smoothTransition ((t - c ^ 2) / (d ^ 2 - c ^ 2)) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith)
  unfold cutProfile
  rw [hA, sub_self, mul_zero]

theorem cutProfile_eq_one {a b c d t : ℝ} (hab : a ^ 2 < b ^ 2) (hcd : c ^ 2 < d ^ 2)
    (h1 : b ^ 2 ≤ t) (h2 : t ≤ c ^ 2) : cutProfile a b c d t = 1 := by
  have hw1 : 0 < b ^ 2 - a ^ 2 := by linarith
  have hw2 : 0 < d ^ 2 - c ^ 2 := by linarith
  unfold cutProfile
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw1]; linarith),
    Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hw2]; linarith)]
  ring

theorem cutProfile_ne_zero {a b c d t : ℝ} (hab : a ^ 2 < b ^ 2) (hcd : c ^ 2 < d ^ 2)
    (h : cutProfile a b c d t ≠ 0) : a ^ 2 < t ∧ t < d ^ 2 := by
  constructor
  · by_contra hn
    exact h (cutProfile_eq_zero_of_le hab (not_lt.mp hn))
  · by_contra hn
    exact h (cutProfile_eq_zero_of_ge hcd (not_lt.mp hn))

theorem plateauProfile_eq_one {k m t : ℝ} (hkm : k ^ 2 < m ^ 2) (ht : t ≤ k ^ 2) :
    plateauProfile k m t = 1 := by
  have hw : 0 < m ^ 2 - k ^ 2 := by linarith
  unfold plateauProfile
  rw [Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hw]; linarith), sub_zero]

theorem plateauProfile_ne_zero {k m t : ℝ} (hkm : k ^ 2 < m ^ 2)
    (h : plateauProfile k m t ≠ 0) : t < m ^ 2 := by
  have hw : 0 < m ^ 2 - k ^ 2 := by linarith
  by_contra hn
  apply h
  unfold plateauProfile
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith [not_lt.mp hn]),
    sub_self]

theorem sqScaled_eq (x : R3) (s : ℝ) : ‖x‖ ^ 2 * (1 / s) ^ 2 = (‖x‖ / s) ^ 2 := by
  rw [← mul_pow, mul_one_div]

theorem sqScaled_lt_iff {x : R3} {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    ‖x‖ ^ 2 * (1 / s) ^ 2 < r ^ 2 ↔ ‖x‖ < r * s := by
  rw [sqScaled_eq, sq_lt_sq₀ (div_nonneg (norm_nonneg _) hs.le) hr, div_lt_iff₀ hs]

theorem sqScaled_le_iff {x : R3} {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    ‖x‖ ^ 2 * (1 / s) ^ 2 ≤ r ^ 2 ↔ ‖x‖ ≤ r * s := by
  rw [sqScaled_eq, sq_le_sq₀ (div_nonneg (norm_nonneg _) hs.le) hr, div_le_iff₀ hs]

/-- V1: a profile of the squared scaled radius `‖y - c‖² u²` is jointly smooth in `(P, y)`. -/
theorem jointSmooth_profile {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    JointSmooth fun (P : ℝ × R3 × ℝ) (y : R3) => F (‖y - P.2.1‖ ^ 2 * P.2.2 ^ 2) :=
  hF.comp ((ContDiff.norm_sq ℝ (contDiff_snd.sub contDiff_fst.snd.fst)).mul
    (contDiff_fst.snd.snd.pow 2))

theorem contDiff_profile_slice {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (c : R3) (u : ℝ) :
    ContDiff ℝ ∞ (fun y : R3 => F (‖y - c‖ ^ 2 * u ^ 2)) :=
  hF.comp ((ContDiff.norm_sq ℝ (contDiff_id.sub contDiff_const)).mul contDiff_const)

/-- V2: ONE pointwise cutoff-residual constant for the actual dilated coefficient family and a
fixed profile `F`, uniform in `lam ∈ [0, lam1]`, `‖c‖ ≤ B`, `s ∈ [s0, s1]`. -/
theorem uniform_cutoff_residual_pointwise (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 k1 k2 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B → ∀ s ∈ Icc s0 s1,
      ∀ y : R3, k1 * s ≤ ‖y - c‖ → ‖y - c‖ ≤ k2 * s →
      ∀ D : Set R3, IsOpen D → ∀ q : R3 → ℝ, ContDiffOn ℝ ∞ q D → y ∈ D →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0 →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
          (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2) * q z) y ^ 2 ≤
        M * (q y ^ 2 + ∑ j, pd j q y ^ 2) := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  have hχJ : JointSmooth fun (P : ℝ × R3 × ℝ) (y : R3) => F (‖y - P.2.1‖ ^ 2 * P.2.2 ^ 2) :=
    jointSmooth_profile hF
  have haJ := jointSmooth_radialCoeff g hg
  have hLc : Continuous (fun x : (ℝ × R3 × ℝ) × R3 =>
      Lop (radialCoeff g x.1) (fun y => F (‖y - x.1.2.1‖ ^ 2 * x.1.2.2 ^ 2)) x.2) :=
    (jointSmooth_Lop haJ hχJ).continuous
  have hbc : ∀ j : Fin 3, Continuous (fun x : (ℝ × R3 × ℝ) × R3 =>
      2 * ∑ i, radialCoeff g x.1 i j x.2 *
        pd i (fun y => F (‖y - x.1.2.1‖ ^ 2 * x.1.2.2 ^ 2)) x.2) := fun j =>
    (jointSmooth_const_mul 2 (jointSmooth_sum
      (F := fun i (P : ℝ × R3 × ℝ) y => radialCoeff g P i j y *
        pd i (fun y => F (‖y - P.2.1‖ ^ 2 * P.2.2 ^ 2)) y)
      (fun i => jointSmooth_mul (haJ i j) (jointSmooth_pd hχJ i)))).continuous
  obtain ⟨M0, hM0⟩ := exists_upper_of_compact (isCompact_radialSet lam1 B s0 s1 k1 k2 hs1)
    ((hLc.pow 2).add (continuous_finsetSum _ fun j _ => (hbc j).pow 2)).continuousOn
  refine ⟨max M0 0, le_max_right _ _, ?_⟩
  intro lam hlam c hc s hs y hy1 hy2 D hD q hq hyD hLq
  have hs' : 0 < s := hs0.trans_le hs.1
  have hmem : (((lam, c, 1 / s), y) : (ℝ × R3 × ℝ) × R3) ∈ radialSet lam1 B s0 s1 k1 k2 := by
    refine ⟨⟨hlam.1, hlam.2, hc, one_div_le_one_div_of_le hs' hs.2,
      one_div_le_one_div_of_le hs0 hs.1⟩, ?_, ?_⟩
    · show k1 ≤ 1 / s * ‖y - c‖
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hs').mpr hy1
    · show 1 / s * ‖y - c‖ ≤ k2
      rw [one_div_mul_eq_div]
      exact (div_le_iff₀ hs').mpr hy2
  have hbound : Lop (radialCoeff g (lam, c, 1 / s)) (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2)) y ^ 2 +
      ∑ j, (2 * ∑ i, radialCoeff g (lam, c, 1 / s) i j y *
        pd i (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2)) y) ^ 2 ≤ max M0 0 :=
    (le_abs_self _).trans ((hM0 _ hmem).trans (le_max_left _ _))
  have hLq' : Lop (radialCoeff g (lam, c, 1 / s)) q y = 0 := hLq
  have hcomm := local_Lop_mul_symm (radialCoeff g (lam, c, 1 / s)) (radialCoeff_contDiff g hg _)
    (fun i j x => congrFun (radialCoeff_symm g hg _ i j) x) hD
    (contDiff_profile_slice hF c (1 / s)) hq hyD
  beta_reduce at hcomm
  rw [hLq', mul_zero, zero_add] at hcomm
  have hexp : Lop (radialCoeff g (lam, c, 1 / s))
      (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2) * q z) y =
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2)) y * q y +
        ∑ j, (2 * ∑ i, radialCoeff g (lam, c, 1 / s) i j y *
          pd i (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2)) y) * pd j q y := by
    rw [hcomm]
    simp only [Fin.sum_univ_three]
    ring
  show Lop (radialCoeff g (lam, c, 1 / s))
    (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2) * q z) y ^ 2 ≤ _
  rw [hexp]
  refine (affine_three_sq_le _ (q y) (fun j => 2 * ∑ i, radialCoeff g (lam, c, 1 / s) i j y *
    pd i (fun z => F (‖z - c‖ ^ 2 * (1 / s) ^ 2)) y) (fun j => pd j q y)).trans ?_
  exact mul_le_mul_of_nonneg_right hbound
    (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))

theorem sum_sq_le_three_norm_sq (ξ : Fin 3 → ℝ) : ∑ i, ξ i ^ 2 ≤ 3 * ‖ξ‖ ^ 2 := by
  have h : ∀ i, ξ i ^ 2 ≤ ‖ξ‖ ^ 2 := fun i => by
    have h1 : |ξ i| ≤ ‖ξ‖ := by
      have := norm_le_pi_norm ξ i
      rwa [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  simp only [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem bilinear_sq_le (A : Fin 3 → Fin 3 → ℝ) (ζ ξ : Fin 3 → ℝ) :
    (∑ i, ∑ k, ζ i * A i k * ξ k) ^ 2 ≤
      (∑ i, ζ i ^ 2) * ((∑ i, ∑ k, A i k ^ 2) * ∑ k, ξ k ^ 2) := by
  have e : ∑ i, ∑ k, ζ i * A i k * ξ k = ∑ i, ζ i * ∑ k, A i k * ξ k :=
    Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- V3 (one instance): Caccioppoli on `closedBall c rk` from EXPLICIT cutoff, ellipticity and
gradient bounds; the per-`q` plateau only provides smoothness and enters no constant. -/
theorem caccioppoli_of_cutoff_bounds {a : Fin 3 → Fin 3 → R3 → ℝ}
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {c : R3} {rk rm re lamE Λ Mη : ℝ} (hmre : rm < re)
    (hl : 0 < lamE) (hMη : 0 ≤ Mη) {et : R3 → ℝ} (het : ContDiff ℝ ∞ et)
    (hne : ∀ y, et y ≠ 0 → ‖y - c‖ < rm) (hone : ∀ y, ‖y - c‖ ≤ rk → et y = 1)
    (hgrad : ∀ y, ‖y - c‖ ≤ rm → ∑ i, pd i et y ^ 2 ≤ Mη)
    (hlow : ∀ y, ‖y - c‖ ≤ rm → ∀ ξ : Fin 3 → ℝ,
      lamE * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ k, ξ i * a i k y * ξ k)
    (hup : ∀ y, ‖y - c‖ ≤ rm → ∀ ζ ξ : Fin 3 → ℝ,
      (∑ i, ∑ k, ζ i * a i k y * ξ k) ^ 2 ≤ Λ ^ 2 * (∑ i, ζ i ^ 2) * ∑ k, ξ k ^ 2)
    {q : R3 → ℝ} (hq : ContDiffOn ℝ ∞ q (ball c re)) (hL : ∀ y ∈ ball c re, Lop a q y = 0)
    (hint : IntegrableOn (fun y => q y ^ 2) (ball c re)) :
    ∫ y in closedBall c rk, ∑ j, pd j q y ^ 2 ≤
      (2 * Λ / lamE) ^ 2 * Mη * ∫ y in ball c re, q y ^ 2 := by
  have hts : tsupport et ⊆ closedBall c rm := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_eq_norm]
    exact (hne y hy).le
  have hetcs : HasCompactSupport et :=
    (isCompact_closedBall c rm).of_isClosed_subset (isClosed_tsupport _) hts
  have htsE : tsupport et ⊆ ball c re := hts.trans (closedBall_subset_ball hmre)
  obtain ⟨zeta, hz, -, hzE, hz1⟩ :=
    CutoffCommutator.exists_plateau_cutoff isOpen_ball hetcs htsE
  have hv : ContDiff ℝ ∞ (fun y => zeta y * q y) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball hz hzE hq
  have hgerm : ∀ y ∈ tsupport et, (fun y => zeta y * q y) =ᶠ[𝓝 y] q := fun y hy => by
    filter_upwards [hz1 y hy] with z hz'
    rw [hz', one_mul]
  have hval : ∀ y ∈ tsupport et, zeta y * q y = q y := fun y hy => (hgerm y hy).eq_of_nhds
  have hin : ∀ y, et y ≠ 0 → ‖y - c‖ ≤ rm := fun y hy => (hne y hy).le
  have hcac := CutoffCommutator.caccioppoli_of_ellipticity ha het hetcs hv
    (fun y hy => by
      rw [CutoffCommutator.Lop_congr_of_eventuallyEq a (hgerm y (subset_tsupport et hy))]
      exact hL y (htsE (subset_tsupport et hy)))
    hl (fun y hy => hlow y (hin y hy)) (fun y hy => hup y (hin y hy))
  beta_reduce at hcac
  have hI1 : Integrable (fun x => et x ^ 2 * ∑ i, pd i (fun y => zeta y * q y) x ^ 2) :=
    CutoffCommutator.integrable_of_eta_factor hetcs
      ((het.pow 2).mul (ContDiff.sum fun i _ => (contDiff_pd hv).pow 2))
      (fun x h => by simp [h])
  have hlow1 : ∫ y in closedBall c rk, ∑ j, pd j q y ^ 2 ≤
      ∫ x, et x ^ 2 * ∑ i, pd i (fun y => zeta y * q y) x ^ 2 := by
    have heq : ∫ y in closedBall c rk, ∑ j, pd j q y ^ 2 =
        ∫ y in closedBall c rk, et y ^ 2 * ∑ i, pd i (fun y => zeta y * q y) y ^ 2 := by
      refine setIntegral_congr_fun measurableSet_closedBall (fun y hy => ?_)
      have hy' : ‖y - c‖ ≤ rk := by rwa [mem_closedBall, dist_eq_norm] at hy
      have h1 : et y = 1 := hone y hy'
      have hyK : y ∈ tsupport et := subset_tsupport et (show et y ≠ 0 by rw [h1]; exact one_ne_zero)
      have hp : ∀ i, pd i (fun y => zeta y * q y) y = pd i q y := fun i =>
        CutoffCommutator.pd_congr_of_eventuallyEq (hgerm y hyK) i
      simp only [h1, hp, one_pow, one_mul]
    rw [heq]
    exact setIntegral_le_integral hI1 (Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hI2 : Integrable (fun x => (zeta x * q x) ^ 2 * ∑ i, pd i et x ^ 2) := by
    refine ((hv.pow 2).mul (ContDiff.sum fun i _ =>
      (contDiff_pd het).pow 2)).continuous.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (show IsCompact (tsupport et) from hetcs) (fun x hx => ?_)
    have h0 : ∀ i, pd i et x = 0 := fun i => CutoffCommutator.pd_eq_zero_of_not_mem_tsupport hx i
    simp [h0]
  have hpt : ∀ x, (zeta x * q x) ^ 2 * ∑ i, pd i et x ^ 2 ≤
      Mη * (ball c re).indicator (fun y => q y ^ 2) x := by
    intro x
    by_cases hx : x ∈ tsupport et
    · rw [indicator_of_mem (htsE hx), hval x hx]
      have hx' : ‖x - c‖ ≤ rm := by
        have := hts hx
        rwa [mem_closedBall, dist_eq_norm] at this
      have := mul_le_mul_of_nonneg_left (hgrad x hx') (sq_nonneg (q x))
      linarith
    · have h0 : ∑ i, pd i et x ^ 2 = 0 := by
        simp [fun i => CutoffCommutator.pd_eq_zero_of_not_mem_tsupport hx i]
      rw [h0, mul_zero]
      exact mul_nonneg hMη (indicator_nonneg (fun y _ => sq_nonneg (q y)) x)
  have hup1 : ∫ x, (zeta x * q x) ^ 2 * ∑ i, pd i et x ^ 2 ≤ Mη * ∫ y in ball c re, q y ^ 2 := by
    have h := integral_mono hI2 ((hint.integrable_indicator measurableSet_ball).const_mul Mη) hpt
    rwa [integral_const_mul, integral_indicator measurableSet_ball] at h
  calc ∫ y in closedBall c rk, ∑ j, pd j q y ^ 2
      ≤ ∫ x, et x ^ 2 * ∑ i, pd i (fun y => zeta y * q y) x ^ 2 := hlow1
    _ ≤ (2 * Λ / lamE) ^ 2 * ∫ x, (zeta x * q x) ^ 2 * ∑ i, pd i et x ^ 2 := hcac
    _ ≤ (2 * Λ / lamE) ^ 2 * (Mη * ∫ y in ball c re, q y ^ 2) :=
        mul_le_mul_of_nonneg_left hup1 (sq_nonneg _)
    _ = (2 * Λ / lamE) ^ 2 * Mη * ∫ y in ball c re, q y ^ 2 := by ring

/-- V3: ONE Caccioppoli constant for the actual dilated coefficient family, uniform in
`lam ∈ [0, lam1]`, `‖c‖ ≤ B`, `s ∈ [s0, s1]`, before the local solution `q`. -/
theorem uniform_caccioppoli (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 k m e : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) (hk : 0 ≤ k) (hkm : k < m)
    (hme : m < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B → ∀ s ∈ Icc s0 s1,
      ∀ q : R3 → ℝ, ContDiffOn ℝ ∞ q (ball c (e * s)) →
      (∀ y ∈ ball c (e * s),
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0) →
      IntegrableOn (fun y => q y ^ 2) (ball c (e * s)) →
      ∫ y in closedBall c (k * s), ∑ j, pd j q y ^ 2 ≤ C * ∫ y in ball c (e * s), q y ^ 2 := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  have hm : 0 < m := hk.trans_lt hkm
  have hkm2 : k ^ 2 < m ^ 2 := by nlinarith
  have hηJ : JointSmooth fun (P : ℝ × R3 × ℝ) (y : R3) =>
      plateauProfile k m (‖y - P.2.1‖ ^ 2 * P.2.2 ^ 2) :=
    jointSmooth_profile (contDiff_plateauProfile k m)
  have haJ := jointSmooth_radialCoeff g hg
  have hG := isCompact_radialSet lam1 B s0 s1 0 m hs1
  obtain ⟨α, hα, hαG⟩ := radial_quad_lower g hg lam1 B s0 s1 0 m hs1
  have hNc : Continuous (fun x : (ℝ × R3 × ℝ) × R3 =>
      ∑ i, ∑ k, radialCoeff g x.1 i k x.2 ^ 2) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ =>
      (haJ i k).continuous.pow 2
  have hMc : Continuous (fun x : (ℝ × R3 × ℝ) × R3 =>
      ∑ i, pd i (fun y => plateauProfile k m (‖y - x.1.2.1‖ ^ 2 * x.1.2.2 ^ 2)) x.2 ^ 2) :=
    continuous_finsetSum _ fun i _ => (jointSmooth_pd hηJ i).continuous.pow 2
  obtain ⟨N, hN⟩ := exists_upper_of_compact hG hNc.continuousOn
  obtain ⟨Mη, hMη⟩ := exists_upper_of_compact hG hMc.continuousOn
  refine ⟨(2 * max N 1 / (α / 3)) ^ 2 * max Mη 0, by positivity, ?_⟩
  intro lam hlam c hc s hs q hq hL hint
  have hs' : 0 < s := hs0.trans_le hs.1
  have hP : ((lam, c, 1 / s) : ℝ × R3 × ℝ) ∈ radialParams lam1 B s0 s1 :=
    ⟨hlam.1, hlam.2, hc, one_div_le_one_div_of_le hs' hs.2, one_div_le_one_div_of_le hs0 hs.1⟩
  have hmemG : ∀ y : R3, ‖y - c‖ ≤ m * s →
      (((lam, c, 1 / s), y) : (ℝ × R3 × ℝ) × R3) ∈ radialSet lam1 B s0 s1 0 m := by
    intro y hy
    refine ⟨hP, ?_, ?_⟩
    · show (0 : ℝ) ≤ 1 / s * ‖y - c‖
      positivity
    · show 1 / s * ‖y - c‖ ≤ m
      rw [one_div_mul_eq_div]
      exact (div_le_iff₀ hs').mpr hy
  exact caccioppoli_of_cutoff_bounds (a := radialCoeff g (lam, c, 1 / s))
    (radialCoeff_contDiff g hg _) (c := c) (rk := k * s) (rm := m * s) (re := e * s)
    (lamE := α / 3) (Λ := max N 1) (Mη := max Mη 0)
    (mul_lt_mul_of_pos_right hme hs') (by positivity) (le_max_right _ _)
    (et := fun y => plateauProfile k m (‖y - c‖ ^ 2 * (1 / s) ^ 2))
    (contDiff_profile_slice (contDiff_plateauProfile k m) c (1 / s))
    (fun y hy => (sqScaled_lt_iff hs' hm.le).mp (plateauProfile_ne_zero hkm2 hy))
    (fun y hy => plateauProfile_eq_one hkm2 ((sqScaled_le_iff hs' hk).mpr hy))
    (fun y hy => (le_abs_self _).trans ((hMη _ (hmemG y hy)).trans (le_max_left _ _)))
    (fun y hy ξ => by
      have h1 : α * ‖ξ‖ ^ 2 ≤ quad (radialCoeff g (lam, c, 1 / s)) y ξ :=
        hαG _ (hmemG y hy) ξ
      have h2 := mul_le_mul_of_nonneg_left (sum_sq_le_three_norm_sq ξ)
        (by positivity : (0 : ℝ) ≤ α / 3)
      have e1 : quad (radialCoeff g (lam, c, 1 / s)) y ξ =
          ∑ i, ∑ k, ξ i * radialCoeff g (lam, c, 1 / s) i k y * ξ k := by
        simp only [quad, Fin.sum_univ_three]
        ring
      linarith)
    (fun y hy ζ ξ => by
      have hNy : ∑ i, ∑ k, radialCoeff g (lam, c, 1 / s) i k y ^ 2 ≤ max N 1 ^ 2 := by
        have h1 := (le_abs_self _).trans (hN _ (hmemG y hy))
        have hM1 : (1 : ℝ) ≤ max N 1 := le_max_right _ _
        have hM : max N 1 ≤ max N 1 ^ 2 := by nlinarith
        exact h1.trans ((le_max_left N 1).trans hM)
      have hζ : 0 ≤ ∑ i, ζ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hξ : 0 ≤ ∑ k, ξ k ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      calc _ ≤ (∑ i, ζ i ^ 2) * ((∑ i, ∑ k, radialCoeff g (lam, c, 1 / s) i k y ^ 2) *
            ∑ k, ξ k ^ 2) := bilinear_sq_le (fun i k => radialCoeff g (lam, c, 1 / s) i k y) ζ ξ
        _ ≤ (∑ i, ζ i ^ 2) * (max N 1 ^ 2 * ∑ k, ξ k ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNy hξ) hζ
        _ = _ := by ring)
    hq hL hint

/-- Closed annulus `r1 ≤ ‖y - c‖ ≤ r2`. -/
def closedAnnulus (c : R3) (r1 r2 : ℝ) : Set R3 := {y | r1 ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ r2}

theorem isClosed_closedAnnulus (c : R3) (r1 r2 : ℝ) : IsClosed (closedAnnulus c r1 r2) := by
  have hc : Continuous fun y : R3 => ‖y - c‖ := by fun_prop
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem isCompact_closedAnnulus (c : R3) (r1 r2 : ℝ) : IsCompact (closedAnnulus c r1 r2) :=
  (isCompact_closedBall c r2).of_isClosed_subset (isClosed_closedAnnulus c r1 r2)
    (fun y hy => by rw [mem_closedBall, dist_eq_norm]; exact hy.2)

theorem closedAnnulus_subset_ball {c : R3} {r1 r2 R : ℝ} (h : r2 < R) :
    closedAnnulus c r1 r2 ⊆ ball c R :=
  fun y hy => mem_ball_iff_norm.mpr (lt_of_le_of_lt hy.2 h)

/-- The fixed three-ball cutoff: `0` for `‖y-c‖ ≤ s/4` and `≥ 3s`, `1` on `[s/2, 5s/2]`. -/
def threeBallCut (c : R3) (s : ℝ) (y : R3) : ℝ :=
  cutProfile (1 / 4) (1 / 2) (5 / 2) 3 (‖y - c‖ ^ 2 * (1 / s) ^ 2)

theorem contDiff_threeBallCut (c : R3) (s : ℝ) : ContDiff ℝ ∞ (threeBallCut c s) :=
  contDiff_profile_slice (contDiff_cutProfile _ _ _ _) c (1 / s)

theorem threeBallCut_ne_zero (c : R3) {s : ℝ} (hs : 0 < s) {y : R3}
    (h : threeBallCut c s y ≠ 0) : 1 / 4 * s < ‖y - c‖ ∧ ‖y - c‖ < 3 * s := by
  obtain ⟨h1, h2⟩ := cutProfile_ne_zero (by norm_num) (by norm_num) h
  exact ⟨not_le.mp fun h' => (not_lt.mpr ((sqScaled_le_iff hs (by norm_num)).mpr h')) h1,
    (sqScaled_lt_iff hs (by norm_num)).mp h2⟩

theorem threeBallCut_eq_one (c : R3) {s : ℝ} (hs : 0 < s) {y : R3}
    (h1 : 1 / 2 * s ≤ ‖y - c‖) (h2 : ‖y - c‖ ≤ 5 / 2 * s) : threeBallCut c s y = 1 :=
  cutProfile_eq_one (by norm_num) (by norm_num)
    (not_lt.mp fun h => absurd ((sqScaled_lt_iff hs (by norm_num)).mp h) (not_lt.mpr h1))
    ((sqScaled_le_iff hs (by norm_num)).mpr h2)

theorem tsupport_threeBallCut (c : R3) {s : ℝ} (hs : 0 < s) :
    tsupport (threeBallCut c s) ⊆ closedAnnulus c (1 / 4 * s) (3 * s) :=
  closure_minimal (fun y hy => ⟨(threeBallCut_ne_zero c hs hy).1.le,
    (threeBallCut_ne_zero c hs hy).2.le⟩) (isClosed_closedAnnulus _ _ _)

theorem threeBallCut_dich (c : R3) {s : ℝ} (hs : 0 < s) :
    ∀ x, x ∉ closedAnnulus c (1 / 4 * s) (1 / 2 * s) ∪ closedAnnulus c (5 / 2 * s) (3 * s) →
      threeBallCut c s =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) ∨
        threeBallCut c s =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  intro x hx
  have htc : Continuous (fun y : R3 => ‖y - c‖ ^ 2 * (1 / s) ^ 2) := by fun_prop
  simp only [closedAnnulus, mem_union, mem_setOf_eq, not_or, not_and_or, not_le] at hx
  obtain ⟨h1 | h1, h2 | h2⟩ := hx
  · left
    have hlt : ‖x - c‖ ^ 2 * (1 / s) ^ 2 < (1 / 4) ^ 2 :=
      (sqScaled_lt_iff hs (by norm_num)).mpr h1
    filter_upwards [(isOpen_lt htc continuous_const).mem_nhds hlt] with y hy
    exact cutProfile_eq_zero_of_le (by norm_num) (le_of_lt hy)
  · left
    have hlt : ‖x - c‖ ^ 2 * (1 / s) ^ 2 < (1 / 4) ^ 2 :=
      (sqScaled_lt_iff hs (by norm_num)).mpr h1
    filter_upwards [(isOpen_lt htc continuous_const).mem_nhds hlt] with y hy
    exact cutProfile_eq_zero_of_le (by norm_num) (le_of_lt hy)
  · right
    have hlt1 : (1 / 2) ^ 2 < ‖x - c‖ ^ 2 * (1 / s) ^ 2 :=
      not_le.mp fun h => absurd ((sqScaled_le_iff hs (by norm_num)).mp h) (not_le.mpr h1)
    have hlt2 : ‖x - c‖ ^ 2 * (1 / s) ^ 2 < (5 / 2) ^ 2 :=
      (sqScaled_lt_iff hs (by norm_num)).mpr h2
    filter_upwards [(isOpen_lt continuous_const htc).mem_nhds hlt1,
      (isOpen_lt htc continuous_const).mem_nhds hlt2] with y hy1 hy2
    exact cutProfile_eq_one (by norm_num) (by norm_num) (le_of_lt hy1) (le_of_lt hy2)
  · left
    have hlt : (3 : ℝ) ^ 2 < ‖x - c‖ ^ 2 * (1 / s) ^ 2 :=
      not_le.mp fun h => absurd ((sqScaled_le_iff hs (by norm_num)).mp h) (not_le.mpr h2)
    filter_upwards [(isOpen_lt continuous_const htc).mem_nhds hlt] with y hy
    exact cutProfile_eq_zero_of_ge (by norm_num) (le_of_lt hy)

theorem radial_weight_bounds {Λ s ρ : ℝ} (hΛ : 0 < Λ) (hs : 0 < s) (hρ : 0 ≤ ρ) (x c : R3) :
    (ρ * s ≤ ‖x - c‖ → Real.exp (Λ * -(‖x - c‖ ^ 2 / s ^ 2)) ≤ Real.exp (Λ * -(ρ ^ 2))) ∧
    (‖x - c‖ ≤ ρ * s → Real.exp (Λ * -(ρ ^ 2)) ≤ Real.exp (Λ * -(‖x - c‖ ^ 2 / s ^ 2))) := by
  constructor
  · intro h
    have h1 : ρ ≤ ‖x - c‖ / s := (le_div_iff₀ hs).mpr h
    have h2 : ρ ^ 2 ≤ (‖x - c‖ / s) ^ 2 := pow_le_pow_left₀ hρ h1 2
    rw [div_pow] at h2
    have := mul_le_mul_of_nonneg_left h2 hΛ.le
    exact Real.exp_le_exp.mpr (by linarith)
  · intro h
    have h1 : ‖x - c‖ / s ≤ ρ := (div_le_iff₀ hs).mpr h
    have h2 : (‖x - c‖ / s) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [div_pow] at h2
    have := mul_le_mul_of_nonneg_left h2 hΛ.le
    exact Real.exp_le_exp.mpr (by linarith)

/-- Weight values at the inner, target and outer radii `1/4, 2, 5/2`. -/
def tbEin (Λ : ℝ) : ℝ := Real.exp (Λ * -((1 / 4 : ℝ) ^ 2))
def tbEt (Λ : ℝ) : ℝ := Real.exp (Λ * -((2 : ℝ) ^ 2))
def tbEo (Λ : ℝ) : ℝ := Real.exp (Λ * -((5 / 2 : ℝ) ^ 2))
def tbAlpha (Λ : ℝ) : ℝ := tbEt Λ - tbEo Λ
def tbBeta (Λ : ℝ) : ℝ := tbEin Λ - tbEt Λ
/-- The single three-ball exponent `alpha/(alpha+beta)`. -/
def tbGamma (Λ : ℝ) : ℝ := tbAlpha Λ / (tbAlpha Λ + tbBeta Λ)

theorem tbAlpha_pos {Λ : ℝ} (hΛ : 0 < Λ) : 0 < tbAlpha Λ := by
  unfold tbAlpha tbEt tbEo
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith))

theorem tbBeta_pos {Λ : ℝ} (hΛ : 0 < Λ) : 0 < tbBeta Λ := by
  unfold tbBeta tbEin tbEt
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith))

theorem tbGamma_pos {Λ : ℝ} (hΛ : 0 < Λ) : 0 < tbGamma Λ :=
  div_pos (tbAlpha_pos hΛ) (add_pos (tbAlpha_pos hΛ) (tbBeta_pos hΛ))

theorem tbGamma_lt_one {Λ : ℝ} (hΛ : 0 < Λ) : tbGamma Λ < 1 :=
  (div_lt_one (add_pos (tbAlpha_pos hΛ) (tbBeta_pos hΛ))).mpr (by linarith [tbBeta_pos hΛ])

theorem tbGamma_compl {Λ : ℝ} (hΛ : 0 < Λ) :
    tbBeta Λ / (tbAlpha Λ + tbBeta Λ) = 1 - tbGamma Λ := by
  unfold tbGamma
  rw [eq_sub_iff_add_eq, ← add_div, add_comm (tbBeta Λ) (tbAlpha Λ),
    div_self (add_pos (tbAlpha_pos hΛ) (tbBeta_pos hΛ)).ne']

/-- The weighted collar split for a Carleman inequality with constant one. -/
theorem carleman_collar_split {u L ψ wO : R3 → ℝ} {KB KH Ob : Set R3} {τ hB hS hO : ℝ}
    (hτ : 0 < τ)
    (hcarl : ∫ x, Real.exp (2 * τ * ψ x) * u x ^ 2 ≤ ∫ x, Real.exp (2 * τ * ψ x) * L x ^ 2)
    (hu_int : Integrable (fun x => (Real.exp (τ * ψ x) * u x) ^ 2))
    (hL_int : Integrable (fun x => L x ^ 2))
    (hKB : MeasurableSet KB) (hKH : MeasurableSet KH) (hOm : MeasurableSet Ob)
    (hLzero : ∀ x, x ∉ KB ∪ KH → L x = 0)
    (hψB : ∀ x ∈ KB, ψ x ≤ hB) (hψS : ∀ x ∈ KH, ψ x ≤ hS) (hψO : ∀ x ∈ Ob, hO ≤ ψ x)
    (huO : ∀ x ∈ Ob, u x = wO x) (hwO_int : IntegrableOn (fun x => wO x ^ 2) Ob) :
    Real.exp (2 * (τ * hO)) * ∫ x in Ob, wO x ^ 2 ≤
      Real.exp (2 * (τ * hB)) * (∫ x in KB, L x ^ 2) +
        Real.exp (2 * (τ * hS)) * ∫ x in KH, L x ^ 2 := by
  have e : ∀ x, (Real.exp (τ * ψ x) * u x) ^ 2 = Real.exp (2 * τ * ψ x) * u x ^ 2 := fun x => by
    rw [show (2 : ℝ) * τ * ψ x = ((2 : ℕ) : ℝ) * (τ * ψ x) by push_cast; ring,
      Real.exp_nat_mul, mul_pow]
  have e2 : ∀ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2 = Real.exp (2 * τ * ψ x) * L x ^ 2 :=
    fun x => by rw [mul_assoc]
  have hcarl' : τ * 0 + τ ^ 3 * (∫ x, (Real.exp (τ * ψ x) * u x) ^ 2) ≤
      τ ^ 3 * ∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2 := by
    simp only [e, e2, mul_zero, zero_add]
    exact mul_le_mul_of_nonneg_left hcarl (by positivity)
  have h := weighted_sq_split (C := τ ^ 3) (G := 0) hτ.le (by positivity) le_rfl hcarl'
    hu_int hL_int hKB hKH hOm hLzero hψB hψS hψO huO hwO_int
  exact le_of_mul_le_mul_left h (by positivity)

theorem tb_balance_step {A2 S2 D2 RI RO Kr Ein Et Eo τ : ℝ} (hS2 : 0 ≤ S2) (hD2 : 0 ≤ D2)
    (hKr : 0 ≤ Kr)
    (h : Real.exp (2 * (τ * Et)) * A2 ≤
      Real.exp (2 * (τ * Ein)) * RI + Real.exp (2 * (τ * Eo)) * RO)
    (hRI : RI ≤ Kr * S2) (hRO : RO ≤ Kr * D2) :
    Real.sqrt A2 ≤ Real.sqrt Kr * (Real.exp (-((Et - Eo) * τ)) * Real.sqrt D2 +
      Real.exp ((Ein - Et) * τ) * Real.sqrt S2) := by
  have e1 : Real.exp (2 * (τ * Ein)) =
      Real.exp (2 * (τ * Et)) * Real.exp ((Ein - Et) * τ) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Real.exp (2 * (τ * Eo)) =
      Real.exp (2 * (τ * Et)) * Real.exp (-((Et - Eo) * τ)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hE := Real.exp_pos (2 * (τ * Et))
  have ha := Real.exp_pos ((Ein - Et) * τ)
  have hb := Real.exp_pos (-((Et - Eo) * τ))
  rw [e1, e2] at h
  have h1 := mul_le_mul_of_nonneg_left hRI (le_of_lt (mul_pos hE (pow_pos ha 2)))
  have h2 := mul_le_mul_of_nonneg_left hRO (le_of_lt (mul_pos hE (pow_pos hb 2)))
  have h3 : Real.exp (2 * (τ * Et)) * A2 ≤ Real.exp (2 * (τ * Et)) *
      (Kr * (Real.exp ((Ein - Et) * τ) ^ 2 * S2 + Real.exp (-((Et - Eo) * τ)) ^ 2 * D2)) := by
    linarith
  have h4 := le_of_mul_le_mul_left h3 hE
  have hsq : Kr * (Real.exp ((Ein - Et) * τ) ^ 2 * S2 + Real.exp (-((Et - Eo) * τ)) ^ 2 * D2) ≤
      (Real.sqrt Kr * (Real.exp (-((Et - Eo) * τ)) * Real.sqrt D2 +
        Real.exp ((Ein - Et) * τ) * Real.sqrt S2)) ^ 2 := by
    have hcross : 0 ≤ 2 * Kr * (Real.exp ((Ein - Et) * τ) * Real.exp (-((Et - Eo) * τ)) *
        Real.sqrt D2 * Real.sqrt S2) := by positivity
    have hexp : (Real.sqrt Kr * (Real.exp (-((Et - Eo) * τ)) * Real.sqrt D2 +
        Real.exp ((Ein - Et) * τ) * Real.sqrt S2)) ^ 2 =
        Real.sqrt Kr ^ 2 * (Real.exp ((Ein - Et) * τ) ^ 2 * Real.sqrt S2 ^ 2 +
          Real.exp (-((Et - Eo) * τ)) ^ 2 * Real.sqrt D2 ^ 2) +
        2 * Real.sqrt Kr ^ 2 * (Real.exp ((Ein - Et) * τ) * Real.exp (-((Et - Eo) * τ)) *
          Real.sqrt D2 * Real.sqrt S2) := by ring
    rw [hexp, Real.sq_sqrt hKr, Real.sq_sqrt hS2, Real.sq_sqrt hD2]
    linarith
  calc Real.sqrt A2 ≤ Real.sqrt ((Real.sqrt Kr * (Real.exp (-((Et - Eo) * τ)) * Real.sqrt D2 +
        Real.exp ((Ein - Et) * τ) * Real.sqrt S2)) ^ 2) := Real.sqrt_le_sqrt (h4.trans hsq)
    _ = _ := Real.sqrt_sq (by positivity)

theorem tb_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (by positivity)

theorem tb_combine {T X A2 S D K γ : ℝ} (hX : 0 ≤ X) (hA2 : 0 ≤ A2) (hS : 0 ≤ S)
    (hSD : S ≤ D) (hγ : 0 < γ) (hγ1 : γ < 1) (hT : T = X + A2) (hXS : Real.sqrt X ≤ S)
    (hA : Real.sqrt A2 ≤ K * (S ^ γ * D ^ (1 - γ))) :
    Real.sqrt T ≤ (1 + K) * (S ^ γ * D ^ (1 - γ)) := by
  have hm := interpolation_weight_antitone hS hSD hγ hγ1.le
  rw [Real.rpow_one, sub_self, Real.rpow_zero, mul_one] at hm
  rw [hT]
  have := tb_sqrt_add_le hX hA2
  linarith

theorem continuous_Lop_of_contDiff (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {w : R3 → ℝ} (hw : ContDiff ℝ ∞ w) :
    Continuous (Lop a w) := by
  unfold Lop
  exact continuous_finsetSum _ fun i _ => (contDiff_pd_apply (ContDiff.sum fun k _ =>
    (ha i k).mul (contDiff_pd_apply hw))).continuous

/-- Integrated collar residual bound from a pointwise bound and a Caccioppoli bound. -/
theorem collar_residual_integral {Kc E Bk Dom : Set R3} {L q : R3 → ℝ} {M C : ℝ}
    (hKc : IsCompact Kc) (hKE : Kc ⊆ E) (hKB : Kc ⊆ Bk) (hBk : IsCompact Bk)
    (hBkDom : Bk ⊆ Dom) (hDom : IsOpen Dom) (hM : 0 ≤ M) (hLc : Continuous L)
    (hq : ContDiffOn ℝ ∞ q Dom) (hint : IntegrableOn (fun y => q y ^ 2) E)
    (hpt : ∀ y ∈ Kc, L y ^ 2 ≤ M * (q y ^ 2 + ∑ j, pd j q y ^ 2))
    (hcac : ∫ y in Bk, ∑ j, pd j q y ^ 2 ≤ C * ∫ y in E, q y ^ 2) :
    ∫ y in Kc, L y ^ 2 ≤ M * (1 + C) * ∫ y in E, q y ^ 2 := by
  have hfd := hq.continuousOn_fderiv_of_isOpen hDom (by simp)
  have hgradc : ContinuousOn (fun y => ∑ j, pd j q y ^ 2) Dom :=
    continuousOn_finset_sum _ fun j _ => (show ContinuousOn
      (fun y => fderiv ℝ q y (EuclideanSpace.single j 1)) Dom from
        hfd.clm_apply continuousOn_const).pow 2
  have I1 : IntegrableOn (fun y => L y ^ 2) Kc := (hLc.pow 2).continuousOn.integrableOn_compact hKc
  have I2 : IntegrableOn (fun y => q y ^ 2) Kc :=
    ((hq.continuousOn.mono (hKB.trans hBkDom)).pow 2).integrableOn_compact hKc
  have I3 : IntegrableOn (fun y => ∑ j, pd j q y ^ 2) Kc :=
    (hgradc.mono (hKB.trans hBkDom)).integrableOn_compact hKc
  have I4 : IntegrableOn (fun y => ∑ j, pd j q y ^ 2) Bk :=
    (hgradc.mono hBkDom).integrableOn_compact hBk
  have h1 : ∫ y in Kc, L y ^ 2 ≤ ∫ y in Kc, M * (q y ^ 2 + ∑ j, pd j q y ^ 2) :=
    setIntegral_mono_on I1 ((I2.add I3).const_mul M) hKc.measurableSet hpt
  rw [integral_const_mul, integral_add I2 I3] at h1
  have h2 : ∫ y in Kc, q y ^ 2 ≤ ∫ y in E, q y ^ 2 :=
    setIntegral_mono_set hint
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _) hKE.eventuallyLE
  have h3 : ∫ y in Kc, ∑ j, pd j q y ^ 2 ≤ ∫ y in Bk, ∑ j, pd j q y ^ 2 :=
    setIntegral_mono_set I4
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ ∑ j, pd j q x ^ 2 from
        Finset.sum_nonneg fun j _ => sq_nonneg _) hKB.eventuallyLE
  calc ∫ y in Kc, L y ^ 2 ≤ M * ((∫ y in Kc, q y ^ 2) + ∫ y in Kc, ∑ j, pd j q y ^ 2) := h1
    _ ≤ M * ((∫ y in E, q y ^ 2) + C * ∫ y in E, q y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 (h3.trans hcac)) hM
    _ = M * (1 + C) * ∫ y in E, q y ^ 2 := by ring

/-- V4 (one instance): the three-ball inequality from the Carleman estimate on the fixed
annulus and the two collar residual bounds; all constants are given before `q`. -/
theorem three_ball_instance (g : MatrixField) (hg : IsAdmissibleMetric g) {lam s Λ τ0 Kr : ℝ}
    {c : R3} (hs : 0 < s) (hΛ : 0 < Λ) (hKr : 0 ≤ Kr) {q : R3 → ℝ}
    (hq : ContDiffOn ℝ ∞ q (ball c (4 * s)))
    (hL : ∀ y ∈ ball c (4 * s), Lop (radialCoeff g (lam, c, 1 / s)) q y = 0)
    (hint : IntegrableOn (fun y => q y ^ 2) (ball c (4 * s)))
    (HC : ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ closedAnnulus c (1 / 4 * s) (3 * s) →
      (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) * w y ^ 2) ≤
        ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          Lop (radialCoeff g (lam, c, 1 / s)) w y ^ 2)
    (hRI : ∫ y in closedAnnulus c (1 / 4 * s) (1 / 2 * s),
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 ≤
      Kr * ∫ y in ball c s, q y ^ 2)
    (hRO : ∫ y in closedAnnulus c (5 / 2 * s) (3 * s),
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 ≤
      Kr * ∫ y in ball c (4 * s), q y ^ 2) :
    Real.sqrt (∫ y in ball c (2 * s), q y ^ 2) ≤
      (1 + (2 * Real.sqrt Kr + Real.exp (tbAlpha Λ * max τ0 1))) *
        (Real.sqrt (∫ y in ball c s, q y ^ 2) ^ tbGamma Λ *
          Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) ^ (1 - tbGamma Λ)) := by
  have hchi := contDiff_threeBallCut c s
  have hts := tsupport_threeBallCut c hs
  have hts4 : tsupport (threeBallCut c s) ⊆ ball c (4 * s) :=
    hts.trans (closedAnnulus_subset_ball (by linarith))
  have hw : ContDiff ℝ ∞ (fun z => threeBallCut c s z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball hchi hts4 hq
  have hwts : tsupport (fun z => threeBallCut c s z * q z) ⊆
      closedAnnulus c (1 / 4 * s) (3 * s) := tsupport_mul_subset_left.trans hts
  have hLzero : ∀ x, x ∉ closedAnnulus c (1 / 4 * s) (1 / 2 * s) ∪
      closedAnnulus c (5 / 2 * s) (3 * s) →
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x = 0 :=
    Lop_cutoff_mul_eq_zero _ hts4 hL (threeBallCut_dich c hs)
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, c, 1 / s))
    (radialCoeff_contDiff g hg _) hw
  have hψc : Continuous (fun y : R3 => Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) := by fun_prop
  have hKin := isCompact_closedAnnulus c (1 / 4 * s) (1 / 2 * s)
  have hKout := isCompact_closedAnnulus c (5 / 2 * s) (3 * s)
  have hL_int : Integrable (fun x =>
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hKin.union hKout)
      (fun x hx => by
        rw [Pi.pow_apply, hLzero x hx]
        norm_num))
  have hu_int : ∀ τ : ℝ, Integrable (fun x =>
      (Real.exp (τ * Real.exp (Λ * -(‖x - c‖ ^ 2 / s ^ 2))) * (threeBallCut c s x * q x)) ^ 2) :=
    fun τ => (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul hw.continuous).pow
      2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedAnnulus c (1 / 4 * s) (3 * s)) (fun x hx => by
        have h0 : threeBallCut c s x = 0 := by
          by_contra h
          exact hx (hts (subset_tsupport _ h))
        simp [h0]))
  have hOb4 : ball c (2 * s) \ ball c (1 / 2 * s) ⊆ ball c (4 * s) :=
    diff_subset.trans (ball_subset_ball (by linarith))
  have hstep : ∀ τ : ℝ, max τ0 1 ≤ τ →
      Real.sqrt (∫ y in ball c (2 * s) \ ball c (1 / 2 * s), q y ^ 2) ≤
        Real.sqrt Kr * (Real.exp (-(tbAlpha Λ * τ)) *
          Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) +
          Real.exp (tbBeta Λ * τ) * Real.sqrt (∫ y in ball c s, q y ^ 2)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hτ
    have hcarl := HC τ ((le_max_left _ _).trans hτ) _ hw hwts
    have hsplit := carleman_collar_split (τ := τ) (u := fun z => threeBallCut c s z * q z)
      (L := Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z))
      (ψ := fun y => Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) (wO := q)
      (KB := closedAnnulus c (1 / 4 * s) (1 / 2 * s)) (KH := closedAnnulus c (5 / 2 * s) (3 * s))
      (Ob := ball c (2 * s) \ ball c (1 / 2 * s)) (hB := tbEin Λ) (hS := tbEo Λ) (hO := tbEt Λ)
      (by linarith) hcarl (hu_int τ) hL_int hKin.isClosed.measurableSet
      hKout.isClosed.measurableSet (measurableSet_ball.diff measurableSet_ball) hLzero
      (fun x hx => (radial_weight_bounds hΛ hs (by norm_num : (0 : ℝ) ≤ 1 / 4) x c).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hs (by norm_num : (0 : ℝ) ≤ 5 / 2) x c).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hs (by norm_num : (0 : ℝ) ≤ 2) x c).2
        (le_of_lt (mem_ball_iff_norm.mp hx.1)))
      (fun x hx => by
        have h1 : 1 / 2 * s ≤ ‖x - c‖ :=
          not_lt.mp fun h => hx.2 (mem_ball_iff_norm.mpr h)
        have h2 : ‖x - c‖ ≤ 5 / 2 * s := by
          have := mem_ball_iff_norm.mp hx.1
          linarith
        beta_reduce
        rw [threeBallCut_eq_one c hs h1 h2, one_mul])
      (hint.mono_set hOb4)
    exact tb_balance_step (integral_nonneg fun x => sq_nonneg (q x))
      (integral_nonneg fun x => sq_nonneg (q x)) hKr hsplit hRI hRO
  have hS4 : ball c s ⊆ ball c (4 * s) := ball_subset_ball (by linarith)
  have hsub : ball c (1 / 2 * s) ⊆ ball c (2 * s) := ball_subset_ball (by linarith)
  have hAD : Real.sqrt (∫ y in ball c (2 * s) \ ball c (1 / 2 * s), q y ^ 2) ≤
      Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set hint
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _) hOb4.eventuallyLE)
  have hSD : Real.sqrt (∫ y in ball c s, q y ^ 2) ≤ Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set hint
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _) hS4.eventuallyLE)
  have hXS : Real.sqrt (∫ y in ball c (1 / 2 * s), q y ^ 2) ≤
      Real.sqrt (∫ y in ball c s, q y ^ 2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set (hint.mono_set hS4)
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (ball_subset_ball (by linarith)).eventuallyLE)
  have hT : ∫ y in ball c (2 * s), q y ^ 2 = (∫ y in ball c (1 / 2 * s), q y ^ 2) +
      ∫ y in ball c (2 * s) \ ball c (1 / 2 * s), q y ^ 2 := by
    conv_lhs => rw [← Set.union_diff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right (measurableSet_ball.diff measurableSet_ball)
      (hint.mono_set (hsub.trans (ball_subset_ball (by linarith)))) (hint.mono_set hOb4)
  have hbal := exp_balance (tbAlpha_pos hΛ) (tbBeta_pos hΛ) (Real.sqrt_nonneg Kr)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hAD hstep
  rw [tbGamma_compl hΛ] at hbal
  exact tb_combine (integral_nonneg fun x => sq_nonneg (q x))
    (integral_nonneg fun x => sq_nonneg (q x)) (Real.sqrt_nonneg _) hSD (tbGamma_pos hΛ)
    (tbGamma_lt_one hΛ) hT hXS hbal

/-- V4: the UNIFORM three-ball inequality for the actual dilated coefficient
`principalCoefficient g (lam • y)`. ONE `K > 0` and ONE exponent `γ ∈ (0,1)` are chosen BEFORE
`lam ∈ [0, lam1]`, the center `‖c‖ ≤ B`, the scale `s ∈ [s0, s1]` and the local solution `q`
(smooth and harmonic only on `ball c (4s)`, square integrable there). The integrals are the
restricted-volume L² integrals. -/
theorem uniform_three_ball (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ γ < 1 ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B →
      ∀ s ∈ Icc s0 s1, ∀ q : R3 → ℝ, ContDiffOn ℝ ∞ q (ball c (4 * s)) →
      (∀ y ∈ ball c (4 * s),
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0) →
      IntegrableOn (fun y => q y ^ 2) (ball c (4 * s)) →
      Real.sqrt (∫ y in ball c (2 * s), q y ^ 2) ≤
        K * (Real.sqrt (∫ y in ball c s, q y ^ 2) ^ γ *
          Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) ^ (1 - γ)) := by
  obtain ⟨Λ, τ0, hΛ, HC⟩ := uniform_radial_carleman g hg lam1 B s0 s1 (1 / 4) 3 hs0 hss
    (by norm_num)
  obtain ⟨Mi, hMi, HMi⟩ := uniform_cutoff_residual_pointwise g hg lam1 B s0 s1 (1 / 4) (1 / 2)
    hs0 hss (contDiff_cutProfile (1 / 4) (1 / 2) (5 / 2) 3)
  obtain ⟨Mo, hMo, HMo⟩ := uniform_cutoff_residual_pointwise g hg lam1 B s0 s1 (5 / 2) 3
    hs0 hss (contDiff_cutProfile (1 / 4) (1 / 2) (5 / 2) 3)
  obtain ⟨Ci, hCi, HCi⟩ := uniform_caccioppoli g hg lam1 B s0 s1 (1 / 2) (3 / 4) 1 hs0 hss
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Co, hCo, HCo⟩ := uniform_caccioppoli g hg lam1 B s0 s1 3 (7 / 2) 4 hs0 hss
    (by norm_num) (by norm_num) (by norm_num)
  have hKr : 0 ≤ Mi * (1 + Ci) + Mo * (1 + Co) := by positivity
  refine ⟨1 + (2 * Real.sqrt (Mi * (1 + Ci) + Mo * (1 + Co)) + Real.exp (tbAlpha Λ * max τ0 1)),
    tbGamma Λ, by positivity, tbGamma_pos hΛ, tbGamma_lt_one hΛ, ?_⟩
  intro lam hlam c hc s hs q hq hL hint
  have hs' : 0 < s := hs0.trans_le hs.1
  have hw : ContDiff ℝ ∞ (fun z => threeBallCut c s z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball (contDiff_threeBallCut c s)
      ((tsupport_threeBallCut c hs').trans (closedAnnulus_subset_ball (by linarith))) hq
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, c, 1 / s))
    (radialCoeff_contDiff g hg _) hw
  have hKin4 : closedAnnulus c (1 / 4 * s) (1 / 2 * s) ⊆ ball c (4 * s) :=
    closedAnnulus_subset_ball (by linarith)
  have hKout4 : closedAnnulus c (5 / 2 * s) (3 * s) ⊆ ball c (4 * s) :=
    closedAnnulus_subset_ball (by linarith)
  have hcI := HCi lam hlam c hc s hs q (hq.mono (ball_subset_ball (by linarith)))
    (fun y hy => hL y (ball_subset_ball (by linarith) hy))
    (hint.mono_set (ball_subset_ball (by linarith)))
  rw [one_mul] at hcI
  have hcO := HCo lam hlam c hc s hs q hq hL hint
  have hRI0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / s))
      (fun z => threeBallCut c s z * q z)) (Dom := ball c (4 * s))
    (isCompact_closedAnnulus c (1 / 4 * s) (1 / 2 * s))
    (closedAnnulus_subset_ball (by linarith)) (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c (1 / 2 * s)) (closedBall_subset_ball (by linarith)) isOpen_ball
    hMi hLc hq (hint.mono_set (ball_subset_ball (by linarith)))
    (fun y hy => HMi lam hlam c hc s hs y hy.1 hy.2 (ball c (4 * s)) isOpen_ball q hq
      (hKin4 hy) (hL y (hKin4 hy))) hcI
  have hRO0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / s))
      (fun z => threeBallCut c s z * q z)) (Dom := ball c (4 * s))
    (isCompact_closedAnnulus c (5 / 2 * s) (3 * s)) hKout4
    (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c (3 * s)) (closedBall_subset_ball (by linarith)) isOpen_ball
    hMo hLc hq hint
    (fun y hy => HMo lam hlam c hc s hs y hy.1 hy.2 (ball c (4 * s)) isOpen_ball q hq
      (hKout4 hy) (hL y (hKout4 hy))) hcO
  have hS0 : 0 ≤ ∫ y in ball c s, q y ^ 2 := integral_nonneg fun x => sq_nonneg (q x)
  have hD0 : 0 ≤ ∫ y in ball c (4 * s), q y ^ 2 := integral_nonneg fun x => sq_nonneg (q x)
  have hi : 0 ≤ Mi * (1 + Ci) := by positivity
  have ho : 0 ≤ Mo * (1 + Co) := by positivity
  exact three_ball_instance g hg hs' hΛ hKr hq hL hint
    (fun τ hτ w hw' hsupp => HC lam hlam c hc s hs τ hτ w hw' hsupp)
    (hRI0.trans (mul_le_mul_of_nonneg_right (by linarith) hS0))
    (hRO0.trans (mul_le_mul_of_nonneg_right (by linarith) hD0))

section NativeThreeBall
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume

/-- V4 (native form on the actual `Lp` carriers): the literal operator
`coordinateFluxDivergence ∘ metricDivergenceFlux (g(lam ·))` and the restricted-volume `Lp`
norms; ONE `K` and ONE `γ ∈ (0,1)` before `lam, c, s` and the solution. -/
theorem uniform_three_ball_native_lp (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ γ < 1 ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B →
      ∀ s ∈ Icc s0 s1,
      ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (ball c (4 * s)))) (q : R3 → ℝ),
      q =ᵐ[(volume : Measure R3).restrict (ball c (4 * s))] (u : R3 → ℝ) →
      ContDiffOn ℝ ∞ q (ball c (4 * s)) →
      (∀ y ∈ ball c (4 * s),
        coordinateFluxDivergence (metricDivergenceFlux (fun x => g (lam • x)) q) y = 0) →
      ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (ball c (2 * s))))
        (uS : Lp ℝ 2 ((volume : Measure R3).restrict (ball c s))),
      q =ᵐ[(volume : Measure R3).restrict (ball c (2 * s))] (uO : R3 → ℝ) →
      q =ᵐ[(volume : Measure R3).restrict (ball c s)] (uS : R3 → ℝ) →
      ‖uO‖ ≤ K * (‖uS‖ ^ γ * ‖u‖ ^ (1 - γ)) := by
  obtain ⟨K, γ, hK, hγ, hγ1, H⟩ := uniform_three_ball g hg lam1 B s0 s1 hs0 hss
  refine ⟨K, γ, hK, hγ, hγ1, fun lam hlam c hc s hs u q hq hqs hpde uO uS hqO hqS => ?_⟩
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hL : ∀ y ∈ ball c (4 * s),
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0 := by
    intro y hy
    have h := hpde y hy
    rw [coordinateFluxDivergence_eq_divCoeffGrad] at h
    exact h
  have hI := H lam hlam c hc s hs q hqs hL hmem.integrable_sq
  rw [hnO, hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hI
  exact hI

end NativeThreeBall

/-- Step-5 chain constant: explicit, a function of `K, γ` and the step count only. -/
def chainConst (K γ : ℝ) : ℕ → ℝ
  | 0 => K
  | n + 1 => K * chainConst K γ n ^ γ

theorem chainConst_nonneg {K γ : ℝ} (hK : 0 ≤ K) : ∀ n, 0 ≤ chainConst K γ n
  | 0 => hK
  | n + 1 => mul_nonneg hK (Real.rpow_nonneg (chainConst_nonneg hK n) _)

/-- Step-5 chain composition: one-step interpolations `X (i+1) ≤ K X_i^γ D^(1-γ)` with the
SAME `K, γ` and full norm `D` compose along a finite chain with exponent `γ^(n+1)` and the
explicit constant `chainConst K γ n` (checked interpolation_compose; zero data included). -/
theorem chain_interpolation {X : ℕ → ℝ} {D K γ : ℝ} (hX : ∀ i, 0 ≤ X i) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hstep : ∀ i, X (i + 1) ≤ K * (X i ^ γ * D ^ (1 - γ))) :
    ∀ n : ℕ, X (n + 1) ≤ chainConst K γ n * (X 0 ^ (γ ^ (n + 1)) * D ^ (1 - γ ^ (n + 1))) := by
  intro n
  induction n with
  | zero => simpa [chainConst] using hstep 0
  | succ n ih =>
    have ha0 : 0 < γ ^ (n + 1) := pow_pos hγ _
    have ha1 : γ ^ (n + 1) < 1 := pow_lt_one₀ hγ.le hγ1 (Nat.succ_ne_zero n)
    have h := interpolation_compose (hX 0) hD (hX (n + 1)) (chainConst_nonneg hK n) hK ha0 ha1
      hγ hγ1 hD le_rfl ih (hstep (n + 1))
    rw [pow_succ γ (n + 1)]
    exact h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v050: uniform second interpolation on the literal annulus (W1-W4 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

/-- W: the literal second-domain annulus `D2 = (s/2, 2s)` about `p`. -/
def annD (p : R3) (s : ℝ) : Set R3 := {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s}

/-- W: the literal observation ball `S2 = ball(p - s e₂, s/8)`. -/
def annS (p : R3) (s : ℝ) : Set R3 :=
  ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8)

/-- W: the open unit annulus `(5/8, 11/8)` carrying the unit chain centers. -/
def annA : Set R3 := {b : R3 | 5/8 < ‖b-0‖ ∧ ‖b-0‖ < 11/8}

/-- W: the compact unit target `[3/4, 5/4]`. -/
def annKu : Set R3 := {b : R3 | 3/4 ≤ ‖b-0‖ ∧ ‖b-0‖ ≤ 5/4}

/-- W: the actual class of local solutions of the dilated operator on the literal annulus. -/
def AnnClass (g : MatrixField) (lam : ℝ) (p : R3) (s : ℝ) (q : R3 → ℝ) : Prop :=
  ContDiffOn ℝ ∞ q (annD p s) ∧
    (∀ y ∈ annD p s,
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0) ∧
    IntegrableOn (fun y => q y ^ 2) (annD p s)

theorem sqrt_setIntegral_sq_mono {q : R3 → ℝ} {E F : Set R3}
    (hF : IntegrableOn (fun y => q y ^ 2) F) (hEF : E ⊆ F) :
    Real.sqrt (∫ y in E, q y ^ 2) ≤ Real.sqrt (∫ y in F, q y ^ 2) :=
  Real.sqrt_le_sqrt (setIntegral_mono_set hF
    (Filter.Eventually.of_forall (fun y => sq_nonneg (q y))) (Filter.Eventually.of_forall hEF))

/-- W1(a): the whole three-ball `4`-ball of a transported unit center lies in `D2`. -/
theorem annA_ball_subset (p : R3) {s : ℝ} (hs : 0 < s) {b : R3} (hb : b ∈ annA) :
    ball (p + s • b) (4 * (s/40)) ⊆ annD p s := by
  intro y hy
  have hyc : ‖y - (p + s • b)‖ < 4 * (s/40) := by rw [← dist_eq_norm]; exact mem_ball.mp hy
  obtain ⟨hb1, hb2⟩ := hb
  rw [sub_zero] at hb1 hb2
  have hsb : ‖s • b‖ = s * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have h1 : ‖y - p‖ ≤ ‖y - (p + s • b)‖ + ‖s • b‖ := by
    have he : y - p = (y - (p + s • b)) + s • b := by abel
    rw [he]; exact norm_add_le _ _
  have h2 : ‖s • b‖ ≤ ‖y - p‖ + ‖y - (p + s • b)‖ := by
    have he : (y - p) - (y - (p + s • b)) = s • b := by abel
    have h := norm_sub_le (y - p) (y - (p + s • b))
    rw [he] at h
    exact h
  rw [hsb] at h1 h2
  have h3 : s * (5/8) < s * ‖b‖ := mul_lt_mul_of_pos_left hb1 hs
  have h4 : s * ‖b‖ < s * (11/8) := mul_lt_mul_of_pos_left hb2 hs
  show s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s
  constructor <;> linarith

/-- W1(b): a unit step of length `≤ 1/40` keeps the next small ball inside the doubled ball. -/
theorem annA_step_subset (p : R3) {s : ℝ} (hs : 0 < s) {b b' : R3} (hbb : dist b' b ≤ 1/40) :
    ball (p + s • b') (s/40) ⊆ ball (p + s • b) (2 * (s/40)) := by
  apply ball_subset_ball'
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hs]
  have h := mul_le_mul_of_nonneg_left hbb hs.le
  linarith

/-- W1(c): transported centers stay in one bounded set. -/
theorem annA_center_norm {p b : R3} {B s s1 : ℝ} (hp : ‖p‖ ≤ B) (hs : 0 < s) (hs1 : s ≤ s1)
    (hb : ‖b‖ < 11/8) : ‖p + s • b‖ ≤ B + 11/8 * s1 := by
  have h1 := norm_add_le p (s • b)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at h1
  have h2 : s * ‖b‖ ≤ s1 * (11/8) := mul_le_mul hs1 hb.le (norm_nonneg _) (by linarith)
  linarith

/-- W1(d): the base unit center `-e₂` lies in the unit annulus. -/
theorem annA_base_mem : -EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈ annA := by
  have h : ‖-EuclideanSpace.single (2 : Fin 3) (1 : ℝ) - 0‖ = 1 := by
    rw [sub_zero, norm_neg, EuclideanSpace.norm_single, norm_one]
  show 5/8 < ‖-EuclideanSpace.single (2 : Fin 3) (1 : ℝ) - 0‖ ∧
    ‖-EuclideanSpace.single (2 : Fin 3) (1 : ℝ) - 0‖ < 11/8
  rw [h]
  norm_num

/-- W1(d): the transported base ball lies in the literal observation ball `S2`. -/
theorem annA_base_ball (p : R3) {s : ℝ} (hs : 0 < s) :
    ball (p + s • -EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/40) ⊆ annS p s := by
  have he : p + s • -EuclideanSpace.single (2 : Fin 3) (1 : ℝ) =
      p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    rw [smul_neg, ← sub_eq_add_neg]
  rw [he]
  unfold annS
  exact ball_subset_ball (by linarith)

theorem annS_subset_annD (p : R3) {s : ℝ} (hs : 0 < s) : annS p s ⊆ annD p s :=
  ball_subset_closedBall.trans (native_closed_observation_subset_annulus p s hs)

/-- W2: a unit center is uniformly good when ONE constant and ONE exponent, chosen before
`lam ∈ [0,lam1]`, `‖p‖ ≤ B`, `s ∈ [s0,s1]` and the solution, bound its transported small ball. -/
def AnnGood (g : MatrixField) (lam1 B s0 s1 : ℝ) (b : R3) : Prop :=
  ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ a < 1 ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3, ‖p‖ ≤ B →
    ∀ s ∈ Icc s0 s1, ∀ q : R3 → ℝ, AnnClass g lam p s q →
      Real.sqrt (∫ y in ball (p + s • b) (s/40), q y ^ 2) ≤
        C * (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ a *
          Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - a))

/-- W2(i): the base unit center is uniformly good with `C = 1`, `a = 1/2`. -/
theorem annGood_base (g : MatrixField) (lam1 B s0 s1 : ℝ) (hs0 : 0 < s0) :
    AnnGood g lam1 B s0 s1 (-EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
  refine ⟨1, 1/2, one_pos, by norm_num, by norm_num, ?_⟩
  intro lam _ p _ s hs q hq
  have hspos : 0 < s := hs0.trans_le hs.1
  obtain ⟨-, -, hint⟩ := hq
  have hSD := sqrt_setIntegral_sq_mono hint (annS_subset_annD p hspos)
  have hY := sqrt_setIntegral_sq_mono (hint.mono_set (annS_subset_annD p hspos))
    (annA_base_ball p hspos)
  have hw := interpolation_weight_antitone (Real.sqrt_nonneg _) hSD
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  rw [Real.rpow_one, sub_self, Real.rpow_zero, mul_one] at hw
  rw [one_mul]
  exact hY.trans hw

/-- W2(ii): one uniform three-ball step (scale `s/40`) along a unit step of length `≤ 1/40`. -/
theorem annGood_step (g : MatrixField) (hg : IsAdmissibleMetric g) {lam1 B s0 s1 : ℝ}
    (hs0 : 0 < s0) (hss : s0 ≤ s1) {b b' : R3} (hb : b ∈ annA) (hbb : dist b' b ≤ 1/40)
    (hG : AnnGood g lam1 B s0 s1 b) : AnnGood g lam1 B s0 s1 b' := by
  obtain ⟨K, γ, hK, hγ, hγ1, H⟩ := uniform_three_ball g hg lam1 (B + 11/8 * s1) (s0/40)
    (s1/40) (by positivity) (by linarith)
  obtain ⟨C, a, hC, ha, ha1, HG⟩ := hG
  refine ⟨K * C ^ γ, a * γ, by positivity, mul_pos ha hγ, by nlinarith, ?_⟩
  intro lam hlam p hp s hs q hq
  have hspos : 0 < s := hs0.trans_le hs.1
  have hT0 := HG lam hlam p hp s hs q hq
  obtain ⟨hqs, hL, hint⟩ := hq
  have hb2 : ‖b‖ < 11/8 := by
    obtain ⟨-, h⟩ := hb
    rw [sub_zero] at h
    exact h
  have h4 := annA_ball_subset p hspos hb
  have hc := annA_center_norm hp hspos hs.2 hb2
  have hr : s/40 ∈ Icc (s0/40) (s1/40) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hT := H lam hlam (p + s • b) hc (s/40) hr q (hqs.mono h4) (fun y hy => hL y (h4 hy))
    (hint.mono_set h4)
  have h2 : ball (p + s • b) (2 * (s/40)) ⊆ annD p s :=
    (ball_subset_ball (by linarith)).trans h4
  have hO := sqrt_setIntegral_sq_mono (hint.mono_set h2) (annA_step_subset p hspos hbb)
  have hDl := sqrt_setIntegral_sq_mono hint h4
  exact interpolation_compose (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hC.le hK.le ha ha1 hγ hγ1 (Real.sqrt_nonneg _) hDl hT0 (hO.trans hT)

theorem isOpen_annA : IsOpen annA := isOpen_native_annulus 0 (5/8) (11/8)

theorem isPreconnected_annA : IsPreconnected annA :=
  (isConnected_native_annulus 0 (5/8) (11/8) (by norm_num) (by norm_num)).isPreconnected

/-- W2(iii): finite `1/40`-chains reach every unit center (relatively clopen reachability on
the connected open unit annulus); constants are recorded uniformly by `AnnGood`. -/
theorem annA_subset_good (g : MatrixField) (hg : IsAdmissibleMetric g) (lam1 B s0 s1 : ℝ)
    (hs0 : 0 < s0) (hss : s0 ≤ s1) : ∀ b ∈ annA, AnnGood g lam1 B s0 s1 b := by
  have hu : IsOpen {b : R3 | b ∈ annA ∧ AnnGood g lam1 B s0 s1 b} := by
    rw [Metric.isOpen_iff]
    rintro b ⟨hbA, hbG⟩
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp isOpen_annA b hbA
    refine ⟨min ε (1/40), lt_min hε (by norm_num), fun b' hb' => ?_⟩
    have hd : dist b' b < min ε (1/40) := mem_ball.mp hb'
    have hb'A : b' ∈ annA := hεA (mem_ball.mpr (hd.trans_le (min_le_left _ _)))
    exact ⟨hb'A, annGood_step g hg hs0 hss hbA (hd.le.trans (min_le_right _ _)) hbG⟩
  have hv : IsOpen {b : R3 | b ∈ annA ∧ ¬ AnnGood g lam1 B s0 s1 b} := by
    rw [Metric.isOpen_iff]
    rintro b ⟨hbA, hbG⟩
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp isOpen_annA b hbA
    refine ⟨min ε (1/40), lt_min hε (by norm_num), fun b' hb' => ?_⟩
    have hd : dist b' b < min ε (1/40) := mem_ball.mp hb'
    have hb'A : b' ∈ annA := hεA (mem_ball.mpr (hd.trans_le (min_le_left _ _)))
    refine ⟨hb'A, fun hG' => hbG ?_⟩
    rw [dist_comm] at hd
    exact annGood_step g hg hs0 hss hb'A (hd.le.trans (min_le_right _ _)) hG'
  have huv : Disjoint {b : R3 | b ∈ annA ∧ AnnGood g lam1 B s0 s1 b}
      {b : R3 | b ∈ annA ∧ ¬ AnnGood g lam1 B s0 s1 b} :=
    Set.disjoint_left.mpr fun b hbu hbv => hbv.2 hbu.2
  have hcov : annA ⊆ {b : R3 | b ∈ annA ∧ AnnGood g lam1 B s0 s1 b} ∪
      {b : R3 | b ∈ annA ∧ ¬ AnnGood g lam1 B s0 s1 b} := by
    intro b hb
    by_cases h : AnnGood g lam1 B s0 s1 b
    · exact Or.inl ⟨hb, h⟩
    · exact Or.inr ⟨hb, h⟩
  have hne : (annA ∩ {b : R3 | b ∈ annA ∧ AnnGood g lam1 B s0 s1 b}).Nonempty :=
    ⟨_, annA_base_mem, annA_base_mem, annGood_base g lam1 B s0 s1 hs0⟩
  intro b hb
  exact (isPreconnected_annA.subset_left_of_subset_union hu hv huv hcov hne hb).2

/-- W3: the UNIFORM integral interpolation on the literal annulus target
`K2 = [3s/4, 5s/4]`: ONE `C > 0` and ONE `a ∈ (0,1)` before `lam, p, s` and the solution. -/
theorem uniform_annulus_interpolation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B s0 s1 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ a < 1 ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3, ‖p‖ ≤ B →
      ∀ s ∈ Icc s0 s1, ∀ q : R3 → ℝ, AnnClass g lam p s q →
        Real.sqrt (∫ y in {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4}, q y ^ 2) ≤
          C * (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ a *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - a)) := by
  classical
  have hKu : IsCompact annKu := isCompact_native_closed_annulus 0 (3/4) (5/4)
  have hKuA : ∀ b ∈ annKu, b ∈ annA := by
    intro b hb
    obtain ⟨h1, h2⟩ := hb
    exact ⟨by linarith, by linarith⟩
  obtain ⟨t, ht⟩ := hKu.elim_finite_subcover (fun b : annKu => ball (b : R3) (1/40))
    (fun _ => isOpen_ball) (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (by norm_num)⟩)
  have hgood : ∀ b : annKu, AnnGood g lam1 B s0 s1 (b : R3) :=
    fun b => annA_subset_good g hg lam1 B s0 s1 hs0 hss b (hKuA b b.2)
  unfold AnnGood at hgood
  choose C a hC ha ha1 HG using hgood
  let A : Finset ℝ := insert (1/2) (t.image a)
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  have hamem : A.min' hAne ∈ A := Finset.min'_mem A hAne
  have hA : ∀ x ∈ A, 0 < x ∧ x < 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨ha i, ha1 i⟩
  have hale : ∀ i ∈ t, A.min' hAne ≤ a i := fun i hi =>
    Finset.min'_le A _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hi))
  have hsum : 0 ≤ ∑ i ∈ t, (C i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨Real.sqrt (∑ i ∈ t, (C i) ^ 2) + 1, A.min' hAne, by positivity,
    (hA _ hamem).1, (hA _ hamem).2, ?_⟩
  intro lam hlam p hp s hsI q hq
  have hspos : 0 < s := hs0.trans_le hsI.1
  have hint : IntegrableOn (fun y => q y ^ 2) (annD p s) := by
    obtain ⟨-, -, h⟩ := hq
    exact h
  have hSD := sqrt_setIntegral_sq_mono hint (annS_subset_annD p hspos)
  have hcover : {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} ⊆
      ⋃ i ∈ t, ball (p + s • (i : R3)) (s/40) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    set b : R3 := s⁻¹ • (y - p) with hb
    have hyb : y = p + s • b := by
      rw [hb, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
      abel
    have hnb : ‖b‖ = ‖y - p‖ / s := by
      rw [hb, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hspos, inv_mul_eq_div]
    have hbK : b ∈ annKu := by
      show 3/4 ≤ ‖b - 0‖ ∧ ‖b - 0‖ ≤ 5/4
      rw [sub_zero, hnb, le_div_iff₀ hspos, div_le_iff₀ hspos]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.mp (ht hbK)
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    have hdist : dist y (p + s • (i : R3)) = s * dist b (i : R3) := by
      calc dist y (p + s • (i : R3)) = dist (p + s • b) (p + s • (i : R3)) := by rw [← hyb]
        _ = s * dist b (i : R3) := by
          rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hspos]
    rw [mem_ball, hdist]
    have hbi' : dist b (i : R3) < 1/40 := mem_ball.mp hbi
    have h := mul_lt_mul_of_pos_left hbi' hspos
    linarith
  have hsq := finite_cover_interpolation_sq t (fun i => ball (p + s • (i : R3)) (s/40))
    {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} (annD p s)
    (isCompact_native_closed_annulus p (3*s/4) (5*s/4)).isClosed.measurableSet
    (fun i _ => measurableSet_ball)
    (fun i _ => (ball_subset_ball (by linarith)).trans (annA_ball_subset p hspos (hKuA i i.2)))
    hcover q hint (Real.sqrt (∫ y in annS p s, q y ^ 2)) (Real.sqrt (∫ y in annD p s, q y ^ 2))
    (A.min' hAne) C a (Real.sqrt_nonneg _) hSD (hA _ hamem).1
    (fun i _ => (hC i).le) hale (fun i _ => by
      have hI : 0 ≤ ∫ y in ball (p + s • (i : R3)) (s/40), q y ^ 2 :=
        integral_nonneg (fun y => sq_nonneg (q y))
      rw [← Real.sq_sqrt hI]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (HG i lam hlam p hp s hsI q hq) 2)
  have hw : 0 ≤ Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
      Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne) :=
    mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  calc Real.sqrt (∫ y in {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4}, q y ^ 2)
      ≤ Real.sqrt ((∑ i ∈ t, (C i) ^ 2) *
          (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i ∈ t, (C i) ^ 2) *
          (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne)) := by
        rw [Real.sqrt_mul hsum, Real.sqrt_sq hw]
    _ ≤ (Real.sqrt (∑ i ∈ t, (C i) ^ 2) + 1) *
          (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne)) :=
        mul_le_mul_of_nonneg_right (by linarith) hw

section NativeUniformSecond
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

/-- W4: the UNIFORM exact second-coefficient interpolation on Root's literal annulus
`D2=(s/2,2s)`, `O2=(4s/5,6s/5)`, `S2=ball(p-s e₂,s/8)` for ORIGINAL `S.g2`: ONE `K2i > 0` and
ONE `γ2 ∈ (0,1)` are chosen BEFORE `lam ∈ [0,lam1]`, `‖p‖ ≤ B` and `s ∈ [s0,s1]`. The literal
PDE and the `Lp` normalization are those of `SecondCoefficientInterpolationOn`. -/
theorem uniform_secondCoefficientInterpolation_annulus (S : KnownSideSourceData)
    (lam1 B s0 s1 : ℝ) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ K2i γ2 : ℝ, 0 < K2i ∧ 0 < γ2 ∧ γ2 < 1 ∧ ∀ L : ℝ, ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3,
      ‖p‖ ≤ B → ∀ s ∈ Icc s0 s1,
      SecondCoefficientInterpolationOn S L lam {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s}
        {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
        (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8)) K2i γ2 := by
  obtain ⟨C, a, hC, ha, ha1, H⟩ :=
    uniform_annulus_interpolation S.g2 S.g2_admissible lam1 B s0 s1 hs0 hss
  refine ⟨C, a, hC, ha, ha1, ?_⟩
  intro L lam hlam p hp s hs b hb hpde bD bO bS hbD hbO hbS M μ hμ hM hSM hDM
  have hspos : 0 < s := hs0.trans_le hs.1
  have hint : IntegrableOn (fun y => b y ^ 2) (annD p s) :=
    (integral_sq_representative_eq_norm_sq bD b hbD).1.integrable_sq
  have hcls : AnnClass S.g2 lam p s b :=
    ⟨hb, fun x hx => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2
      S.g1_admissible S.g2_admissible L lam b x).mp (hpde x hx), hint⟩
  have hmain := H lam hlam p hp s hs b hcls
  obtain ⟨-, -, -, -, -, hOK, hKD, -⟩ := native_annulus_target_geometry p s hspos
  have hOKi := sqrt_setIntegral_sq_mono (hint.mono_set hKD) hOK
  have hS' : ‖bS‖ = Real.sqrt (∫ y in annS p s, b y ^ 2) :=
    lp_norm_eq_sqrt_integral_sq bS b hbS
  have hD' : ‖bD‖ = Real.sqrt (∫ y in annD p s, b y ^ 2) :=
    lp_norm_eq_sqrt_integral_sq bD b hbD
  rw [← hS', ← hD'] at hmain
  rw [lp_norm_eq_sqrt_integral_sq bO b hbO]
  exact interp_coeff_bound hμ hM hC.le (norm_nonneg _) hSM (norm_nonneg _) hDM ha.le ha1.le
    (hOKi.trans hmain)

end NativeUniformSecond

/-- N: the radial weight value `exp(-Λ t²)`. -/
def nearE (Λ t : ℝ) : ℝ := Real.exp (Λ * -(t ^ 2))

/-- N: the radial interpolation exponent `(E(t)-E(c))/(E(a)-E(c))`. -/
def radGamma (Λ a t c : ℝ) : ℝ := (nearE Λ t - nearE Λ c) / (nearE Λ a - nearE Λ c)

/-- N: the near-one first-arm exponent `(E(1+α/4)-E(2))/(E(1-2α)-E(2))`. -/
def nearGamma (Λ α : ℝ) : ℝ := radGamma Λ (1 - 2 * α) (1 + α / 4) 2

theorem nearE_lt {Λ t u : ℝ} (hΛ : 0 < Λ) (ht : 0 ≤ t) (htu : t < u) :
    nearE Λ u < nearE Λ t := by
  unfold nearE
  have h1 : t ^ 2 < u ^ 2 := by nlinarith
  have h2 := mul_lt_mul_of_pos_left h1 hΛ
  exact Real.exp_lt_exp.mpr (by linarith)

/-- N1: the general squared-radius annular cutoff about `ctr` at scale `η`. -/
def genCut (a b c d : ℝ) (ctr : R3) (η : ℝ) (y : R3) : ℝ :=
  cutProfile a b c d (‖y - ctr‖ ^ 2 * (1 / η) ^ 2)

theorem contDiff_genCut (a b c d : ℝ) (ctr : R3) (η : ℝ) :
    ContDiff ℝ ∞ (genCut a b c d ctr η) :=
  contDiff_profile_slice (contDiff_cutProfile _ _ _ _) ctr (1 / η)

theorem genCut_ne_zero {a b c d η : ℝ} (ctr : R3) (hη : 0 < η) (ha : 0 ≤ a) (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) {y : R3} (h : genCut a b c d ctr η y ≠ 0) :
    a * η < ‖y - ctr‖ ∧ ‖y - ctr‖ < d * η := by
  obtain ⟨h1, h2⟩ := cutProfile_ne_zero (by nlinarith) (by nlinarith) h
  exact ⟨not_le.mp fun h' => (not_lt.mpr ((sqScaled_le_iff hη ha).mpr h')) h1,
    (sqScaled_lt_iff hη (by linarith)).mp h2⟩

theorem genCut_eq_one {a b c d η : ℝ} (ctr : R3) (hη : 0 < η) (ha : 0 ≤ a) (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) {y : R3} (h1 : b * η ≤ ‖y - ctr‖) (h2 : ‖y - ctr‖ ≤ c * η) :
    genCut a b c d ctr η y = 1 :=
  cutProfile_eq_one (by nlinarith) (by nlinarith)
    (not_lt.mp fun h => absurd ((sqScaled_lt_iff hη (by linarith)).mp h) (not_lt.mpr h1))
    ((sqScaled_le_iff hη hc).mpr h2)

theorem tsupport_genCut {a b c d η : ℝ} (ctr : R3) (hη : 0 < η) (ha : 0 ≤ a) (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) :
    tsupport (genCut a b c d ctr η) ⊆ closedAnnulus ctr (a * η) (d * η) :=
  closure_minimal (fun y hy => ⟨(genCut_ne_zero ctr hη ha hab hc hcd hy).1.le,
    (genCut_ne_zero ctr hη ha hab hc hcd hy).2.le⟩) (isClosed_closedAnnulus _ _ _)

theorem genCut_dich {a b c d η : ℝ} (ctr : R3) (hη : 0 < η) (ha : 0 ≤ a) (hab : a < b)
    (hbc : b ≤ c) (hcd : c < d) :
    ∀ x, x ∉ closedAnnulus ctr (a * η) (b * η) ∪ closedAnnulus ctr (c * η) (d * η) →
      genCut a b c d ctr η =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) ∨
        genCut a b c d ctr η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  intro x hx
  have hb : 0 ≤ b := by linarith
  have hc : 0 ≤ c := by linarith
  have hd : 0 ≤ d := by linarith
  have hab2 : a ^ 2 < b ^ 2 := by nlinarith
  have hcd2 : c ^ 2 < d ^ 2 := by nlinarith
  have htc : Continuous (fun y : R3 => ‖y - ctr‖ ^ 2 * (1 / η) ^ 2) := by fun_prop
  simp only [closedAnnulus, mem_union, mem_setOf_eq, not_or, not_and_or, not_le] at hx
  obtain ⟨h1 | h1, h2 | h2⟩ := hx
  · left
    have hlt : ‖x - ctr‖ ^ 2 * (1 / η) ^ 2 < a ^ 2 := (sqScaled_lt_iff hη ha).mpr h1
    filter_upwards [(isOpen_lt htc continuous_const).mem_nhds hlt] with y hy
    exact cutProfile_eq_zero_of_le hab2 (le_of_lt hy)
  · left
    have hlt : ‖x - ctr‖ ^ 2 * (1 / η) ^ 2 < a ^ 2 := (sqScaled_lt_iff hη ha).mpr h1
    filter_upwards [(isOpen_lt htc continuous_const).mem_nhds hlt] with y hy
    exact cutProfile_eq_zero_of_le hab2 (le_of_lt hy)
  · right
    have hlt1 : b ^ 2 < ‖x - ctr‖ ^ 2 * (1 / η) ^ 2 :=
      not_le.mp fun h => absurd ((sqScaled_le_iff hη hb).mp h) (not_le.mpr h1)
    have hlt2 : ‖x - ctr‖ ^ 2 * (1 / η) ^ 2 < c ^ 2 := (sqScaled_lt_iff hη hc).mpr h2
    filter_upwards [(isOpen_lt continuous_const htc).mem_nhds hlt1,
      (isOpen_lt htc continuous_const).mem_nhds hlt2] with y hy1 hy2
    exact cutProfile_eq_one hab2 hcd2 (le_of_lt hy1) (le_of_lt hy2)
  · left
    have hlt : d ^ 2 < ‖x - ctr‖ ^ 2 * (1 / η) ^ 2 :=
      not_le.mp fun h => absurd ((sqScaled_le_iff hη hd).mp h) (not_le.mpr h2)
    filter_upwards [(isOpen_lt continuous_const htc).mem_nhds hlt] with y hy
    exact cutProfile_eq_zero_of_ge hcd2 (le_of_lt hy)

/-- N2: the generic radial interpolation instance (the checked three-ball chain with general
radii): target `Ob` on the plateau with weight `≥ E(t)`, inner collar weight `≤ E(a)`, outer
collar weight `≤ E(c)`, exponent `radGamma Λ a t c`; all constants given before `q`. -/
theorem radial_interp_instance (g : MatrixField) (hg : IsAdmissibleMetric g)
    {lam η Λ τ0 Kr a b c d e f t : ℝ} {ctr : R3} {Ob : Set R3}
    (hη : 0 < η) (hΛ : 0 < Λ) (hKr : 0 ≤ Kr) (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (hbe : b < e) (hef : e ≤ f) (hdf : d < f) (hat : a < t) (htc : t < c)
    (hObm : MeasurableSet Ob) (hOb : ∀ y ∈ Ob, b * η ≤ ‖y - ctr‖ ∧ ‖y - ctr‖ ≤ t * η)
    {q : R3 → ℝ}
    (hq : ContDiffOn ℝ ∞ q (ball ctr (f * η)))
    (hL : ∀ y ∈ ball ctr (f * η), Lop (radialCoeff g (lam, ctr, 1 / η)) q y = 0)
    (hint : IntegrableOn (fun y => q y ^ 2) (ball ctr (f * η)))
    (HC : ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ closedAnnulus ctr (a * η) (d * η) →
      (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) * w y ^ 2) ≤
        ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) *
          Lop (radialCoeff g (lam, ctr, 1 / η)) w y ^ 2)
    (hRI : ∫ y in closedAnnulus ctr (a * η) (b * η),
        Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 ≤
      Kr * ∫ y in ball ctr (e * η), q y ^ 2)
    (hRO : ∫ y in closedAnnulus ctr (c * η) (d * η),
        Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 ≤
      Kr * ∫ y in ball ctr (f * η), q y ^ 2) :
    Real.sqrt (∫ y in Ob, q y ^ 2) ≤
      (2 * Real.sqrt Kr + Real.exp ((nearE Λ t - nearE Λ c) * max τ0 1)) *
        (Real.sqrt (∫ y in ball ctr (e * η), q y ^ 2) ^ radGamma Λ a t c *
          Real.sqrt (∫ y in ball ctr (f * η), q y ^ 2) ^ (1 - radGamma Λ a t c)) := by
  have hc0 : 0 ≤ c := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hchi := contDiff_genCut a b c d ctr η
  have hts := tsupport_genCut ctr hη ha hab hc0 hcd
  have hts4 : tsupport (genCut a b c d ctr η) ⊆ ball ctr (f * η) :=
    hts.trans (closedAnnulus_subset_ball (by nlinarith))
  have hw : ContDiff ℝ ∞ (fun z => genCut a b c d ctr η z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball hchi hts4 hq
  have hwts : tsupport (fun z => genCut a b c d ctr η z * q z) ⊆
      closedAnnulus ctr (a * η) (d * η) := tsupport_mul_subset_left.trans hts
  have hLzero : ∀ x, x ∉ closedAnnulus ctr (a * η) (b * η) ∪
      closedAnnulus ctr (c * η) (d * η) →
      Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) x = 0 :=
    Lop_cutoff_mul_eq_zero _ hts4 hL (genCut_dich ctr hη ha hab hbc hcd)
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, ctr, 1 / η))
    (radialCoeff_contDiff g hg _) hw
  have hψc : Continuous (fun y : R3 => Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) := by fun_prop
  have hKin := isCompact_closedAnnulus ctr (a * η) (b * η)
  have hKout := isCompact_closedAnnulus ctr (c * η) (d * η)
  have hL_int : Integrable (fun x =>
      Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hKin.union hKout)
      (fun x hx => by
        rw [Pi.pow_apply, hLzero x hx]
        norm_num))
  have hu_int : ∀ τ : ℝ, Integrable (fun x =>
      (Real.exp (τ * Real.exp (Λ * -(‖x - ctr‖ ^ 2 / η ^ 2))) *
        (genCut a b c d ctr η x * q x)) ^ 2) :=
    fun τ => (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul hw.continuous).pow
      2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedAnnulus ctr (a * η) (d * η)) (fun x hx => by
        have h0 : genCut a b c d ctr η x = 0 := by
          by_contra h
          exact hx (hts (subset_tsupport _ h))
        simp [h0]))
  have hObf : Ob ⊆ ball ctr (f * η) := fun y hy =>
    mem_ball_iff_norm.mpr (lt_of_le_of_lt (hOb y hy).2 (by nlinarith))
  have hstep : ∀ τ : ℝ, max τ0 1 ≤ τ →
      Real.sqrt (∫ y in Ob, q y ^ 2) ≤
        Real.sqrt Kr * (Real.exp (-((nearE Λ t - nearE Λ c) * τ)) *
          Real.sqrt (∫ y in ball ctr (f * η), q y ^ 2) +
          Real.exp ((nearE Λ a - nearE Λ t) * τ) *
            Real.sqrt (∫ y in ball ctr (e * η), q y ^ 2)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hτ
    have hcarl := HC τ ((le_max_left _ _).trans hτ) _ hw hwts
    have hsplit := carleman_collar_split (τ := τ) (u := fun z => genCut a b c d ctr η z * q z)
      (L := Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z))
      (ψ := fun y => Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) (wO := q)
      (KB := closedAnnulus ctr (a * η) (b * η)) (KH := closedAnnulus ctr (c * η) (d * η))
      (Ob := Ob) (hB := nearE Λ a) (hS := nearE Λ c) (hO := nearE Λ t)
      (by linarith) hcarl (hu_int τ) hL_int hKin.isClosed.measurableSet
      hKout.isClosed.measurableSet hObm hLzero
      (fun x hx => (radial_weight_bounds hΛ hη ha x ctr).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hη hc0 x ctr).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hη ht0 x ctr).2 (hOb x hx).2)
      (fun x hx => by
        have hx2 : ‖x - ctr‖ ≤ c * η := (hOb x hx).2.trans (by nlinarith)
        beta_reduce
        rw [genCut_eq_one ctr hη ha hab hc0 hcd (hOb x hx).1 hx2, one_mul])
      (hint.mono_set hObf)
    exact tb_balance_step (integral_nonneg fun x => sq_nonneg (q x))
      (integral_nonneg fun x => sq_nonneg (q x)) hKr hsplit hRI hRO
  have hAD : Real.sqrt (∫ y in Ob, q y ^ 2) ≤ Real.sqrt (∫ y in ball ctr (f * η), q y ^ 2) :=
    sqrt_setIntegral_sq_mono hint hObf
  have hα' : 0 < nearE Λ t - nearE Λ c := sub_pos.mpr (nearE_lt hΛ ht0 htc)
  have hβ' : 0 < nearE Λ a - nearE Λ t := sub_pos.mpr (nearE_lt hΛ ha hat)
  have hbal := exp_balance hα' hβ' (Real.sqrt_nonneg Kr) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hAD hstep
  have hsum : nearE Λ t - nearE Λ c + (nearE Λ a - nearE Λ t) = nearE Λ a - nearE Λ c := by
    ring
  have hne : nearE Λ a - nearE Λ c ≠ 0 := (by linarith : 0 < nearE Λ a - nearE Λ c).ne'
  have hcompl : (nearE Λ a - nearE Λ t) / (nearE Λ a - nearE Λ c) = 1 - radGamma Λ a t c := by
    unfold radGamma
    rw [eq_sub_iff_add_eq, ← add_div, show nearE Λ a - nearE Λ t + (nearE Λ t - nearE Λ c) =
      nearE Λ a - nearE Λ c by ring, div_self hne]
  rw [hsum, hcompl] at hbal
  exact hbal

/-- N3: the UNIFORM near-one radial interpolation. ONE `Λ` (the checked uniform radial
Carleman convexification on the FIXED support `[1/2, 5/2]`) is chosen BEFORE `α`; for each
`α ∈ (0, 1/4]` ONE `K` is chosen before `lam, c, η, p` and the solution. Target
`ball(p, α η/4)` on the sphere `‖p - c‖ = η`, observation `ball(c, (1-α/2)η)`,
full domain `ball(c, 3η)`, exponent `nearGamma Λ α`. -/
theorem uniform_near_one_interpolation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam1 B η0 η1 : ℝ) (hη0 : 0 < η0) (hηη : η0 ≤ η1) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∃ K : ℝ, 0 < K ∧
      ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B → ∀ η ∈ Icc η0 η1, ∀ p : R3, ‖p - c‖ = η →
      ∀ q : R3 → ℝ, ContDiffOn ℝ ∞ q (ball c (3 * η)) →
      (∀ y ∈ ball c (3 * η),
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0) →
      IntegrableOn (fun y => q y ^ 2) (ball c (3 * η)) →
      Real.sqrt (∫ y in ball p (α / 4 * η), q y ^ 2) ≤
        K * (Real.sqrt (∫ y in ball c ((1 - α / 2) * η), q y ^ 2) ^ nearGamma Λ α *
          Real.sqrt (∫ y in ball c (3 * η), q y ^ 2) ^ (1 - nearGamma Λ α)) := by
  obtain ⟨Λ, τ0, hΛ, HC⟩ := uniform_radial_carleman g hg lam1 B η0 η1 (1 / 2) (5 / 2) hη0 hηη
    (by norm_num)
  refine ⟨Λ, hΛ, fun α hα hα4 => ?_⟩
  obtain ⟨Mi, hMi, HMi⟩ := uniform_cutoff_residual_pointwise g hg lam1 B η0 η1 (1 - 2 * α)
    (1 - α) hη0 hηη (contDiff_cutProfile (1 - 2 * α) (1 - α) 2 (5 / 2))
  obtain ⟨Mo, hMo, HMo⟩ := uniform_cutoff_residual_pointwise g hg lam1 B η0 η1 2 (5 / 2)
    hη0 hηη (contDiff_cutProfile (1 - 2 * α) (1 - α) 2 (5 / 2))
  obtain ⟨Ci, hCi, HCi⟩ := uniform_caccioppoli g hg lam1 B η0 η1 (1 - α) (1 - 3 * α / 4)
    (1 - α / 2) hη0 hηη (by linarith) (by linarith) (by linarith)
  obtain ⟨Co, hCo, HCo⟩ := uniform_caccioppoli g hg lam1 B η0 η1 (5 / 2) (11 / 4) 3 hη0 hηη
    (by norm_num) (by norm_num) (by norm_num)
  have hKr : 0 ≤ Mi * (1 + Ci) + Mo * (1 + Co) := by positivity
  refine ⟨2 * Real.sqrt (Mi * (1 + Ci) + Mo * (1 + Co)) +
    Real.exp ((nearE Λ (1 + α / 4) - nearE Λ 2) * max τ0 1), by positivity, ?_⟩
  intro lam hlam c hc η hη p hp q hq hL hint
  have hη' : 0 < η := hη0.trans_le hη.1
  have hw : ContDiff ℝ ∞ (fun z => genCut (1 - 2 * α) (1 - α) 2 (5 / 2) c η z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball (contDiff_genCut _ _ _ _ c η)
      ((tsupport_genCut c hη' (by linarith) (by linarith) (by norm_num) (by norm_num)).trans
        (closedAnnulus_subset_ball (by linarith))) hq
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, c, 1 / η))
    (radialCoeff_contDiff g hg _) hw
  have hsub_e : ball c ((1 - α / 2) * η) ⊆ ball c (3 * η) := ball_subset_ball (by nlinarith)
  have hKin3 : closedAnnulus c ((1 - 2 * α) * η) ((1 - α) * η) ⊆ ball c (3 * η) :=
    closedAnnulus_subset_ball (by nlinarith)
  have hKout3 : closedAnnulus c (2 * η) (5 / 2 * η) ⊆ ball c (3 * η) :=
    closedAnnulus_subset_ball (by linarith)
  have hcI := HCi lam hlam c hc η hη q (hq.mono hsub_e) (fun y hy => hL y (hsub_e hy))
    (hint.mono_set hsub_e)
  have hcO := HCo lam hlam c hc η hη q hq hL hint
  have hRI0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / η))
      (fun z => genCut (1 - 2 * α) (1 - α) 2 (5 / 2) c η z * q z)) (Dom := ball c (3 * η))
    (isCompact_closedAnnulus c ((1 - 2 * α) * η) ((1 - α) * η))
    (closedAnnulus_subset_ball (by nlinarith)) (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c ((1 - α) * η)) (closedBall_subset_ball (by nlinarith)) isOpen_ball
    hMi hLc hq (hint.mono_set hsub_e)
    (fun y hy => HMi lam hlam c hc η hη y hy.1 hy.2 (ball c (3 * η)) isOpen_ball q hq
      (hKin3 hy) (hL y (hKin3 hy))) hcI
  have hRO0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / η))
      (fun z => genCut (1 - 2 * α) (1 - α) 2 (5 / 2) c η z * q z)) (Dom := ball c (3 * η))
    (isCompact_closedAnnulus c (2 * η) (5 / 2 * η)) hKout3
    (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c (5 / 2 * η)) (closedBall_subset_ball (by linarith)) isOpen_ball
    hMo hLc hq hint
    (fun y hy => HMo lam hlam c hc η hη y hy.1 hy.2 (ball c (3 * η)) isOpen_ball q hq
      (hKout3 hy) (hL y (hKout3 hy))) hcO
  have hS0 : 0 ≤ ∫ y in ball c ((1 - α / 2) * η), q y ^ 2 :=
    integral_nonneg fun x => sq_nonneg (q x)
  have hD0 : 0 ≤ ∫ y in ball c (3 * η), q y ^ 2 := integral_nonneg fun x => sq_nonneg (q x)
  have hi : 0 ≤ Mi * (1 + Ci) := by positivity
  have ho : 0 ≤ Mo * (1 + Co) := by positivity
  have hOb : ∀ y ∈ ball p (α / 4 * η), (1 - α) * η ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ (1 + α / 4) * η := by
    intro y hy
    have hyp : ‖y - p‖ < α / 4 * η := mem_ball_iff_norm.mp hy
    have h1 : ‖y - c‖ ≤ ‖y - p‖ + ‖p - c‖ := by
      have he : y - c = (y - p) + (p - c) := by abel
      rw [he]; exact norm_add_le _ _
    have h2 : ‖p - c‖ ≤ ‖y - c‖ + ‖y - p‖ := by
      have he : (y - c) - (y - p) = p - c := by abel
      have h := norm_sub_le (y - c) (y - p)
      rw [he] at h
      exact h
    have hαη : 0 < α * η := mul_pos hα hη'
    constructor <;> nlinarith
  have hsupp' : closedAnnulus c ((1 - 2 * α) * η) (5 / 2 * η) ⊆
      {y | 1 / 2 * η ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ 5 / 2 * η} := by
    intro y hy
    have h12 : 1 / 2 * η ≤ (1 - 2 * α) * η := by nlinarith
    exact ⟨h12.trans hy.1, hy.2⟩
  exact radial_interp_instance g hg (a := 1 - 2 * α) (b := 1 - α) (c := 2) (d := 5 / 2)
    (e := 1 - α / 2) (f := 3) (t := 1 + α / 4) (Ob := ball p (α / 4 * η))
    hη' hΛ hKr (by linarith) (by linarith) (by linarith) (by norm_num)
    (by linarith) (by linarith) (by norm_num) (by linarith) (by linarith) measurableSet_ball hOb
    hq hL hint
    (fun τ hτ w hw' hsupp => HC lam hlam c hc η hη τ hτ w hw' (hsupp.trans hsupp'))
    (hRI0.trans (mul_le_mul_of_nonneg_right (by linarith) hS0))
    (hRO0.trans (mul_le_mul_of_nonneg_right (by linarith) hD0))

/-- N4: for `0 < α ≤ 1/4` the near-one exponent lies in `(0,1)`. -/
theorem nearGamma_pos_lt_one {Λ α : ℝ} (hΛ : 0 < Λ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    0 < nearGamma Λ α ∧ nearGamma Λ α < 1 := by
  have h1 : nearE Λ 2 < nearE Λ (1 + α / 4) := nearE_lt hΛ (by linarith) (by linarith)
  have h2 : nearE Λ (1 + α / 4) < nearE Λ (1 - 2 * α) := nearE_lt hΛ (by linarith) (by linarith)
  unfold nearGamma radGamma
  constructor
  · exact div_pos (by linarith) (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

/-- N4: with `Λ` FIXED, the near-one exponent tends to `1` as `α → 0`: for every `γ2 > 0`
some `α ∈ (0, 1/4]` gives `γ1 + γ2 > 1`. -/
theorem nearGamma_near_one {Λ : ℝ} (hΛ : 0 < Λ) {γ2 : ℝ} (hγ2 : 0 < γ2) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 1 - γ2 < nearGamma Λ α := by
  have hden0 : nearE Λ 2 < nearE Λ (1 - 2 * 0) := nearE_lt hΛ (by norm_num) (by norm_num)
  have hnum : Continuous (fun α : ℝ => nearE Λ (1 + α / 4) - nearE Λ 2) := by
    unfold nearE; fun_prop
  have hden : Continuous (fun α : ℝ => nearE Λ (1 - 2 * α) - nearE Λ 2) := by
    unfold nearE; fun_prop
  have hca : ContinuousAt (fun α : ℝ => nearGamma Λ α) 0 :=
    hnum.continuousAt.div hden.continuousAt (sub_pos.mpr hden0).ne'
  have h0 : nearGamma Λ 0 = 1 := by
    unfold nearGamma radGamma
    rw [show (1 : ℝ) + 0 / 4 = 1 - 2 * 0 by norm_num]
    exact div_self (sub_pos.mpr hden0).ne'
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hca γ2 hγ2
  have hm : 0 < min (δ / 2) (1 / 4) := lt_min (by positivity) (by norm_num)
  refine ⟨min (δ / 2) (1 / 4), hm, min_le_right _ _, ?_⟩
  have hd : dist (min (δ / 2) (1 / 4)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hm]
    exact (min_le_left _ _).trans_lt (by linarith)
  have h := hδc hd
  beta_reduce at h
  rw [h0, Real.dist_eq] at h
  have := (abs_lt.mp h).1
  linarith

section NativeNearOneFirst
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

/-- N5: the UNIFORM near-one native FIRST basis arm for ORIGINAL `S.g1` and the literal first
operator: `Λ` before `α`, `K` after `α`, both before `lam, c, η, p`, every Gram system. -/
theorem uniform_near_one_first_arm (S : KnownSideSourceData) (lam1 B η0 η1 : ℝ)
    (hη0 : 0 < η0) (hηη : η0 ≤ η1) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∃ K : ℝ, 0 < K ∧
      ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ c : R3, ‖c‖ ≤ B → ∀ η ∈ Icc η0 η1, ∀ p : R3, ‖p - c‖ = η →
      FirstBasisArmOn S lam (ball c (3 * η)) (ball p (α / 4 * η)) (ball c ((1 - α / 2) * η))
        K (nearGamma Λ α) := by
  obtain ⟨Λ, hΛ, H⟩ := uniform_near_one_interpolation S.g1 S.g1_admissible lam1 B η0 η1 hη0 hηη
  refine ⟨Λ, hΛ, fun α hα hα4 => ?_⟩
  obtain ⟨K, hK, HK⟩ := H α hα hα4
  refine ⟨K, hK, fun lam hlam c hc η hη p hp => ?_⟩
  apply first_basis_arm_on_of_room
  intro u q hq hqs hpde uO uS hqO hqS
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hL : ∀ y ∈ ball c (3 * η),
      Lop (fun i k y => EnergyBridge.principalCoefficient S.g1 (lam • y) i k) q y = 0 := by
    intro y hy
    have h := hpde y hy
    rw [coordinateFluxDivergence_eq_divCoeffGrad] at h
    exact h
  have hI := HK lam hlam c hc η hη p hp q hqs hL hmem.integrable_sq
  rw [hnO, hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hI
  exact hI

open scoped Matrix.Norms.Elementwise

/-- N6: the UNIFORM coarse cross series on the literal annulus. The opening fraction `α`,
the constants `K1i, K2i` and exponents with `γ1 + γ2 > 1` are chosen BEFORE `lam0`; then for
every `lam ∈ (0, lam0]`, every actual separator zero `p` with `‖p‖ ≤ B` and `s ∈ [s0, s1]`,
the SAME spectral family / current coefficient bounds give the convergent cross series with
first opening `ball(p, α/4 · s/20)`. The compact cross data lie in the ORIGINAL `initialCross`
(certified by the checked uniform separator error, not by assuming `p 2 = 0`). -/
theorem uniform_coarse_cross_series (S : KnownSideSourceData) (B s0 s1 : ℝ) (hB : 0 < B)
    (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ ∃ K1i K2i γ1 γ2 : ℝ, 0 < K1i ∧ 0 < γ1 + γ2 - 1 ∧
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ (F : R3 × R3 → ℝ) (L lam : ℝ) (Ω : Set (R3 × R3)), IsOpen Ω →
      ProductSolutionOn S L lam F Ω → initialCross S lam ⊆ Ω → 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lam • p) = 0 → ∀ s ∈ Icc s0 s1,
      ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
        (hTD1 : T ⊆ D1) (ι : Type)
        (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        O1 = ball p (α / 4 * (s / 20)) ∧
        CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1
          {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
          (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
          K1i K2i γ1 γ2 ι w μ := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨K2i, γ2, -, hγ2, -, HB⟩ :=
    uniform_secondCoefficientInterpolation_annulus S 1 B s0 s1 hs0 hss
  obtain ⟨Λ, hΛ, HA⟩ := uniform_near_one_first_arm S 1 (B + s1 / 20) (s0 / 20) (s1 / 20)
    (by positivity) (by linarith)
  obtain ⟨α, hα, hα4, hαγ⟩ := nearGamma_near_one hΛ hγ2
  obtain ⟨K1i, hK1i, HA'⟩ := HA α hα hα4
  have he : 0 < α * s0 / 80 := by positivity
  obtain ⟨l1, hl1, Hsep⟩ :=
    exists_uniform_scaled_separating_error S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  obtain ⟨l2, hl2, Hcross⟩ :=
    exists_uniform_original_lower_cross S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  refine ⟨α, hα, hα4, K1i, K2i, nearGamma Λ α, γ2, hK1i, by linarith, min (min l1 l2) 1,
    lt_min (lt_min hl1 hl2) one_pos, ?_⟩
  intro F L lam Ω hΩ hSol hΩc hlam hlam0 p hp hp0 s hs
  have hspos : 0 < s := hs0.trans_le hs.1
  have hl1' : lam ≤ l1 := hlam0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hl2' : lam ≤ l2 := hlam0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlam1 : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le, hlam0.trans (min_le_right _ _)⟩
  have hpB : ‖p‖ ≤ B + 2 * s1 + 1 := by linarith
  have hp2 : |p 2| ≤ α * s0 / 80 / 2 := by
    have h := (Hsep lam hlam hl1' p hpB).2.1
    rw [hp0, zero_sub, abs_neg, abs_mul, abs_of_pos hlam, mul_div_assoc] at h
    exact le_of_mul_le_mul_left h hlam
  have hp2' := (abs_le.mp hp2).2
  set η : ℝ := s / 20 with hη_def
  have hη : 0 < η := by positivity
  set c : R3 := p - η • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) with hc_def
  have he2n : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  have hpc : ‖p - c‖ = η := by
    rw [hc_def, sub_sub_cancel, norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hη, mul_one]
  have hcB : ‖c‖ ≤ B + s1 / 20 := by
    have h := norm_sub_le p (η • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hη, mul_one] at h
    rw [hc_def]
    linarith [hs.2]
  have hηI : η ∈ Icc (s0 / 20) (s1 / 20) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have HA1 := HA' lam hlam1 c hcB η hηI p hpc
  have HB1 := HB L lam hlam1 p hp s hs
  have hc2 : c 2 = p 2 - η := by simp [hc_def, PiLp.sub_apply, PiLp.smul_apply]
  have hαη : α * η = α * s / 20 := by rw [hη_def]; ring
  have hαη0 : 0 ≤ α * η := by positivity
  have hαs : α * s0 ≤ α * s := mul_le_mul_of_nonneg_left hs.1 hα.le
  have hαs0 : α * s0 ≤ 1 / 4 * s0 := mul_le_mul_of_nonneg_right hα4 hs0.le
  have hrow : closedBall c ((1 - α / 2) * η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hΩc
    have hxc : ‖x - c‖ ≤ (1 - α / 2) * η := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hxp : ‖x - p‖ ≤ ‖x - c‖ + ‖p - c‖ := by
      have hh := norm_sub_le (x - c) (p - c)
      rwa [sub_sub_sub_cancel_right] at hh
    obtain ⟨hy1, hy2⟩ := hy
    have hcoord : (x - c) 2 ≤ ‖x - c‖ := (abs_le.mp (abs_coord_le_norm (x - c) 2)).2
    have hsum : x 2 = (x - c) 2 + c 2 := by simp only [PiLp.sub_apply]; ring
    have hx2 : x 2 ≤ -(α * s0 / 80) := by linarith
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    have hne : x ≠ y := by
      intro hxy
      rw [← hxy] at hy1
      linarith
    exact Hcross lam hlam hl2' (x, y) hxn hyn hne (Or.inl hx2)
  have hobs : closedBall c (3 * η) ×ˢ
      closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8) ⊆ Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hΩc
    have hxc : ‖x - c‖ ≤ 3 * η := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hxp : ‖x - p‖ ≤ ‖x - c‖ + ‖p - c‖ := by
      have hh := norm_sub_le (x - c) (p - c)
      rwa [sub_sub_sub_cancel_right] at hh
    have hyc : ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ≤ s / 8 := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    have hse : ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = s := by
      rw [norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hspos, mul_one]
    have hyp1 : ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤
        ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ + ‖y - p‖ := by
      have hh := norm_sub_le (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) (y - p)
      have he' : y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - (y - p) =
          s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by abel
      rwa [he'] at hh
    have hyp2 : ‖y - p‖ ≤ ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ +
        ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ := by
      have hh := norm_sub_le (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
        (s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      have he' : y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) -
          s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) = y - p := by abel
      rwa [he'] at hh
    have hcoord : (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) 2 ≤
        ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ :=
      (abs_le.mp (abs_coord_le_norm _ 2)).2
    have hj2 : (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = p 2 - s := by
      simp [PiLp.sub_apply, PiLp.smul_apply]
    have hsum : y 2 = (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) 2 +
        (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 := by
      simp only [PiLp.sub_apply]; ring
    have hy2 : y 2 ≤ -(α * s0 / 80) := by linarith [hs.1]
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    have hne : x ≠ y := by
      intro hxy
      rw [← hxy] at hyp1 hyc
      linarith
    exact Hcross lam hlam hl2' (x, y) hxn hyn hne (Or.inr hy2)
  obtain ⟨hDo, -, -, -, -, hOK, hKD, -⟩ := native_annulus_target_geometry p s hspos
  have hαη4 := mul_le_mul_of_nonneg_right hα4 hη.le
  have hO1D1 : ball p (α / 4 * η) ⊆ ball c (3 * η) :=
    ball_subset_ball' (by rw [dist_eq_norm, hpc]; linarith)
  have hKTD1 : closedBall c ((1 - α / 2) * η) ⊆ ball c (3 * η) :=
    closedBall_subset_ball (by linarith)
  have hTD1 : ball c ((1 - α / 2) * η) ⊆ ball c (3 * η) := ball_subset_closedBall.trans hKTD1
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms_sum F S L lam Ω hΩ hSol
    (ball c (3 * η)) (ball p (α / 4 * η)) (ball c ((1 - α / 2) * η)) (closedBall c (3 * η))
    (closedBall c ((1 - α / 2) * η))
    {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8))
    {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s}
    (closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8))
    isOpen_ball (isConnected_ball (by positivity)) hO1D1 isOpen_ball
    (nonempty_ball.mpr (mul_pos (by linarith) hη)) (isCompact_closedBall _ _)
    ball_subset_closedBall hKTD1
    hTD1 (isCompact_closedBall _ _) ball_subset_closedBall hDo (hOK.trans hKD) isOpen_ball
    (isCompact_native_closed_annulus p (s/2) (2*s)) (fun y hy => ⟨hy.1.le, hy.2.le⟩)
    (isCompact_closedBall _ _) ball_subset_closedBall hrow hobs hK1i (by linarith) HA1 HB1
  exact ⟨_, isOpen_ball, _, hO1D1, _, hTD1, ι, w, μ, rfl, hser⟩

end NativeNearOneFirst

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v051: range-free Carleman convexification and three-ball exponent (R1-R6 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

/-- Slices of a jointly smooth family are smooth. -/
theorem jointSmooth_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → R3 → ℝ} (hF : JointSmooth F) (P : E) : ContDiff ℝ ∞ (F P) := by
  have hJ : ContDiff ℝ ∞ (fun q : E × R3 => F q.1 q.2) := hF
  have h := hJ.comp (by fun_prop : ContDiff ℝ ∞ fun y : R3 => (P, y))
  exact h

/-- R1: one convexification `Λ` and one `τ0` for ANY jointly smooth symmetric family that is
positive definite with nondegenerate weight on a compact set `G ⊆ E × R3`; the support of the
test function is the `P`-slice of `G`. -/
theorem carleman_of_jointSmooth_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → Fin 3 → Fin 3 → R3 → ℝ) (ψ : E → R3 → ℝ) {G : Set (E × R3)} (hG : IsCompact G)
    (ha : ∀ i k, JointSmooth fun q => a q i k) (hψ : JointSmooth ψ)
    (hsymm : ∀ P i k, a P i k = a P k i)
    (hpos : ∀ x ∈ G, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < quad (a x.1) x.2 ξ)
    (hN : ∀ x ∈ G, 0 < Nf (a x.1) (ψ x.1) x.2) :
    ∃ Λ τ0 : ℝ, 0 < Λ ∧ ∀ P : E, ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ {y | (P, y) ∈ G} →
      (∫ x, Real.exp (2 * τ * phi (ψ P) Λ x) * w x ^ 2) ≤
        ∫ x, Real.exp (2 * τ * phi (ψ P) Λ x) * Lop (a P) w x ^ 2 := by
  have hA : Continuous (fun q : E × R3 => fun i k => a q.1 i k q.2) :=
    continuous_pi fun i => continuous_pi fun k => (ha i k).continuous
  have hdB : Continuous (fun q : E × R3 => fun i j => pd i (bv (a q.1) (ψ q.1) j) q.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      (jointSmooth_pd (F := fun q => bv (a q) (ψ q) j) (jointSmooth_bv ha hψ j) i).continuous
  have hdA : Continuous (fun q : E × R3 => fun j i k => pd j (a q.1 i k) q.2) :=
    continuous_pi fun j => continuous_pi fun i => continuous_pi fun k =>
      (jointSmooth_pd (F := fun q => a q i k) (ha i k) j).continuous
  have hb : Continuous (fun q : E × R3 => fun j => bv (a q.1) (ψ q.1) j q.2) :=
    continuous_pi fun j => (jointSmooth_bv ha hψ j).continuous
  have hQc : Continuous (fun p : (E × R3) × (Fin 3 → ℝ) => quad (a p.1.1) p.1.2 p.2) :=
    continuous_quad_form hA
  have hEc : Continuous (fun p : (E × R3) × (Fin 3 → ℝ) =>
      E1 (a p.1.1) (ψ p.1.1) p.1.2 p.2) := by
    have h := continuous_E1_form hA hdB hdA hb
    exact h
  obtain ⟨α, hα, hαG⟩ := quad_lower_param hG (fun x ξ => quad (a x.1) x.2 ξ) hQc
    (fun x t ξ => by simp only [quad, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring) hpos
  obtain ⟨C₁, hC₁⟩ := quad_upper_param hG (fun x ξ => E1 (a x.1) (ψ x.1) x.2 ξ) hEc
    (fun x t ξ => by simp only [E1, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)
  obtain ⟨n₀, hn₀, hn₀G⟩ := exists_pos_lower_of_compact hG
    (jointSmooth_Nf ha hψ).continuous.continuousOn hN
  obtain ⟨N₁, hN₁⟩ := exists_upper_of_compact hG (jointSmooth_Nf ha hψ).continuous.continuousOn
  obtain ⟨C₂, hC₂⟩ := exists_upper_of_compact hG (jointSmooth_Pf ha hψ).continuous.continuousOn
  obtain ⟨Ψ, hΨ⟩ := exists_upper_of_compact hG hψ.continuous.continuousOn
  have hK : ∀ P : E, IsCompact {y : R3 | (P, y) ∈ G} := fun P =>
    (hG.image continuous_snd).of_isClosed_subset
      (hG.isClosed.preimage (by fun_prop : Continuous fun y : R3 => (P, y)))
      (fun y hy => ⟨(P, y), hy, rfl⟩)
  obtain ⟨Λ, τ0, hΛ, H⟩ := carleman_family_of_bounds a ψ (fun P => {y : R3 | (P, y) ∈ G})
    (fun P i k => jointSmooth_slice (ha i k) P) hsymm (fun P => jointSmooth_slice hψ P) hK hα hn₀
    (fun P y hy ξ => hαG (P, y) hy ξ) (fun P y hy ξ => hC₁ (P, y) hy ξ)
    (fun P y hy => hn₀G (P, y) hy) (fun P y hy => hN₁ (P, y) hy)
    (fun P y hy => hC₂ (P, y) hy) (fun P y hy => hΨ (P, y) hy)
    (fun Λ κ => by
      obtain ⟨D, hD⟩ := exists_upper_of_compact hG
        (jointSmooth_Rf ha hψ Λ κ).continuous.continuousOn
      exact ⟨D, fun P y hy => hD (P, y) hy⟩)
  exact ⟨Λ, τ0, hΛ, H⟩

/-- R2: the normalized affine coefficient family `z ↦ principalCoefficient g (a + ρ z)`. -/
def affCoeffRF (g : MatrixField) (P : R3 × ℝ) : Fin 3 → Fin 3 → R3 → ℝ :=
  fun i k z => EnergyBridge.principalCoefficient g (P.1 + P.2 • z) i k

/-- R2: the fixed unit radial weight `-‖z‖²`. -/
def unitWeightRF (_P : R3 × ℝ) : R3 → ℝ := radialWeight ((0 : ℝ), (0 : R3), (1 : ℝ))

/-- R2: the compact normalized parameter/annulus set. -/
def affSetRF (δ ρ1 ρ2 : ℝ) : Set ((R3 × ℝ) × R3) :=
  (closedBall (0 : R3) δ ×ˢ Icc (-δ) δ) ×ˢ closedAnnulus 0 ρ1 ρ2

theorem isCompact_affSetRF (δ ρ1 ρ2 : ℝ) : IsCompact (affSetRF δ ρ1 ρ2) :=
  ((isCompact_closedBall _ _).prod isCompact_Icc).prod (isCompact_closedAnnulus 0 ρ1 ρ2)

theorem affSetRF_ne {δ ρ1 ρ2 : ℝ} (hρ1 : 0 < ρ1) {x : (R3 × ℝ) × R3}
    (hx : x ∈ affSetRF δ ρ1 ρ2) : x.2 ≠ 0 := by
  intro h
  have h1 : ρ1 ≤ ‖x.2 - 0‖ := hx.2.1
  rw [h, sub_zero, norm_zero] at h1
  linarith

theorem jointSmooth_affCoeffRF (g : MatrixField) (hg : IsAdmissibleMetric g) (i k : Fin 3) :
    JointSmooth fun P : R3 × ℝ => affCoeffRF g P i k :=
  (EnergyBridge.contDiff_principalCoefficient_entry g hg i k).comp
    (contDiff_fst.fst.add (contDiff_fst.snd.smul contDiff_snd))

theorem jointSmooth_unitWeightRF : JointSmooth unitWeightRF := by
  have h : ContDiff ℝ ∞ (fun q : (R3 × ℝ) × R3 => radialWeight ((0 : ℝ), (0 : R3), (1 : ℝ)) q.2) :=
    (radialWeight_contDiff _).comp contDiff_snd
  exact h

theorem affCoeffRF_symm (g : MatrixField) (hg : IsAdmissibleMetric g) (P : R3 × ℝ)
    (i k : Fin 3) : affCoeffRF g P i k = affCoeffRF g P k i := by
  funext y
  have := (EnergyBridge.principalCoefficient_posDef g hg (P.1 + P.2 • y)).1.apply i k
  simpa [affCoeffRF] using this.symm

theorem affCoeffRF_quad_pos (g : MatrixField) (hg : IsAdmissibleMetric g) (P : R3 × ℝ)
    (y : R3) {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) : 0 < quad (affCoeffRF g P) y ξ := by
  have := (EnergyBridge.principalCoefficient_posDef g hg (P.1 + P.2 • y)).dotProduct_mulVec_pos hξ
  convert this using 1
  simp [quad, affCoeffRF, dotProduct, Matrix.mulVec, Fin.sum_univ_three] <;> ring

theorem affCoeffRF_Nf_pos (g : MatrixField) (hg : IsAdmissibleMetric g) (P : R3 × ℝ)
    {z : R3} (hz : z ≠ 0) : 0 < Nf (affCoeffRF g P) (unitWeightRF P) z := by
  have hne := grad_ne_zero_of_fderiv_ne
    (fderiv_radialWeight_ne_zero (q := ((0 : ℝ), (0 : R3), (1 : ℝ))) one_ne_zero hz)
  have := affCoeffRF_quad_pos g hg P z hne
  convert this using 1
  simp only [Nf_apply, bv_apply, quad, grad, unitWeightRF, Fin.sum_univ_three]
  ring

/-- R3a: chain rule for the affine change of variables `x ↦ c + s x`. -/
theorem pd_comp_affineRF {f : R3 → ℝ} (c : R3) (s : ℝ) (k : Fin 3) (z : R3)
    (hf : DifferentiableAt ℝ f (c + s • z)) :
    pd k (fun x => f (c + s • x)) z = s * pd k f (c + s • z) := by
  have hT : HasFDerivAt (fun x : R3 => c + s • x) (s • ContinuousLinearMap.id ℝ R3) z :=
    ((hasFDerivAt_id z).const_smul s).const_add c
  have h : HasFDerivAt (fun x => f (c + s • x))
      ((fderiv ℝ f (c + s • z)).comp (s • ContinuousLinearMap.id ℝ R3)) z :=
    hf.hasFDerivAt.comp z hT
  show fderiv ℝ (fun x => f (c + s • x)) z (EuclideanSpace.single k 1) =
    s * fderiv ℝ f (c + s • z) (EuclideanSpace.single k 1)
  rw [h.fderiv]
  simp

/-- R3b: the divergence-form operator under `x ↦ c + s x` picks up exactly `s²`. -/
theorem Lop_comp_affineRF (a : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {w : R3 → ℝ} (hw : ContDiff ℝ ∞ w) (c : R3) (s : ℝ) (z : R3) :
    Lop (fun i k x => a i k (c + s • x)) (fun x => w (c + s • x)) z =
      s ^ 2 * Lop a w (c + s • z) := by
  have hF : ∀ i, ContDiff ℝ ∞ (fun y => ∑ k, a i k y * pd k w y) := fun i =>
    ContDiff.sum fun k _ => (ha i k).mul (contDiff_pd hw)
  have hin : ∀ i, (fun x => ∑ k, a i k (c + s • x) * pd k (fun x => w (c + s • x)) x) =
      fun x => s * ∑ k, a i k (c + s • x) * pd k w (c + s • x) := by
    intro i
    funext x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_comp_affineRF c s k x (diffAt hw _)]
    ring
  show ∑ i, pd i (fun x => ∑ k, a i k (c + s • x) * pd k (fun x => w (c + s • x)) x) z =
    s ^ 2 * ∑ i, pd i (fun y => ∑ k, a i k y * pd k w y) (c + s • z)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hin i]
  calc pd i (fun x => s * ∑ k, a i k (c + s • x) * pd k w (c + s • x)) z
      = s * pd i (fun y => s * ∑ k, a i k y * pd k w y) (c + s • z) :=
        pd_comp_affineRF (f := fun y => s * ∑ k, a i k y * pd k w y) c s i z
          ((contDiff_const.mul (hF i)).differentiable (by simp) _)
    _ = s ^ 2 * pd i (fun y => ∑ k, a i k y * pd k w y) (c + s • z) := by
        rw [pd_const_mul s (hF i)]
        ring

/-- R3c: Lebesgue measure under `z ↦ c + s z`, `s > 0`. -/
theorem integral_comp_affineRF (F : R3 → ℝ) (c : R3) {s : ℝ} (hs : 0 < s) :
    ∫ z, F (c + s • z) = (s ^ 3)⁻¹ * ∫ y, F y := by
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg (volume : Measure R3)
    (fun y => F (c + y)) s (hR := hs.le)
  simp only [show Module.finrank ℝ R3 = 3 from finrank_euclideanSpace_fin, smul_eq_mul] at h
  rw [h, integral_add_left_eq_self F c]

/-- R4: ONE `Λ` and ONE `τ0`, depending only on `g, δ, ρ1, ρ2`, for the ACTUAL coefficient
`principalCoefficient g (lam • y)` at EVERY center `c` and scale `s > 0` with `‖lam c‖ ≤ δ`,
`|lam s| ≤ δ`; the exact dimensional factor `s⁴` appears. No range `B, s0, s1` enters. -/
theorem uniform_affine_radial_carleman (g : MatrixField) (hg : IsAdmissibleMetric g)
    (δ ρ1 ρ2 : ℝ) (hρ1 : 0 < ρ1) :
    ∃ Λ τ0 : ℝ, 0 < Λ ∧ ∀ lam : ℝ, ∀ c : R3, ∀ s : ℝ, 0 < s → ‖lam • c‖ ≤ δ →
      |lam * s| ≤ δ → ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ {y | ρ1 * s ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ ρ2 * s} →
      (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) * w y ^ 2) ≤
        s ^ 4 * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y ^ 2 := by
  obtain ⟨Λ, τ0, hΛ, H⟩ := carleman_of_jointSmooth_compact (affCoeffRF g) unitWeightRF
    (isCompact_affSetRF δ ρ1 ρ2) (jointSmooth_affCoeffRF g hg) jointSmooth_unitWeightRF
    (affCoeffRF_symm g hg) (fun x _ ξ hξ => affCoeffRF_quad_pos g hg x.1 x.2 hξ)
    (fun x hx => affCoeffRF_Nf_pos g hg x.1 (affSetRF_ne hρ1 hx))
  refine ⟨Λ, τ0, hΛ, fun lam c s hs hc hls τ hτ w hw hsupp => ?_⟩
  have hT : ContDiff ℝ ∞ (fun z : R3 => c + s • z) := by fun_prop
  have hwt : ContDiff ℝ ∞ (fun z : R3 => w (c + s • z)) := hw.comp hT
  have hn : ∀ z : R3, ‖c + s • z - c‖ = s * ‖z‖ := fun z => by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
  have hsub : tsupport (fun z : R3 => w (c + s • z)) ⊆
      {z | ((lam • c, lam * s), z) ∈ affSetRF δ ρ1 ρ2} := by
    have hcl : IsClosed ((fun z : R3 => c + s • z) ⁻¹' tsupport w) :=
      (isClosed_tsupport w).preimage hT.continuous
    have hsp : Function.support (fun z : R3 => w (c + s • z)) ⊆
        (fun z : R3 => c + s • z) ⁻¹' tsupport w := fun z hz => subset_tsupport w hz
    refine (closure_minimal hsp hcl).trans ?_
    intro z hz
    obtain ⟨h1, h2⟩ := hsupp hz
    rw [hn z] at h1 h2
    refine ⟨⟨mem_closedBall_zero_iff.mpr hc, abs_le.mp hls⟩, ?_, ?_⟩
    · rw [sub_zero]
      exact le_of_mul_le_mul_left (by linarith : s * ρ1 ≤ s * ‖z‖) hs
    · rw [sub_zero]
      exact le_of_mul_le_mul_left (by linarith : s * ‖z‖ ≤ s * ρ2) hs
  have key := H (lam • c, lam * s) τ hτ (fun z => w (c + s • z)) hwt hsub
  have hcoef : affCoeffRF g (lam • c, lam * s) =
      fun i k z => EnergyBridge.principalCoefficient g (lam • (c + s • z)) i k := by
    funext i k z
    simp only [affCoeffRF, smul_add, mul_smul]
  have hL : ∀ z, Lop (affCoeffRF g (lam • c, lam * s)) (fun z => w (c + s • z)) z =
      s ^ 2 * Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w
        (c + s • z) := by
    intro z
    rw [hcoef]
    exact Lop_comp_affineRF (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
      (fun i k => radialCoeff_contDiff g hg (lam, 0, 0) i k) hw c s z
  have hphi : ∀ z : R3, Real.exp (2 * τ * phi (unitWeightRF (lam • c, lam * s)) Λ z) =
      Real.exp (2 * τ * Real.exp (Λ * -(‖c + s • z - c‖ ^ 2 / s ^ 2))) := by
    intro z
    have hq : ‖c + s • z - c‖ ^ 2 / s ^ 2 = ‖z - 0‖ ^ 2 * 1 ^ 2 := by
      rw [hn z, sub_zero, one_pow, mul_one, mul_pow, div_eq_iff (pow_ne_zero 2 hs.ne')]
      ring
    rw [hq]
    rfl
  have h1 := integral_comp_affineRF
    (fun y => Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) * w y ^ 2) c hs
  have h2 := integral_comp_affineRF
    (fun y => Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
      (s ^ 2 * Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y) ^ 2) c hs
  have h3 : (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
      (s ^ 2 * Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y) ^ 2) =
      s ^ 4 * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have e1 : (s ^ 3)⁻¹ * (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
      w y ^ 2) = ∫ z, Real.exp (2 * τ * phi (unitWeightRF (lam • c, lam * s)) Λ z) *
        w (c + s • z) ^ 2 := by
    rw [← h1]
    congr 1
    funext z
    rw [hphi z]
  have e2 : (∫ z, Real.exp (2 * τ * phi (unitWeightRF (lam • c, lam * s)) Λ z) *
      Lop (affCoeffRF g (lam • c, lam * s)) (fun z => w (c + s • z)) z ^ 2) =
      (s ^ 3)⁻¹ * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
        (s ^ 2 * Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y) ^ 2 := by
    rw [← h2]
    congr 1
    funext z
    rw [hphi z, hL z]
  have hk : (s ^ 3)⁻¹ * (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
      w y ^ 2) ≤ (s ^ 3)⁻¹ * (s ^ 4 * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w y ^ 2) := by
    calc (s ^ 3)⁻¹ * (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          w y ^ 2)
        = ∫ z, Real.exp (2 * τ * phi (unitWeightRF (lam • c, lam * s)) Λ z) *
            w (c + s • z) ^ 2 := e1
      _ ≤ ∫ z, Real.exp (2 * τ * phi (unitWeightRF (lam • c, lam * s)) Λ z) *
            Lop (affCoeffRF g (lam • c, lam * s)) (fun z => w (c + s • z)) z ^ 2 := key
      _ = _ := by rw [e2, h3]
  exact le_of_mul_le_mul_left hk (inv_pos.mpr (pow_pos hs 3))

/-- R5: the checked three-ball instance with a Carleman factor `M ≥ 0`. -/
theorem three_ball_instance_scaled (g : MatrixField) (hg : IsAdmissibleMetric g)
    {lam s Λ τ0 Kr M : ℝ} {c : R3} (hs : 0 < s) (hΛ : 0 < Λ) (hKr : 0 ≤ Kr) (hM : 0 ≤ M)
    {q : R3 → ℝ}
    (hq : ContDiffOn ℝ ∞ q (ball c (4 * s)))
    (hL : ∀ y ∈ ball c (4 * s), Lop (radialCoeff g (lam, c, 1 / s)) q y = 0)
    (hint : IntegrableOn (fun y => q y ^ 2) (ball c (4 * s)))
    (HC : ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ closedAnnulus c (1 / 4 * s) (3 * s) →
      (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) * w y ^ 2) ≤
        M * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          Lop (radialCoeff g (lam, c, 1 / s)) w y ^ 2)
    (hRI : ∫ y in closedAnnulus c (1 / 4 * s) (1 / 2 * s),
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 ≤
      Kr * ∫ y in ball c s, q y ^ 2)
    (hRO : ∫ y in closedAnnulus c (5 / 2 * s) (3 * s),
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 ≤
      Kr * ∫ y in ball c (4 * s), q y ^ 2) :
    Real.sqrt (∫ y in ball c (2 * s), q y ^ 2) ≤
      (1 + (2 * Real.sqrt (M * Kr) + Real.exp (tbAlpha Λ * max τ0 1))) *
        (Real.sqrt (∫ y in ball c s, q y ^ 2) ^ tbGamma Λ *
          Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) ^ (1 - tbGamma Λ)) := by
  have hchi := contDiff_threeBallCut c s
  have hts := tsupport_threeBallCut c hs
  have hts4 : tsupport (threeBallCut c s) ⊆ ball c (4 * s) :=
    hts.trans (closedAnnulus_subset_ball (by linarith))
  have hw : ContDiff ℝ ∞ (fun z => threeBallCut c s z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball hchi hts4 hq
  have hwts : tsupport (fun z => threeBallCut c s z * q z) ⊆
      closedAnnulus c (1 / 4 * s) (3 * s) := tsupport_mul_subset_left.trans hts
  have hLzero : ∀ x, x ∉ closedAnnulus c (1 / 4 * s) (1 / 2 * s) ∪
      closedAnnulus c (5 / 2 * s) (3 * s) →
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x = 0 :=
    Lop_cutoff_mul_eq_zero _ hts4 hL (threeBallCut_dich c hs)
  have hLzero' : ∀ x, x ∉ closedAnnulus c (1 / 4 * s) (1 / 2 * s) ∪
      closedAnnulus c (5 / 2 * s) (3 * s) →
      Real.sqrt M * Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x
        = 0 := fun x hx => by rw [hLzero x hx, mul_zero]
  have hLzero'' : ∀ x, x ∉ closedAnnulus c (1 / 4 * s) (1 / 2 * s) ∪
      closedAnnulus c (5 / 2 * s) (3 * s) →
      (Real.sqrt M * Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x)
        ^ 2 = 0 := fun x hx => by rw [hLzero' x hx]; norm_num
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, c, 1 / s))
    (radialCoeff_contDiff g hg _) hw
  have hψc : Continuous (fun y : R3 => Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) := by fun_prop
  have hKin := isCompact_closedAnnulus c (1 / 4 * s) (1 / 2 * s)
  have hKout := isCompact_closedAnnulus c (5 / 2 * s) (3 * s)
  have hL_int : Integrable (fun x => (Real.sqrt M *
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x) ^ 2) :=
    ((continuous_const.mul hLc).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hKin.union hKout) hLzero'')
  have hu_int : ∀ τ : ℝ, Integrable (fun x =>
      (Real.exp (τ * Real.exp (Λ * -(‖x - c‖ ^ 2 / s ^ 2))) * (threeBallCut c s x * q x)) ^ 2) :=
    fun τ => (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul hw.continuous).pow
      2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedAnnulus c (1 / 4 * s) (3 * s)) (fun x hx => by
        have h0 : threeBallCut c s x = 0 := by
          by_contra h
          exact hx (hts (subset_tsupport _ h))
        simp [h0]))
  have hOb4 : ball c (2 * s) \ ball c (1 / 2 * s) ⊆ ball c (4 * s) :=
    diff_subset.trans (ball_subset_ball (by linarith))
  have hRI' : (∫ y in closedAnnulus c (1 / 4 * s) (1 / 2 * s), (Real.sqrt M *
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y) ^ 2) ≤
      M * Kr * ∫ y in ball c s, q y ^ 2 := by
    have e : (∫ y in closedAnnulus c (1 / 4 * s) (1 / 2 * s), (Real.sqrt M *
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y) ^ 2) =
        M * ∫ y in closedAnnulus c (1 / 4 * s) (1 / 2 * s),
          Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [mul_pow, Real.sq_sqrt hM]
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hRI hM
  have hRO' : (∫ y in closedAnnulus c (5 / 2 * s) (3 * s), (Real.sqrt M *
      Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y) ^ 2) ≤
      M * Kr * ∫ y in ball c (4 * s), q y ^ 2 := by
    have e : (∫ y in closedAnnulus c (5 / 2 * s) (3 * s), (Real.sqrt M *
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y) ^ 2) =
        M * ∫ y in closedAnnulus c (5 / 2 * s) (3 * s),
          Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [mul_pow, Real.sq_sqrt hM]
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hRO hM
  have hstep : ∀ τ : ℝ, max τ0 1 ≤ τ →
      Real.sqrt (∫ y in ball c (2 * s) \ ball c (1 / 2 * s), q y ^ 2) ≤
        Real.sqrt (M * Kr) * (Real.exp (-(tbAlpha Λ * τ)) *
          Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) +
          Real.exp (tbBeta Λ * τ) * Real.sqrt (∫ y in ball c s, q y ^ 2)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hτ
    have hcarl := HC τ ((le_max_left _ _).trans hτ) _ hw hwts
    have hcarl' : (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
        (threeBallCut c s y * q y) ^ 2) ≤
        ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          (Real.sqrt M * Lop (radialCoeff g (lam, c, 1 / s))
            (fun z => threeBallCut c s z * q z) y) ^ 2 := by
      have e : (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
          (Real.sqrt M * Lop (radialCoeff g (lam, c, 1 / s))
            (fun z => threeBallCut c s z * q z) y) ^ 2) =
          M * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) *
            Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) y ^ 2 := by
        rw [← integral_const_mul]
        congr 1
        funext y
        rw [mul_pow, Real.sq_sqrt hM]
        ring
      rw [e]
      exact hcarl
    have hsplit := carleman_collar_split (τ := τ) (u := fun z => threeBallCut c s z * q z)
      (L := fun x => Real.sqrt M *
        Lop (radialCoeff g (lam, c, 1 / s)) (fun z => threeBallCut c s z * q z) x)
      (ψ := fun y => Real.exp (Λ * -(‖y - c‖ ^ 2 / s ^ 2))) (wO := q)
      (KB := closedAnnulus c (1 / 4 * s) (1 / 2 * s)) (KH := closedAnnulus c (5 / 2 * s) (3 * s))
      (Ob := ball c (2 * s) \ ball c (1 / 2 * s)) (hB := tbEin Λ) (hS := tbEo Λ) (hO := tbEt Λ)
      (by linarith) hcarl' (hu_int τ) hL_int hKin.isClosed.measurableSet
      hKout.isClosed.measurableSet (measurableSet_ball.diff measurableSet_ball) hLzero'
      (fun x hx => (radial_weight_bounds hΛ hs (by norm_num : (0 : ℝ) ≤ 1 / 4) x c).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hs (by norm_num : (0 : ℝ) ≤ 5 / 2) x c).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hs (by norm_num : (0 : ℝ) ≤ 2) x c).2
        (le_of_lt (mem_ball_iff_norm.mp hx.1)))
      (fun x hx => by
        have h1 : 1 / 2 * s ≤ ‖x - c‖ :=
          not_lt.mp fun h => hx.2 (mem_ball_iff_norm.mpr h)
        have h2 : ‖x - c‖ ≤ 5 / 2 * s := by
          have := mem_ball_iff_norm.mp hx.1
          linarith
        beta_reduce
        rw [threeBallCut_eq_one c hs h1 h2, one_mul])
      (hint.mono_set hOb4)
    exact tb_balance_step (integral_nonneg fun x => sq_nonneg (q x))
      (integral_nonneg fun x => sq_nonneg (q x)) (mul_nonneg hM hKr) hsplit hRI' hRO'
  have hS4 : ball c s ⊆ ball c (4 * s) := ball_subset_ball (by linarith)
  have hsub : ball c (1 / 2 * s) ⊆ ball c (2 * s) := ball_subset_ball (by linarith)
  have hAD : Real.sqrt (∫ y in ball c (2 * s) \ ball c (1 / 2 * s), q y ^ 2) ≤
      Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set hint
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _) hOb4.eventuallyLE)
  have hSD : Real.sqrt (∫ y in ball c s, q y ^ 2) ≤ Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set hint
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _) hS4.eventuallyLE)
  have hXS : Real.sqrt (∫ y in ball c (1 / 2 * s), q y ^ 2) ≤
      Real.sqrt (∫ y in ball c s, q y ^ 2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set (hint.mono_set hS4)
      (Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (ball_subset_ball (by linarith)).eventuallyLE)
  have hT : ∫ y in ball c (2 * s), q y ^ 2 = (∫ y in ball c (1 / 2 * s), q y ^ 2) +
      ∫ y in ball c (2 * s) \ ball c (1 / 2 * s), q y ^ 2 := by
    conv_lhs => rw [← Set.union_diff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right (measurableSet_ball.diff measurableSet_ball)
      (hint.mono_set (hsub.trans (ball_subset_ball (by linarith)))) (hint.mono_set hOb4)
  have hbal := exp_balance (tbAlpha_pos hΛ) (tbBeta_pos hΛ) (Real.sqrt_nonneg (M * Kr))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hAD hstep
  rw [tbGamma_compl hΛ] at hbal
  exact tb_combine (integral_nonneg fun x => sq_nonneg (q x))
    (integral_nonneg fun x => sq_nonneg (q x)) (Real.sqrt_nonneg _) hSD (tbGamma_pos hΛ)
    (tbGamma_lt_one hΛ) hT hXS hbal

/-- R6: the RANGE-FREE three-ball exponent. ONE `γ ∈ (0,1)` is chosen BEFORE the bounded center
range `B` and the scale interval `[s0, s1]`; only `K` and the dilation ceiling `lam0` depend on
that range. Literal coefficient `principalCoefficient g (lam • y)`, local solutions on
`ball c (4s)`, restricted-volume L² integrals. -/
theorem uniform_three_ball_range_free (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∀ B s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 →
      ∃ K lam0 : ℝ, 0 < K ∧ 0 < lam0 ∧ ∀ lam ∈ Icc (0 : ℝ) lam0, ∀ c : R3, ‖c‖ ≤ B →
      ∀ s ∈ Icc s0 s1, ∀ q : R3 → ℝ, ContDiffOn ℝ ∞ q (ball c (4 * s)) →
      (∀ y ∈ ball c (4 * s),
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0) →
      IntegrableOn (fun y => q y ^ 2) (ball c (4 * s)) →
      Real.sqrt (∫ y in ball c (2 * s), q y ^ 2) ≤
        K * (Real.sqrt (∫ y in ball c s, q y ^ 2) ^ γ *
          Real.sqrt (∫ y in ball c (4 * s), q y ^ 2) ^ (1 - γ)) := by
  obtain ⟨Λ, τ0, hΛ, HC⟩ := uniform_affine_radial_carleman g hg 1 (1 / 4) 3 (by norm_num)
  refine ⟨tbGamma Λ, tbGamma_pos hΛ, tbGamma_lt_one hΛ, fun B s0 s1 hs0 hss => ?_⟩
  have hs1 : 0 < s1 := hs0.trans_le hss
  have hden : 0 < |B| + s1 + 1 := by positivity
  have hlam0 : 0 < 1 / (|B| + s1 + 1) := by positivity
  obtain ⟨Mi, hMi, HMi⟩ := uniform_cutoff_residual_pointwise g hg (1 / (|B| + s1 + 1)) B s0 s1
    (1 / 4) (1 / 2) hs0 hss (contDiff_cutProfile (1 / 4) (1 / 2) (5 / 2) 3)
  obtain ⟨Mo, hMo, HMo⟩ := uniform_cutoff_residual_pointwise g hg (1 / (|B| + s1 + 1)) B s0 s1
    (5 / 2) 3 hs0 hss (contDiff_cutProfile (1 / 4) (1 / 2) (5 / 2) 3)
  obtain ⟨Ci, hCi, HCi⟩ := uniform_caccioppoli g hg (1 / (|B| + s1 + 1)) B s0 s1 (1 / 2) (3 / 4) 1
    hs0 hss (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Co, hCo, HCo⟩ := uniform_caccioppoli g hg (1 / (|B| + s1 + 1)) B s0 s1 3 (7 / 2) 4
    hs0 hss (by norm_num) (by norm_num) (by norm_num)
  have hKr : 0 ≤ Mi * (1 + Ci) + Mo * (1 + Co) := by positivity
  refine ⟨1 + (2 * Real.sqrt (s1 ^ 4 * (Mi * (1 + Ci) + Mo * (1 + Co))) +
    Real.exp (tbAlpha Λ * max τ0 1)), 1 / (|B| + s1 + 1), by positivity, hlam0, ?_⟩
  intro lam hlam c hc s hs q hq hL hint
  have hs' : 0 < s := hs0.trans_le hs.1
  have hlc : ‖lam • c‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hlam.1]
    have h1 : lam * ‖c‖ ≤ 1 / (|B| + s1 + 1) * (|B| + s1 + 1) :=
      mul_le_mul hlam.2 (by linarith [le_abs_self B]) (norm_nonneg c) hlam0.le
    rwa [one_div_mul_cancel hden.ne'] at h1
  have hls : |lam * s| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hlam.1 hs'.le)]
    have h1 : lam * s ≤ 1 / (|B| + s1 + 1) * (|B| + s1 + 1) :=
      mul_le_mul hlam.2 (by linarith [abs_nonneg B, hs.2]) hs'.le hlam0.le
    rwa [one_div_mul_cancel hden.ne'] at h1
  have hw : ContDiff ℝ ∞ (fun z => threeBallCut c s z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball (contDiff_threeBallCut c s)
      ((tsupport_threeBallCut c hs').trans (closedAnnulus_subset_ball (by linarith))) hq
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, c, 1 / s))
    (radialCoeff_contDiff g hg _) hw
  have hKin4 : closedAnnulus c (1 / 4 * s) (1 / 2 * s) ⊆ ball c (4 * s) :=
    closedAnnulus_subset_ball (by linarith)
  have hKout4 : closedAnnulus c (5 / 2 * s) (3 * s) ⊆ ball c (4 * s) :=
    closedAnnulus_subset_ball (by linarith)
  have hcI := HCi lam hlam c hc s hs q (hq.mono (ball_subset_ball (by linarith)))
    (fun y hy => hL y (ball_subset_ball (by linarith) hy))
    (hint.mono_set (ball_subset_ball (by linarith)))
  rw [one_mul] at hcI
  have hcO := HCo lam hlam c hc s hs q hq hL hint
  have hRI0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / s))
      (fun z => threeBallCut c s z * q z)) (Dom := ball c (4 * s))
    (isCompact_closedAnnulus c (1 / 4 * s) (1 / 2 * s))
    (closedAnnulus_subset_ball (by linarith)) (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c (1 / 2 * s)) (closedBall_subset_ball (by linarith)) isOpen_ball
    hMi hLc hq (hint.mono_set (ball_subset_ball (by linarith)))
    (fun y hy => HMi lam hlam c hc s hs y hy.1 hy.2 (ball c (4 * s)) isOpen_ball q hq
      (hKin4 hy) (hL y (hKin4 hy))) hcI
  have hRO0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / s))
      (fun z => threeBallCut c s z * q z)) (Dom := ball c (4 * s))
    (isCompact_closedAnnulus c (5 / 2 * s) (3 * s)) hKout4
    (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c (3 * s)) (closedBall_subset_ball (by linarith)) isOpen_ball
    hMo hLc hq hint
    (fun y hy => HMo lam hlam c hc s hs y hy.1 hy.2 (ball c (4 * s)) isOpen_ball q hq
      (hKout4 hy) (hL y (hKout4 hy))) hcO
  have hS0 : 0 ≤ ∫ y in ball c s, q y ^ 2 := integral_nonneg fun x => sq_nonneg (q x)
  have hD0 : 0 ≤ ∫ y in ball c (4 * s), q y ^ 2 := integral_nonneg fun x => sq_nonneg (q x)
  have hi : 0 ≤ Mi * (1 + Ci) := by positivity
  have ho : 0 ≤ Mo * (1 + Co) := by positivity
  exact three_ball_instance_scaled g hg hs' hΛ hKr (pow_nonneg hs1.le 4) hq hL hint
    (fun τ hτ w hw' hsupp => (HC lam c s hs' hlc hls τ hτ w hw' hsupp).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs'.le hs.2 4)
        (integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))))
    (hRI0.trans (mul_le_mul_of_nonneg_right (by linarith) hS0))
    (hRO0.trans (mul_le_mul_of_nonneg_right (by linarith) hD0))

/-- R7: a unit center is good with an exponent chosen BEFORE the range `B, [s0, s1]`; only the
constant and the dilation ceiling depend on the range. -/
def AnnGoodRF (g : MatrixField) (b : R3) : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ B s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 →
    ∃ C lam1 : ℝ, 0 < C ∧ 0 < lam1 ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3, ‖p‖ ≤ B →
    ∀ s ∈ Icc s0 s1, ∀ q : R3 → ℝ, AnnClass g lam p s q →
      Real.sqrt (∫ y in ball (p + s • b) (s/40), q y ^ 2) ≤
        C * (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ a *
          Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - a))

/-- R7(i): the base unit center, exponent `1/2`. -/
theorem annGoodRF_base (g : MatrixField) :
    AnnGoodRF g (-EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
  refine ⟨1/2, by norm_num, by norm_num, fun B s0 s1 hs0 _ => ⟨1, 1, one_pos, one_pos, ?_⟩⟩
  intro lam _ p _ s hs q hq
  have hspos : 0 < s := hs0.trans_le hs.1
  obtain ⟨-, -, hint⟩ := hq
  have hSD := sqrt_setIntegral_sq_mono hint (annS_subset_annD p hspos)
  have hY := sqrt_setIntegral_sq_mono (hint.mono_set (annS_subset_annD p hspos))
    (annA_base_ball p hspos)
  have hw := interpolation_weight_antitone (Real.sqrt_nonneg _) hSD
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  rw [Real.rpow_one, sub_self, Real.rpow_zero, mul_one] at hw
  rw [one_mul]
  exact hY.trans hw

/-- R7(ii): one range-free three-ball step (scale `s/40`) along a unit step `≤ 1/40`. -/
theorem annGoodRF_step (g : MatrixField) (hg : IsAdmissibleMetric g) {b b' : R3}
    (hb : b ∈ annA) (hbb : dist b' b ≤ 1/40) (hG : AnnGoodRF g b) : AnnGoodRF g b' := by
  obtain ⟨γ, hγ, hγ1, H3⟩ := uniform_three_ball_range_free g hg
  obtain ⟨a, ha, ha1, HG⟩ := hG
  refine ⟨a * γ, mul_pos ha hγ, by nlinarith, fun B s0 s1 hs0 hss => ?_⟩
  obtain ⟨K, lam3, hK, hlam3, H⟩ := H3 (B + 11/8 * s1) (s0/40) (s1/40) (by positivity)
    (by linarith)
  obtain ⟨C, lam1, hC, hlam1, HGr⟩ := HG B s0 s1 hs0 hss
  refine ⟨K * C ^ γ, min lam1 lam3, by positivity, lt_min hlam1 hlam3, ?_⟩
  intro lam hlam p hp s hs q hq
  have hl1 : lam ∈ Icc (0 : ℝ) lam1 := ⟨hlam.1, hlam.2.trans (min_le_left _ _)⟩
  have hl3 : lam ∈ Icc (0 : ℝ) lam3 := ⟨hlam.1, hlam.2.trans (min_le_right _ _)⟩
  have hspos : 0 < s := hs0.trans_le hs.1
  have hT0 := HGr lam hl1 p hp s hs q hq
  obtain ⟨hqs, hL, hint⟩ := hq
  have hb2 : ‖b‖ < 11/8 := by
    obtain ⟨-, h⟩ := hb
    rw [sub_zero] at h
    exact h
  have h4 := annA_ball_subset p hspos hb
  have hc := annA_center_norm hp hspos hs.2 hb2
  have hr : s/40 ∈ Icc (s0/40) (s1/40) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hT := H lam hl3 (p + s • b) hc (s/40) hr q (hqs.mono h4) (fun y hy => hL y (h4 hy))
    (hint.mono_set h4)
  have h2 : ball (p + s • b) (2 * (s/40)) ⊆ annD p s :=
    (ball_subset_ball (by linarith)).trans h4
  have hO := sqrt_setIntegral_sq_mono (hint.mono_set h2) (annA_step_subset p hspos hbb)
  have hDl := sqrt_setIntegral_sq_mono hint h4
  exact interpolation_compose (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hC.le hK.le ha ha1 hγ hγ1 (Real.sqrt_nonneg _) hDl hT0 (hO.trans hT)

/-- R7(iii): clopen reachability on the connected open unit annulus. -/
theorem annA_subset_goodRF (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∀ b ∈ annA, AnnGoodRF g b := by
  have hu : IsOpen {b : R3 | b ∈ annA ∧ AnnGoodRF g b} := by
    rw [Metric.isOpen_iff]
    rintro b ⟨hbA, hbG⟩
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp isOpen_annA b hbA
    refine ⟨min ε (1/40), lt_min hε (by norm_num), fun b' hb' => ?_⟩
    have hd : dist b' b < min ε (1/40) := mem_ball.mp hb'
    have hb'A : b' ∈ annA := hεA (mem_ball.mpr (hd.trans_le (min_le_left _ _)))
    exact ⟨hb'A, annGoodRF_step g hg hbA (hd.le.trans (min_le_right _ _)) hbG⟩
  have hv : IsOpen {b : R3 | b ∈ annA ∧ ¬ AnnGoodRF g b} := by
    rw [Metric.isOpen_iff]
    rintro b ⟨hbA, hbG⟩
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp isOpen_annA b hbA
    refine ⟨min ε (1/40), lt_min hε (by norm_num), fun b' hb' => ?_⟩
    have hd : dist b' b < min ε (1/40) := mem_ball.mp hb'
    have hb'A : b' ∈ annA := hεA (mem_ball.mpr (hd.trans_le (min_le_left _ _)))
    refine ⟨hb'A, fun hG' => hbG ?_⟩
    rw [dist_comm] at hd
    exact annGoodRF_step g hg hb'A (hd.le.trans (min_le_right _ _)) hG'
  have huv : Disjoint {b : R3 | b ∈ annA ∧ AnnGoodRF g b}
      {b : R3 | b ∈ annA ∧ ¬ AnnGoodRF g b} :=
    Set.disjoint_left.mpr fun b hbu hbv => hbv.2 hbu.2
  have hcov : annA ⊆ {b : R3 | b ∈ annA ∧ AnnGoodRF g b} ∪
      {b : R3 | b ∈ annA ∧ ¬ AnnGoodRF g b} := by
    intro b hb
    by_cases h : AnnGoodRF g b
    · exact Or.inl ⟨hb, h⟩
    · exact Or.inr ⟨hb, h⟩
  have hne : (annA ∩ {b : R3 | b ∈ annA ∧ AnnGoodRF g b}).Nonempty :=
    ⟨_, annA_base_mem, annA_base_mem, annGoodRF_base g⟩
  intro b hb
  exact (isPreconnected_annA.subset_left_of_subset_union hu hv huv hcov hne hb).2

/-- R8: the annulus integral interpolation with ONE exponent `a ∈ (0,1)` chosen BEFORE the
range `B, [s0, s1]`; the constant `C` and the dilation ceiling `lam1` come after the range. -/
theorem uniform_annulus_interpolation_RF (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ B s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 →
      ∃ C lam1 : ℝ, 0 < C ∧ 0 < lam1 ∧ ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3, ‖p‖ ≤ B →
      ∀ s ∈ Icc s0 s1, ∀ q : R3 → ℝ, AnnClass g lam p s q →
        Real.sqrt (∫ y in {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4}, q y ^ 2) ≤
          C * (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ a *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - a)) := by
  classical
  have hKu : IsCompact annKu := isCompact_native_closed_annulus 0 (3/4) (5/4)
  have hKuA : ∀ b ∈ annKu, b ∈ annA := by
    intro b hb
    obtain ⟨h1, h2⟩ := hb
    exact ⟨by linarith, by linarith⟩
  obtain ⟨t, ht⟩ := hKu.elim_finite_subcover (fun b : annKu => ball (b : R3) (1/40))
    (fun _ => isOpen_ball) (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (by norm_num)⟩)
  have hgood : ∀ b : annKu, AnnGoodRF g (b : R3) :=
    fun b => annA_subset_goodRF g hg b (hKuA b b.2)
  unfold AnnGoodRF at hgood
  choose a ha ha1 HG using hgood
  let A : Finset ℝ := insert (1/2) (t.image a)
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  have hamem : A.min' hAne ∈ A := Finset.min'_mem A hAne
  have hA : ∀ x ∈ A, 0 < x ∧ x < 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨ha i, ha1 i⟩
  have hale : ∀ i ∈ t, A.min' hAne ≤ a i := fun i hi =>
    Finset.min'_le A _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hi))
  refine ⟨A.min' hAne, (hA _ hamem).1, (hA _ hamem).2, fun B s0 s1 hs0 hss => ?_⟩
  choose C lam1 hC hlam1 HGr using fun i : annKu => HG i B s0 s1 hs0 hss
  let L : Finset ℝ := insert 1 (t.image lam1)
  have hLne : L.Nonempty := Finset.insert_nonempty _ _
  have hLpos : 0 < L.min' hLne := by
    rcases Finset.mem_insert.mp (Finset.min'_mem L hLne) with h | h
    · rw [h]; norm_num
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact hlam1 i
  have hLle : ∀ i ∈ t, L.min' hLne ≤ lam1 i := fun i hi =>
    Finset.min'_le L _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem lam1 hi))
  have hsum : 0 ≤ ∑ i ∈ t, (C i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨Real.sqrt (∑ i ∈ t, (C i) ^ 2) + 1, L.min' hLne, by positivity, hLpos, ?_⟩
  intro lam hlam p hp s hsI q hq
  have hspos : 0 < s := hs0.trans_le hsI.1
  have hint : IntegrableOn (fun y => q y ^ 2) (annD p s) := by
    obtain ⟨-, -, h⟩ := hq
    exact h
  have hSD := sqrt_setIntegral_sq_mono hint (annS_subset_annD p hspos)
  have hcover : {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} ⊆
      ⋃ i ∈ t, ball (p + s • (i : R3)) (s/40) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    set b : R3 := s⁻¹ • (y - p) with hb
    have hyb : y = p + s • b := by
      rw [hb, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
      abel
    have hnb : ‖b‖ = ‖y - p‖ / s := by
      rw [hb, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hspos, inv_mul_eq_div]
    have hbK : b ∈ annKu := by
      show 3/4 ≤ ‖b - 0‖ ∧ ‖b - 0‖ ≤ 5/4
      rw [sub_zero, hnb, le_div_iff₀ hspos, div_le_iff₀ hspos]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.mp (ht hbK)
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    have hdist : dist y (p + s • (i : R3)) = s * dist b (i : R3) := by
      calc dist y (p + s • (i : R3)) = dist (p + s • b) (p + s • (i : R3)) := by rw [← hyb]
        _ = s * dist b (i : R3) := by
          rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hspos]
    rw [mem_ball, hdist]
    have hbi' : dist b (i : R3) < 1/40 := mem_ball.mp hbi
    have h := mul_lt_mul_of_pos_left hbi' hspos
    linarith
  have hsq := finite_cover_interpolation_sq t (fun i => ball (p + s • (i : R3)) (s/40))
    {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} (annD p s)
    (isCompact_native_closed_annulus p (3*s/4) (5*s/4)).isClosed.measurableSet
    (fun i _ => measurableSet_ball)
    (fun i _ => (ball_subset_ball (by linarith)).trans (annA_ball_subset p hspos (hKuA i i.2)))
    hcover q hint (Real.sqrt (∫ y in annS p s, q y ^ 2)) (Real.sqrt (∫ y in annD p s, q y ^ 2))
    (A.min' hAne) C a (Real.sqrt_nonneg _) hSD (hA _ hamem).1
    (fun i _ => (hC i).le) hale (fun i hi => by
      have hI : 0 ≤ ∫ y in ball (p + s • (i : R3)) (s/40), q y ^ 2 :=
        integral_nonneg (fun y => sq_nonneg (q y))
      rw [← Real.sq_sqrt hI]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (HGr i lam ⟨hlam.1, hlam.2.trans (hLle i hi)⟩ p hp s hsI q hq) 2)
  have hw : 0 ≤ Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
      Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne) :=
    mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  calc Real.sqrt (∫ y in {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4}, q y ^ 2)
      ≤ Real.sqrt ((∑ i ∈ t, (C i) ^ 2) *
          (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i ∈ t, (C i) ^ 2) *
          (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne)) := by
        rw [Real.sqrt_mul hsum, Real.sqrt_sq hw]
    _ ≤ (Real.sqrt (∑ i ∈ t, (C i) ^ 2) + 1) *
          (Real.sqrt (∫ y in annS p s, q y ^ 2) ^ (A.min' hAne) *
            Real.sqrt (∫ y in annD p s, q y ^ 2) ^ (1 - A.min' hAne)) :=
        mul_le_mul_of_nonneg_right (by linarith) hw

/-- R10: the checked radial interpolation instance (N2) with a Carleman factor `M ≥ 0`. -/
theorem radial_interp_instance_scaled (g : MatrixField) (hg : IsAdmissibleMetric g)
    {lam η Λ τ0 Kr M a b c d f t : ℝ} {ctr : R3} {Ob : Set R3}
    (hη : 0 < η) (hΛ : 0 < Λ) (hKr : 0 ≤ Kr) (hM : 0 ≤ M) (ha : 0 ≤ a) (hab : a < b)
    (hbc : b ≤ c) (hcd : c < d) (hdf : d < f) (hat : a < t) (htc : t < c) {e : ℝ}
    (hObm : MeasurableSet Ob) (hOb : ∀ y ∈ Ob, b * η ≤ ‖y - ctr‖ ∧ ‖y - ctr‖ ≤ t * η)
    {q : R3 → ℝ}
    (hq : ContDiffOn ℝ ∞ q (ball ctr (f * η)))
    (hL : ∀ y ∈ ball ctr (f * η), Lop (radialCoeff g (lam, ctr, 1 / η)) q y = 0)
    (hint : IntegrableOn (fun y => q y ^ 2) (ball ctr (f * η)))
    (HC : ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ closedAnnulus ctr (a * η) (d * η) →
      (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) * w y ^ 2) ≤
        M * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) *
          Lop (radialCoeff g (lam, ctr, 1 / η)) w y ^ 2)
    (hRI : ∫ y in closedAnnulus ctr (a * η) (b * η),
        Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 ≤
      Kr * ∫ y in ball ctr (e * η), q y ^ 2)
    (hRO : ∫ y in closedAnnulus ctr (c * η) (d * η),
        Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 ≤
      Kr * ∫ y in ball ctr (f * η), q y ^ 2) :
    Real.sqrt (∫ y in Ob, q y ^ 2) ≤
      (2 * Real.sqrt (M * Kr) + Real.exp ((nearE Λ t - nearE Λ c) * max τ0 1)) *
        (Real.sqrt (∫ y in ball ctr (e * η), q y ^ 2) ^ radGamma Λ a t c *
          Real.sqrt (∫ y in ball ctr (f * η), q y ^ 2) ^ (1 - radGamma Λ a t c)) := by
  have hc0 : 0 ≤ c := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hchi := contDiff_genCut a b c d ctr η
  have hts := tsupport_genCut ctr hη ha hab hc0 hcd
  have hts4 : tsupport (genCut a b c d ctr η) ⊆ ball ctr (f * η) :=
    hts.trans (closedAnnulus_subset_ball (by nlinarith))
  have hw : ContDiff ℝ ∞ (fun z => genCut a b c d ctr η z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball hchi hts4 hq
  have hwts : tsupport (fun z => genCut a b c d ctr η z * q z) ⊆
      closedAnnulus ctr (a * η) (d * η) := tsupport_mul_subset_left.trans hts
  have hLzero : ∀ x, x ∉ closedAnnulus ctr (a * η) (b * η) ∪
      closedAnnulus ctr (c * η) (d * η) →
      Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) x = 0 :=
    Lop_cutoff_mul_eq_zero _ hts4 hL (genCut_dich ctr hη ha hab hbc hcd)
  have hLzero' : ∀ x, x ∉ closedAnnulus ctr (a * η) (b * η) ∪
      closedAnnulus ctr (c * η) (d * η) →
      Real.sqrt M * Lop (radialCoeff g (lam, ctr, 1 / η))
        (fun z => genCut a b c d ctr η z * q z) x = 0 :=
    fun x hx => by rw [hLzero x hx, mul_zero]
  have hLzero'' : ∀ x, x ∉ closedAnnulus ctr (a * η) (b * η) ∪
      closedAnnulus ctr (c * η) (d * η) →
      (Real.sqrt M * Lop (radialCoeff g (lam, ctr, 1 / η))
        (fun z => genCut a b c d ctr η z * q z) x) ^ 2 = 0 :=
    fun x hx => by rw [hLzero' x hx]; norm_num
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, ctr, 1 / η))
    (radialCoeff_contDiff g hg _) hw
  have hψc : Continuous (fun y : R3 => Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) := by fun_prop
  have hKin := isCompact_closedAnnulus ctr (a * η) (b * η)
  have hKout := isCompact_closedAnnulus ctr (c * η) (d * η)
  have hL_int : Integrable (fun x => (Real.sqrt M * Lop (radialCoeff g (lam, ctr, 1 / η))
      (fun z => genCut a b c d ctr η z * q z) x) ^ 2) :=
    ((continuous_const.mul hLc).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hKin.union hKout) hLzero'')
  have hu_int : ∀ τ : ℝ, Integrable (fun x =>
      (Real.exp (τ * Real.exp (Λ * -(‖x - ctr‖ ^ 2 / η ^ 2))) *
        (genCut a b c d ctr η x * q x)) ^ 2) :=
    fun τ => (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul hw.continuous).pow
      2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedAnnulus ctr (a * η) (d * η)) (fun x hx => by
        have h0 : genCut a b c d ctr η x = 0 := by
          by_contra h
          exact hx (hts (subset_tsupport _ h))
        simp [h0]))
  have hObf : Ob ⊆ ball ctr (f * η) := fun y hy =>
    mem_ball_iff_norm.mpr (lt_of_le_of_lt (hOb y hy).2 (by nlinarith))
  have hRI' : (∫ y in closedAnnulus ctr (a * η) (b * η), (Real.sqrt M *
      Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y) ^ 2) ≤
      M * Kr * ∫ y in ball ctr (e * η), q y ^ 2 := by
    have e' : (∫ y in closedAnnulus ctr (a * η) (b * η), (Real.sqrt M *
        Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y) ^ 2) =
        M * ∫ y in closedAnnulus ctr (a * η) (b * η),
          Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [mul_pow, Real.sq_sqrt hM]
    rw [e', mul_assoc]
    exact mul_le_mul_of_nonneg_left hRI hM
  have hRO' : (∫ y in closedAnnulus ctr (c * η) (d * η), (Real.sqrt M *
      Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y) ^ 2) ≤
      M * Kr * ∫ y in ball ctr (f * η), q y ^ 2 := by
    have e' : (∫ y in closedAnnulus ctr (c * η) (d * η), (Real.sqrt M *
        Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y) ^ 2) =
        M * ∫ y in closedAnnulus ctr (c * η) (d * η),
          Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [mul_pow, Real.sq_sqrt hM]
    rw [e', mul_assoc]
    exact mul_le_mul_of_nonneg_left hRO hM
  have hstep : ∀ τ : ℝ, max τ0 1 ≤ τ →
      Real.sqrt (∫ y in Ob, q y ^ 2) ≤
        Real.sqrt (M * Kr) * (Real.exp (-((nearE Λ t - nearE Λ c) * τ)) *
          Real.sqrt (∫ y in ball ctr (f * η), q y ^ 2) +
          Real.exp ((nearE Λ a - nearE Λ t) * τ) *
            Real.sqrt (∫ y in ball ctr (e * η), q y ^ 2)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hτ
    have hcarl := HC τ ((le_max_left _ _).trans hτ) _ hw hwts
    have hcarl' : (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) *
        (genCut a b c d ctr η y * q y) ^ 2) ≤
        ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) *
          (Real.sqrt M * Lop (radialCoeff g (lam, ctr, 1 / η))
            (fun z => genCut a b c d ctr η z * q z) y) ^ 2 := by
      have e' : (∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) *
          (Real.sqrt M * Lop (radialCoeff g (lam, ctr, 1 / η))
            (fun z => genCut a b c d ctr η z * q z) y) ^ 2) =
          M * ∫ y, Real.exp (2 * τ * Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) *
            Lop (radialCoeff g (lam, ctr, 1 / η)) (fun z => genCut a b c d ctr η z * q z) y ^ 2 := by
        rw [← integral_const_mul]
        congr 1
        funext y
        rw [mul_pow, Real.sq_sqrt hM]
        ring
      rw [e']
      exact hcarl
    have hsplit := carleman_collar_split (τ := τ) (u := fun z => genCut a b c d ctr η z * q z)
      (L := fun x => Real.sqrt M * Lop (radialCoeff g (lam, ctr, 1 / η))
        (fun z => genCut a b c d ctr η z * q z) x)
      (ψ := fun y => Real.exp (Λ * -(‖y - ctr‖ ^ 2 / η ^ 2))) (wO := q)
      (KB := closedAnnulus ctr (a * η) (b * η)) (KH := closedAnnulus ctr (c * η) (d * η))
      (Ob := Ob) (hB := nearE Λ a) (hS := nearE Λ c) (hO := nearE Λ t)
      (by linarith) hcarl' (hu_int τ) hL_int hKin.isClosed.measurableSet
      hKout.isClosed.measurableSet hObm hLzero'
      (fun x hx => (radial_weight_bounds hΛ hη ha x ctr).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hη hc0 x ctr).1 hx.1)
      (fun x hx => (radial_weight_bounds hΛ hη ht0 x ctr).2 (hOb x hx).2)
      (fun x hx => by
        have hx2 : ‖x - ctr‖ ≤ c * η := (hOb x hx).2.trans (by nlinarith)
        show genCut a b c d ctr η x * q x = q x
        rw [genCut_eq_one ctr hη ha hab hc0 hcd (hOb x hx).1 hx2, one_mul])
      (hint.mono_set hObf)
    exact tb_balance_step (integral_nonneg fun x => sq_nonneg (q x))
      (integral_nonneg fun x => sq_nonneg (q x)) (mul_nonneg hM hKr) hsplit hRI' hRO'
  have hAD : Real.sqrt (∫ y in Ob, q y ^ 2) ≤ Real.sqrt (∫ y in ball ctr (f * η), q y ^ 2) :=
    sqrt_setIntegral_sq_mono hint hObf
  have hα' : 0 < nearE Λ t - nearE Λ c := sub_pos.mpr (nearE_lt hΛ ht0 htc)
  have hβ' : 0 < nearE Λ a - nearE Λ t := sub_pos.mpr (nearE_lt hΛ ha hat)
  have hbal := exp_balance hα' hβ' (Real.sqrt_nonneg (M * Kr)) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hAD hstep
  have hsum : nearE Λ t - nearE Λ c + (nearE Λ a - nearE Λ t) = nearE Λ a - nearE Λ c := by
    ring
  have hne : nearE Λ a - nearE Λ c ≠ 0 := (by linarith : 0 < nearE Λ a - nearE Λ c).ne'
  have hcompl : (nearE Λ a - nearE Λ t) / (nearE Λ a - nearE Λ c) = 1 - radGamma Λ a t c := by
    unfold radGamma
    rw [eq_sub_iff_add_eq, ← add_div, show nearE Λ a - nearE Λ t + (nearE Λ t - nearE Λ c) =
      nearE Λ a - nearE Λ c by ring, div_self hne]
  rw [hsum, hcompl] at hbal
  exact hbal

/-- R11: the near-one radial interpolation with ONE `Λ` chosen BEFORE `α` and BEFORE the range
`B, [η0, η1]`; for each `α` and range only `K` and the dilation ceiling `lam0` follow. -/
theorem uniform_near_one_interpolation_RF (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ B η0 η1 : ℝ, 0 < η0 → η0 ≤ η1 →
      ∃ K lam0 : ℝ, 0 < K ∧ 0 < lam0 ∧
      ∀ lam ∈ Icc (0 : ℝ) lam0, ∀ c : R3, ‖c‖ ≤ B → ∀ η ∈ Icc η0 η1, ∀ p : R3, ‖p - c‖ = η →
      ∀ q : R3 → ℝ, ContDiffOn ℝ ∞ q (ball c (3 * η)) →
      (∀ y ∈ ball c (3 * η),
        Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q y = 0) →
      IntegrableOn (fun y => q y ^ 2) (ball c (3 * η)) →
      Real.sqrt (∫ y in ball p (α / 4 * η), q y ^ 2) ≤
        K * (Real.sqrt (∫ y in ball c ((1 - α / 2) * η), q y ^ 2) ^ nearGamma Λ α *
          Real.sqrt (∫ y in ball c (3 * η), q y ^ 2) ^ (1 - nearGamma Λ α)) := by
  obtain ⟨Λ, τ0, hΛ, HC⟩ := uniform_affine_radial_carleman g hg 1 (1 / 2) (5 / 2) (by norm_num)
  refine ⟨Λ, hΛ, fun α hα hα4 B η0 η1 hη0 hηη => ?_⟩
  have hη1 : 0 < η1 := hη0.trans_le hηη
  have hden : 0 < |B| + η1 + 1 := by positivity
  have hlam0 : 0 < 1 / (|B| + η1 + 1) := by positivity
  obtain ⟨Mi, hMi, HMi⟩ := uniform_cutoff_residual_pointwise g hg (1 / (|B| + η1 + 1)) B η0 η1
    (1 - 2 * α) (1 - α) hη0 hηη (contDiff_cutProfile (1 - 2 * α) (1 - α) 2 (5 / 2))
  obtain ⟨Mo, hMo, HMo⟩ := uniform_cutoff_residual_pointwise g hg (1 / (|B| + η1 + 1)) B η0 η1
    2 (5 / 2) hη0 hηη (contDiff_cutProfile (1 - 2 * α) (1 - α) 2 (5 / 2))
  obtain ⟨Ci, hCi, HCi⟩ := uniform_caccioppoli g hg (1 / (|B| + η1 + 1)) B η0 η1 (1 - α)
    (1 - 3 * α / 4) (1 - α / 2) hη0 hηη (by linarith) (by linarith) (by linarith)
  obtain ⟨Co, hCo, HCo⟩ := uniform_caccioppoli g hg (1 / (|B| + η1 + 1)) B η0 η1 (5 / 2) (11 / 4) 3
    hη0 hηη (by norm_num) (by norm_num) (by norm_num)
  have hKr : 0 ≤ Mi * (1 + Ci) + Mo * (1 + Co) := by positivity
  refine ⟨2 * Real.sqrt (η1 ^ 4 * (Mi * (1 + Ci) + Mo * (1 + Co))) +
    Real.exp ((nearE Λ (1 + α / 4) - nearE Λ 2) * max τ0 1), 1 / (|B| + η1 + 1),
    by positivity, hlam0, ?_⟩
  intro lam hlam c hc η hη p hp q hq hL hint
  have hη' : 0 < η := hη0.trans_le hη.1
  have hlc : ‖lam • c‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hlam.1]
    have h1 : lam * ‖c‖ ≤ 1 / (|B| + η1 + 1) * (|B| + η1 + 1) :=
      mul_le_mul hlam.2 (by linarith [le_abs_self B]) (norm_nonneg c) hlam0.le
    rwa [one_div_mul_cancel hden.ne'] at h1
  have hls : |lam * η| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hlam.1 hη'.le)]
    have h1 : lam * η ≤ 1 / (|B| + η1 + 1) * (|B| + η1 + 1) :=
      mul_le_mul hlam.2 (by linarith [abs_nonneg B, hη.2]) hη'.le hlam0.le
    rwa [one_div_mul_cancel hden.ne'] at h1
  have hw : ContDiff ℝ ∞ (fun z => genCut (1 - 2 * α) (1 - α) 2 (5 / 2) c η z * q z) :=
    CutoffCommutator.contDiff_mul_of_tsupport_subset isOpen_ball (contDiff_genCut _ _ _ _ c η)
      ((tsupport_genCut c hη' (by linarith) (by linarith) (by norm_num) (by norm_num)).trans
        (closedAnnulus_subset_ball (by linarith))) hq
  have hLc := continuous_Lop_of_contDiff (radialCoeff g (lam, c, 1 / η))
    (radialCoeff_contDiff g hg _) hw
  have hsub_e : ball c ((1 - α / 2) * η) ⊆ ball c (3 * η) := ball_subset_ball (by nlinarith)
  have hKin3 : closedAnnulus c ((1 - 2 * α) * η) ((1 - α) * η) ⊆ ball c (3 * η) :=
    closedAnnulus_subset_ball (by nlinarith)
  have hKout3 : closedAnnulus c (2 * η) (5 / 2 * η) ⊆ ball c (3 * η) :=
    closedAnnulus_subset_ball (by linarith)
  have hcI := HCi lam hlam c hc η hη q (hq.mono hsub_e) (fun y hy => hL y (hsub_e hy))
    (hint.mono_set hsub_e)
  have hcO := HCo lam hlam c hc η hη q hq hL hint
  have hRI0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / η))
      (fun z => genCut (1 - 2 * α) (1 - α) 2 (5 / 2) c η z * q z)) (Dom := ball c (3 * η))
    (isCompact_closedAnnulus c ((1 - 2 * α) * η) ((1 - α) * η))
    (closedAnnulus_subset_ball (by nlinarith)) (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c ((1 - α) * η)) (closedBall_subset_ball (by nlinarith)) isOpen_ball
    hMi hLc hq (hint.mono_set hsub_e)
    (fun y hy => HMi lam hlam c hc η hη y hy.1 hy.2 (ball c (3 * η)) isOpen_ball q hq
      (hKin3 hy) (hL y (hKin3 hy))) hcI
  have hRO0 := collar_residual_integral (L := Lop (radialCoeff g (lam, c, 1 / η))
      (fun z => genCut (1 - 2 * α) (1 - α) 2 (5 / 2) c η z * q z)) (Dom := ball c (3 * η))
    (isCompact_closedAnnulus c (2 * η) (5 / 2 * η)) hKout3
    (fun y hy => mem_closedBall_iff_norm.mpr hy.2)
    (isCompact_closedBall c (5 / 2 * η)) (closedBall_subset_ball (by linarith)) isOpen_ball
    hMo hLc hq hint
    (fun y hy => HMo lam hlam c hc η hη y hy.1 hy.2 (ball c (3 * η)) isOpen_ball q hq
      (hKout3 hy) (hL y (hKout3 hy))) hcO
  have hS0 : 0 ≤ ∫ y in ball c ((1 - α / 2) * η), q y ^ 2 :=
    integral_nonneg fun x => sq_nonneg (q x)
  have hD0 : 0 ≤ ∫ y in ball c (3 * η), q y ^ 2 := integral_nonneg fun x => sq_nonneg (q x)
  have hi : 0 ≤ Mi * (1 + Ci) := by positivity
  have ho : 0 ≤ Mo * (1 + Co) := by positivity
  have hOb : ∀ y ∈ ball p (α / 4 * η), (1 - α) * η ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ (1 + α / 4) * η := by
    intro y hy
    have hyp : ‖y - p‖ < α / 4 * η := mem_ball_iff_norm.mp hy
    have h1 : ‖y - c‖ ≤ ‖y - p‖ + ‖p - c‖ := by
      have he : y - c = (y - p) + (p - c) := by abel
      rw [he]; exact norm_add_le _ _
    have h2 : ‖p - c‖ ≤ ‖y - c‖ + ‖y - p‖ := by
      have he : (y - c) - (y - p) = p - c := by abel
      have h := norm_sub_le (y - c) (y - p)
      rw [he] at h
      exact h
    have hαη : 0 < α * η := mul_pos hα hη'
    constructor <;> nlinarith
  have hsupp' : closedAnnulus c ((1 - 2 * α) * η) (5 / 2 * η) ⊆
      {y | 1 / 2 * η ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ 5 / 2 * η} := by
    intro y hy
    have h12 : 1 / 2 * η ≤ (1 - 2 * α) * η := by nlinarith
    exact ⟨h12.trans hy.1, hy.2⟩
  exact radial_interp_instance_scaled g hg (a := 1 - 2 * α) (b := 1 - α) (c := 2) (d := 5 / 2)
    (e := 1 - α / 2) (f := 3) (t := 1 + α / 4) (Ob := ball p (α / 4 * η))
    hη' hΛ hKr (pow_nonneg hη1.le 4) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by norm_num) (by linarith) (by linarith) measurableSet_ball hOb
    hq hL hint
    (fun τ hτ w hw' hsupp => (HC lam c η hη' hlc hls τ hτ w hw' (hsupp.trans hsupp')).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hη'.le hη.2 4)
        (integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))))
    (hRI0.trans (mul_le_mul_of_nonneg_right (by linarith) hS0))
    (hRO0.trans (mul_le_mul_of_nonneg_right (by linarith) hD0))

section NativeRangeFree
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

/-- R12 (W4-RF): the native second-coefficient interpolation on the literal annulus with ONE
exponent `γ2` chosen BEFORE the range `B, [s0, s1]`; `K2i` and `lam1` follow the range. -/
theorem uniform_secondCoefficientInterpolation_annulus_RF (S : KnownSideSourceData) :
    ∃ γ2 : ℝ, 0 < γ2 ∧ γ2 < 1 ∧ ∀ B s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 →
      ∃ K2i lam1 : ℝ, 0 < K2i ∧ 0 < lam1 ∧ ∀ L : ℝ, ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3,
      ‖p‖ ≤ B → ∀ s ∈ Icc s0 s1,
      SecondCoefficientInterpolationOn S L lam {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s}
        {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
        (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8)) K2i γ2 := by
  obtain ⟨a, ha, ha1, H0⟩ := uniform_annulus_interpolation_RF S.g2 S.g2_admissible
  refine ⟨a, ha, ha1, fun B s0 s1 hs0 hss => ?_⟩
  obtain ⟨C, lam1, hC, hlam1, H⟩ := H0 B s0 s1 hs0 hss
  refine ⟨C, lam1, hC, hlam1, ?_⟩
  intro L lam hlam p hp s hs b hb hpde bD bO bS hbD hbO hbS M μ hμ hM hSM hDM
  have hspos : 0 < s := hs0.trans_le hs.1
  have hint : IntegrableOn (fun y => b y ^ 2) (annD p s) :=
    (integral_sq_representative_eq_norm_sq bD b hbD).1.integrable_sq
  have hcls : AnnClass S.g2 lam p s b :=
    ⟨hb, fun x hx => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2
      S.g1_admissible S.g2_admissible L lam b x).mp (hpde x hx), hint⟩
  have hmain := H lam hlam p hp s hs b hcls
  obtain ⟨-, -, -, -, -, hOK, hKD, -⟩ := native_annulus_target_geometry p s hspos
  have hOKi := sqrt_setIntegral_sq_mono (hint.mono_set hKD) hOK
  have hS' : ‖bS‖ = Real.sqrt (∫ y in annS p s, b y ^ 2) :=
    lp_norm_eq_sqrt_integral_sq bS b hbS
  have hD' : ‖bD‖ = Real.sqrt (∫ y in annD p s, b y ^ 2) :=
    lp_norm_eq_sqrt_integral_sq bD b hbD
  rw [← hS', ← hD'] at hmain
  rw [lp_norm_eq_sqrt_integral_sq bO b hbO]
  exact interp_coeff_bound hμ hM hC.le (norm_nonneg _) hSM (norm_nonneg _) hDM ha.le ha1.le
    (hOKi.trans hmain)

/-- R12 (N5-RF): the native near-one FIRST basis arm with `Λ` before `α` and both BEFORE the
range `B, [η0, η1]`; `K` and `lam0` follow the range. -/
theorem uniform_near_one_first_arm_RF (S : KnownSideSourceData) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ B η0 η1 : ℝ, 0 < η0 → η0 ≤ η1 →
      ∃ K lam0 : ℝ, 0 < K ∧ 0 < lam0 ∧
      ∀ lam ∈ Icc (0 : ℝ) lam0, ∀ c : R3, ‖c‖ ≤ B → ∀ η ∈ Icc η0 η1, ∀ p : R3, ‖p - c‖ = η →
      FirstBasisArmOn S lam (ball c (3 * η)) (ball p (α / 4 * η)) (ball c ((1 - α / 2) * η))
        K (nearGamma Λ α) := by
  obtain ⟨Λ, hΛ, H⟩ := uniform_near_one_interpolation_RF S.g1 S.g1_admissible
  refine ⟨Λ, hΛ, fun α hα hα4 B η0 η1 hη0 hηη => ?_⟩
  obtain ⟨K, lam0, hK, hlam0, HK⟩ := H α hα hα4 B η0 η1 hη0 hηη
  refine ⟨K, lam0, hK, hlam0, fun lam hlam c hc η hη p hp => ?_⟩
  apply first_basis_arm_on_of_room
  intro u q hq hqs hpde uO uS hqO hqS
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hL : ∀ y ∈ ball c (3 * η),
      Lop (fun i k y => EnergyBridge.principalCoefficient S.g1 (lam • y) i k) q y = 0 := by
    intro y hy
    have h := hpde y hy
    rw [coordinateFluxDivergence_eq_divCoeffGrad] at h
    exact h
  have hI := HK lam hlam c hc η hη p hp q hqs hL hmem.integrable_sq
  rw [hnO, hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hI
  exact hI

/-- R13: the RANGE-INDEPENDENT coarse opening for both native arms. ONE opening fraction
`α ∈ (0, 1/4]`, ONE `Λ` and ONE `γ2 ∈ (0,1)` with strict exponent sum
`nearGamma Λ α + γ2 > 1` are fixed FIRST; then for EVERY bounded range both arms hold with
range-dependent constants and dilation ceilings only. -/
theorem range_free_coarse_opening (S : KnownSideSourceData) :
    ∃ α Λ γ2 : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < Λ ∧ 0 < γ2 ∧ γ2 < 1 ∧ 1 < nearGamma Λ α + γ2 ∧
      (∀ B η0 η1 : ℝ, 0 < η0 → η0 ≤ η1 →
        ∃ K lam0 : ℝ, 0 < K ∧ 0 < lam0 ∧
        ∀ lam ∈ Icc (0 : ℝ) lam0, ∀ c : R3, ‖c‖ ≤ B → ∀ η ∈ Icc η0 η1, ∀ p : R3,
        ‖p - c‖ = η →
        FirstBasisArmOn S lam (ball c (3 * η)) (ball p (α / 4 * η)) (ball c ((1 - α / 2) * η))
          K (nearGamma Λ α)) ∧
      (∀ B s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 →
        ∃ K2i lam1 : ℝ, 0 < K2i ∧ 0 < lam1 ∧ ∀ L : ℝ, ∀ lam ∈ Icc (0 : ℝ) lam1, ∀ p : R3,
        ‖p‖ ≤ B → ∀ s ∈ Icc s0 s1,
        SecondCoefficientInterpolationOn S L lam {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s}
          {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
          (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8)) K2i γ2) := by
  obtain ⟨γ2, hγ2, hγ21, H2⟩ := uniform_secondCoefficientInterpolation_annulus_RF S
  obtain ⟨Λ, hΛ, H1⟩ := uniform_near_one_first_arm_RF S
  obtain ⟨α, hα, hα4, hnear⟩ := nearGamma_near_one hΛ hγ2
  exact ⟨α, Λ, γ2, hα, hα4, hΛ, hγ2, hγ21, by linarith, H1 α hα hα4, H2⟩

open scoped Matrix.Norms.Elementwise

/-- R14: the coarse cross series with the opening fraction `α` and the exponents (strict sum)
chosen BEFORE the range `B, [s0, s1]`; only `K1i, K2i` and `lam0` follow the range. Same
placement in the ORIGINAL `initialCross` as the checked N6. -/
theorem uniform_coarse_cross_series_RF (S : KnownSideSourceData) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ ∃ γ1 γ2 : ℝ, 0 < γ1 + γ2 - 1 ∧
    ∀ B s0 s1 : ℝ, 0 < B → 0 < s0 → s0 ≤ s1 →
    ∃ K1i K2i : ℝ, 0 < K1i ∧
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ (F : R3 × R3 → ℝ) (L lam : ℝ) (Ω : Set (R3 × R3)), IsOpen Ω →
      ProductSolutionOn S L lam F Ω → initialCross S lam ⊆ Ω → 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lam • p) = 0 → ∀ s ∈ Icc s0 s1,
      ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
        (hTD1 : T ⊆ D1) (ι : Type)
        (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        O1 = ball p (α / 4 * (s / 20)) ∧
        CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1
          {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
          (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
          K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨α, Λ, γ2, hα, hα4, hΛ, hγ2, hγ21, hsum1, H1, H2⟩ := range_free_coarse_opening S
  refine ⟨α, hα, hα4, nearGamma Λ α, γ2, by linarith, fun B s0 s1 hB hs0 hss => ?_⟩
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨K2i, lamB, -, hlamB, HB⟩ := H2 B s0 s1 hs0 hss
  obtain ⟨K1i, lamA, hK1i, hlamA, HA'⟩ := H1 (B + s1 / 20) (s0 / 20) (s1 / 20)
    (by positivity) (by linarith)
  have he : 0 < α * s0 / 80 := by positivity
  obtain ⟨l1, hl1, Hsep⟩ :=
    exists_uniform_scaled_separating_error S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  obtain ⟨l2, hl2, Hcross⟩ :=
    exists_uniform_original_lower_cross S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  refine ⟨K1i, K2i, hK1i, min (min l1 l2) (min lamA lamB),
    lt_min (lt_min hl1 hl2) (lt_min hlamA hlamB), ?_⟩
  intro F L lam Ω hΩ hSol hΩc hlam hlam0 p hp hp0 s hs
  have hspos : 0 < s := hs0.trans_le hs.1
  have hl1' : lam ≤ l1 := hlam0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hl2' : lam ≤ l2 := hlam0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlA : lam ∈ Icc (0 : ℝ) lamA :=
    ⟨hlam.le, hlam0.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hlB : lam ∈ Icc (0 : ℝ) lamB :=
    ⟨hlam.le, hlam0.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hpB : ‖p‖ ≤ B + 2 * s1 + 1 := by linarith
  have hp2 : |p 2| ≤ α * s0 / 80 / 2 := by
    have h := (Hsep lam hlam hl1' p hpB).2.1
    rw [hp0, zero_sub, abs_neg, abs_mul, abs_of_pos hlam, mul_div_assoc] at h
    exact le_of_mul_le_mul_left h hlam
  have hp2' := (abs_le.mp hp2).2
  set η : ℝ := s / 20 with hη_def
  have hη : 0 < η := by positivity
  set c : R3 := p - η • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) with hc_def
  have he2n : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  have hpc : ‖p - c‖ = η := by
    rw [hc_def, sub_sub_cancel, norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hη, mul_one]
  have hcB : ‖c‖ ≤ B + s1 / 20 := by
    have h := norm_sub_le p (η • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hη, mul_one] at h
    rw [hc_def]
    linarith [hs.2]
  have hηI : η ∈ Icc (s0 / 20) (s1 / 20) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have HA1 := HA' lam hlA c hcB η hηI p hpc
  have HB1 := HB L lam hlB p hp s hs
  have hc2 : c 2 = p 2 - η := by simp [hc_def, PiLp.sub_apply, PiLp.smul_apply]
  have hαη : α * η = α * s / 20 := by rw [hη_def]; ring
  have hαη0 : 0 ≤ α * η := by positivity
  have hαs : α * s0 ≤ α * s := mul_le_mul_of_nonneg_left hs.1 hα.le
  have hαs0 : α * s0 ≤ 1 / 4 * s0 := mul_le_mul_of_nonneg_right hα4 hs0.le
  have hrow : closedBall c ((1 - α / 2) * η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hΩc
    have hxc : ‖x - c‖ ≤ (1 - α / 2) * η := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hxp : ‖x - p‖ ≤ ‖x - c‖ + ‖p - c‖ := by
      have hh := norm_sub_le (x - c) (p - c)
      rwa [sub_sub_sub_cancel_right] at hh
    obtain ⟨hy1, hy2⟩ := hy
    have hcoord : (x - c) 2 ≤ ‖x - c‖ := (abs_le.mp (abs_coord_le_norm (x - c) 2)).2
    have hsum : x 2 = (x - c) 2 + c 2 := by simp only [PiLp.sub_apply]; ring
    have hx2 : x 2 ≤ -(α * s0 / 80) := by linarith
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    have hne : x ≠ y := by
      intro hxy
      rw [← hxy] at hy1
      linarith
    exact Hcross lam hlam hl2' (x, y) hxn hyn hne (Or.inl hx2)
  have hobs : closedBall c (3 * η) ×ˢ
      closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8) ⊆ Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hΩc
    have hxc : ‖x - c‖ ≤ 3 * η := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hxp : ‖x - p‖ ≤ ‖x - c‖ + ‖p - c‖ := by
      have hh := norm_sub_le (x - c) (p - c)
      rwa [sub_sub_sub_cancel_right] at hh
    have hyc : ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ≤ s / 8 := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    have hse : ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = s := by
      rw [norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hspos, mul_one]
    have hyp1 : ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤
        ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ + ‖y - p‖ := by
      have hh := norm_sub_le (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) (y - p)
      have he' : y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - (y - p) =
          s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by abel
      rwa [he'] at hh
    have hyp2 : ‖y - p‖ ≤ ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ +
        ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ := by
      have hh := norm_sub_le (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
        (s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      have he' : y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) -
          s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) = y - p := by abel
      rwa [he'] at hh
    have hcoord : (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) 2 ≤
        ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ :=
      (abs_le.mp (abs_coord_le_norm _ 2)).2
    have hj2 : (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = p 2 - s := by
      simp [PiLp.sub_apply, PiLp.smul_apply]
    have hsum : y 2 = (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) 2 +
        (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 := by
      simp only [PiLp.sub_apply]; ring
    have hy2 : y 2 ≤ -(α * s0 / 80) := by linarith [hs.1]
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    have hne : x ≠ y := by
      intro hxy
      rw [← hxy] at hyp1 hyc
      linarith
    exact Hcross lam hlam hl2' (x, y) hxn hyn hne (Or.inr hy2)
  obtain ⟨hDo, -, -, -, -, hOK, hKD, -⟩ := native_annulus_target_geometry p s hspos
  have hαη4 := mul_le_mul_of_nonneg_right hα4 hη.le
  have hO1D1 : ball p (α / 4 * η) ⊆ ball c (3 * η) :=
    ball_subset_ball' (by rw [dist_eq_norm, hpc]; linarith)
  have hKTD1 : closedBall c ((1 - α / 2) * η) ⊆ ball c (3 * η) :=
    closedBall_subset_ball (by linarith)
  have hTD1 : ball c ((1 - α / 2) * η) ⊆ ball c (3 * η) := ball_subset_closedBall.trans hKTD1
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms_sum F S L lam Ω hΩ hSol
    (ball c (3 * η)) (ball p (α / 4 * η)) (ball c ((1 - α / 2) * η)) (closedBall c (3 * η))
    (closedBall c ((1 - α / 2) * η))
    {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8))
    {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s}
    (closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8))
    isOpen_ball (isConnected_ball (by positivity)) hO1D1 isOpen_ball
    (nonempty_ball.mpr (mul_pos (by linarith) hη)) (isCompact_closedBall _ _)
    ball_subset_closedBall hKTD1
    hTD1 (isCompact_closedBall _ _) ball_subset_closedBall hDo (hOK.trans hKD) isOpen_ball
    (isCompact_native_closed_annulus p (s/2) (2*s)) (fun y hy => ⟨hy.1.le, hy.2.le⟩)
    (isCompact_closedBall _ _) ball_subset_closedBall hrow hobs hK1i (by linarith) HA1 HB1
  exact ⟨_, isOpen_ball, _, hO1D1, _, hTD1, ι, w, μ, rfl, hser⟩

end NativeRangeFree

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

