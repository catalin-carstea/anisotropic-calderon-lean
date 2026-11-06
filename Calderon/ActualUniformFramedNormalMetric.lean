import Calderon.ActualFramedNormalGeodesicMetric
import Calderon.ActualNormalizedGeodesicEllipticity
import Calderon.CompactRadialRemainder

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
open NormalCoordinatesFrame

theorem exists_actual_uniform_framed_normal_metric
    (Q M : R3 → R3 →L[ℝ] R3) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V)
    (hpos : ∀ y v, v ≠ 0 → 0 < inner ℝ (M y v) v)
    (y0 : R3) (K : Set R3) (hK : IsCompact K) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (ε B : ℝ),
      0 < ε ∧ 0 ≤ B ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧ ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ContDiff ℝ ∞ (fun y => frameOperator (metricGramFrame (M y))) ∧
      (∀ y, Function.Bijective (frameOperator (metricGramFrame (M y)))) ∧
      ContDiff ℝ ∞ (framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
        (fun y => frameOperator (metricGramFrame (M y)))) ∧
      ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ K,
        (∀ t ∈ Icc (0 : ℝ) 1,
          HasDerivAt (Φ (y,r • frameOperator (metricGramFrame (M y)) z))
            (geodesicPhaseField Q M (Φ (y,r • frameOperator (metricGramFrame (M y)) z) t)) t) ∧
        framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,0),z) =
            ContinuousLinearMap.id ℝ R3 ∧
        HasDerivAt (fun r : ℝ => framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z)) 0 0 ∧
        ‖framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z) -
            ContinuousLinearMap.id ℝ R3‖ ≤ B*r^2 := by
  obtain ⟨Φ,A,hA,hy0,hΦ,h0,hstat,hODE,hΘ,hD,hH,hraw,hF,hbij,hG,hjet⟩ :=
    exists_actual_framed_normal_geodesic_metric Q M hQ hM hsym hMQ hpos y0
  let F := fun y => frameOperator (metricGramFrame (M y))
  let T : R3 × R3 → R3 × R3 := fun p => (p.1,F p.1 p.2)
  have hT : Continuous T := continuous_fst.prodMk
    ((hF.continuous.comp continuous_fst).clm_apply continuous_snd)
  have hB : IsOpen (T ⁻¹' A) := hA.preimage hT
  have hbase : (y0,(0 : R3)) ∈ T ⁻¹' A := by
    simpa only [mem_preimage,T,map_zero] using hy0
  obtain ⟨ε,hε,hdom⟩ := exists_commonRadius_phase_domain (T ⁻¹' A) hB y0 hbase
    (K ∪ {0}) (hK.union isCompact_singleton)
  have hc (y : R3) (hy : ‖y-y0‖ ≤ ε) : (y,0) ∈ A := by
    have h := hdom y hy 0 (by simpa using hε.le) 0 (Or.inr (mem_singleton (0 : R3)))
    simpa only [mem_preimage,T,zero_smul,map_zero] using h
  let G : (R3 × R3) × ℝ → R3 →L[ℝ] R3 := fun p =>
    framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M F ((p.1.1,p.2),p.1.2)
  have hGs : ContDiff ℝ ∞ G := hG.comp
    (((contDiff_fst.fst).prodMk contDiff_snd).prodMk contDiff_fst.snd)
  let q : Set (R3 × R3) := closedBall y0 ε ×ˢ K
  have hq : IsCompact q := (isCompact_closedBall _ _).prod hK
  have hz (p : R3 × R3) (hp : p ∈ q) : HasDerivAt (fun r : ℝ => G (p,r)) 0 0 := by
    have hy : ‖p.1-y0‖ ≤ ε := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
    exact (hjet p.1 (hc p.1 hy) p.2).2
  obtain ⟨B,hB,hquad⟩ := exists_compact_uniform_radial_quadratic_bound G hGs q hq ε hε.le hz
  refine ⟨Φ,ε,B,hε,hB,hΦ,h0,hΘ,hF,hbij,hG,?_⟩
  intro y hy r hr z hzK
  have hyA := hc y hy
  have hphase : (y,r • F y z) ∈ A := by
    have h := hdom y hy r hr z (Or.inl hzK)
    simpa only [mem_preimage,T,map_smul] using h
  have hp : (y,z) ∈ q := ⟨by simpa only [mem_closedBall,dist_eq_norm] using hy,hzK⟩
  refine ⟨hODE _ hphase,(hjet y hyA z).1,(hjet y hyA z).2,?_⟩
  simpa only [G,F,(hjet y hyA z).1] using hquad (y,z) hp r hr
end OAI.AnisotropicCalderon.ConnectionError
